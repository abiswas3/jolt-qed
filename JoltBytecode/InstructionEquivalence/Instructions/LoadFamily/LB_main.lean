import JoltBytecode.InstructionEquivalence.ProofSupport.BundleLemmas
import JoltBytecode.JoltISA.ExpansionsAutomated
import JoltBytecode.JoltISA.Expansions.Load
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Read
import JoltBytecode.InstructionEquivalence.Instructions.LoadFamily.DwordArithmetic
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Windows
import JoltBytecode.InstructionEquivalence.Instructions.LoadFamily.ProgramBlocks
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import Mathlib.Tactic.IntervalCases

set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace LB_main


/-- **Bridge lemma for LB.** The Jolt logic-phase computation (XOR with 7,
    SLL by 3, SLL the dword, arith-shift-right by 56) equals the Sail-side
    direct byte load sign-extended to 64 bits. Pure bit-vector algebra —
    just combines `sll_srai_extracts_byte` with `loaded_byte_in_dword`. -/
theorem jolt_lb_bridge (s : SailState) (addr : BitVec 64)
    (hbytes_base : MemBytesPresentAt s (addr &&& (-8 : BitVec 64)) 8)
    (h_no_ovf_base : (addr &&& (-8 : BitVec 64)).toNat + 7 < 2 ^ 64)
    (hpresent : MemBytePresentAt s addr.toNat) :
    (let dword     := loaded_dword_at s (addr &&& (-8 : BitVec 64))
        hbytes_base h_no_ovf_base
     let xor_addr  := addr ^^^ (7 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6   := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted   := shift_bits_left dword shift_6
     shift_bits_right_arith shifted (56 : BitVec 6))
    = sign_extend (m := 64) (loaded_byte_at s addr hpresent) := by
  simp only [sll_srai_extracts_byte,
    ← loaded_byte_in_dword s addr hbytes_base h_no_ovf_base hpresent]

/-- Bridge for the generated fused byte extraction. -/
theorem jolt_lb_pext_bridge (s : SailState) (base : BitVec 64) (imm : BitVec 12)
    (hbytes : MemBytesPresentAt s (compute_aligned_dword_base_address base imm) 8)
    (h_no_ovf : (compute_aligned_dword_base_address base imm).toNat + 7 < 2 ^ 64)
    (hpresent : MemBytePresentAt s (load_effective_address base imm).toNat) :
    jolt_virtual_pext_signed_value
        (loaded_dword_at s (compute_aligned_dword_base_address base imm)
          hbytes h_no_ovf)
        (jolt_virtual_window_mask_b_value base imm) =
      sign_extend (m := 64)
        (loaded_byte_at s (load_effective_address base imm) hpresent) := by
  rw [window_mask_b_pext_signed]
  have hloaded := loaded_byte_in_dword s (load_effective_address base imm)
    (by simpa only [compute_aligned_dword_base_address] using hbytes)
    (by simpa only [compute_aligned_dword_base_address] using h_no_ovf)
    hpresent
  rw [hloaded]

-- ============================================================================
-- Top-level LB ↔ Sail equivalence theorems
-- ============================================================================

/-- Sail-side `execute_LOAD imm rs1 rd false 1` reduces to
    `stateAfterWrite rd (sign_extend (loaded_byte_at ea))` under the
    flat memory facts for size 1. No `h_no_ovf` needed —
    single-byte reads cannot overflow the 64-bit address space. -/
theorem execute_LB_reduces (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (hbytes : MemBytesPresentAt js.sail (load_effective_address val imm) 1)
    (hload_pmp : Assumptions.LoadPmpOk (load_effective_address val imm) 1 js.sail)
    (hread_mmio : Assumptions.NotReadableMmio (load_effective_address val imm) 1 js.sail) :
    (execute_LOAD imm rs1 rd false 1).run js.sail =
    .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (loaded_byte_at js.sail (load_effective_address val imm)
            hbytes.single_byte))) := by
  unfold execute_LOAD
  simp only [bind, pure]
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  simp (config := { decide := true }) only []
  simp (config := { decide := true }) only [PreSail.assert, EStateM.bind, pure, EStateM.pure,
       EStateM.run, if_true]
  rw [vmem_read_byte_reduces imm rs1 js.sail hpriv hmprv val hrx
      (aligned_access_1 (load_effective_address val imm))
      (loaded_byte_at js.sail (load_effective_address val imm)
        hbytes.single_byte)
      (mem_read_1_eq_loaded_byte _ js.sail hpriv hmprv hbytes hload_pmp
        hread_mmio)]
  simp only [extend_value, Bool.false_eq_true, if_false, EStateM.bind, EStateM.pure]
  obtain ⟨s', hw⟩ := wX_shape rd
    (sign_extend (m := 64)
      (loaded_byte_at js.sail (load_effective_address val imm)
        hbytes.single_byte))
    js.sail
  rw [hw]
  simp only [RETIRE_SUCCESS]
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

/-- Execution of the Rust-generated fused `LB` expansion. -/
theorem lbProgramAuto_concrete (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (hbytes_base :
      MemBytesPresentAt js.sail (compute_aligned_dword_base_address val imm) 8)
    (hload_pmp_base :
      Assumptions.LoadPmpOk (compute_aligned_dword_base_address val imm) 8 js.sail)
    (hread_mmio_base :
      Assumptions.NotReadableMmio (compute_aligned_dword_base_address val imm) 8 js.sail)
    (hbytes_byte : MemBytesPresentAt js.sail (load_effective_address val imm) 1) :
    ∃ js' : SailJoltState,
      (JoltISA.execProgram (JoltISA.lbProgramAuto rd rs1 imm)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (loaded_byte_at js.sail (load_effective_address val imm)
            (by simpa only using hbytes_byte 0 (by omega)))) := by
  let v40 : JoltISA.VReg := BitVec.ofNat 7 40
  let v41 : JoltISA.VReg := BitVec.ofNat 7 41
  let v42 : JoltISA.VReg := BitVec.ofNat 7 42
  have hv40 : WritableVReg v40 := by
    simp only [v40, WritableVReg, BitVec.toNat_ofNat]
    norm_num
  have hv41 : WritableVReg v41 := by
    simp only [v41, WritableVReg, BitVec.toNat_ofNat]
    norm_num
  have hv42 : WritableVReg v42 := by
    simp only [v42, WritableVReg, BitVec.toNat_ofNat]
    norm_num
  have h40_ne_41 : v40 ≠ v41 := by decide
  have h41_ne_42 : v41 ≠ v42 := by decide
  let maskValue := jolt_virtual_window_mask_b_value val imm
  by_cases hx0 : JoltISA.isX0 rd = true
  · let tail : JoltISA.Program :=
      .instr (.VirtualWindowMaskB (.vreg v41) (.xreg rs1) imm) <|
      .instr (.VirtualPextSigned (.vreg v40) (.vreg v42) (.vreg v41)) <|
      .done RETIRE_SUCCESS
    rcases LoadProgramBlocks.alignAddrLdBlock tail v42 imm rs1 js hpriv hmprv
        val hrx hbytes_base hload_pmp_base hread_mmio_base hv42 with
      ⟨js_load, hload_run, hload_sail, _hload_value⟩
    let js_mask : SailJoltState :=
      { sail := js_load.sail
        vregs := fun r => if r = v41 then maskValue else js_load.vregs r }
    have hrx_load : rX_bits rs1 js_load.sail = .ok val js_load.sail := by
      simpa only [hload_sail] using hrx
    have hmask :
        (JoltISA.execInstr
          (.VirtualWindowMaskB (.vreg v41) (.xreg rs1) imm)).run js_load =
          .ok RETIRE_SUCCESS js_mask := by
      simpa only [js_mask, maskValue] using
        JoltISA.virtual_window_mask_b_run_vreg_xreg
          v41 rs1 imm js_load val hrx_load hv41
    let js' : SailJoltState :=
      { sail := js_mask.sail
        vregs := fun r =>
          if r = v40 then
            jolt_virtual_pext_signed_value (js_mask.vregs v42) (js_mask.vregs v41)
          else js_mask.vregs r }
    have hpext :
        (JoltISA.execInstr
          (.VirtualPextSigned (.vreg v40) (.vreg v42) (.vreg v41))).run js_mask =
          .ok RETIRE_SUCCESS js' := by
      simpa only [js'] using
        JoltISA.virtual_pext_signed_run_vreg_vreg_vreg v40 v42 v41 js_mask hv40
    refine ⟨js', ?_, ?_⟩
    · unfold JoltISA.lbProgramAuto
      rw [hx0]
      simp only [if_true]
      change (JoltISA.execProgram
        (.instr (.VirtualAlignAddr (.vreg v42) (.xreg rs1) imm) <|
         .instr (.LD .normal (.vreg v42) (.vreg v42) 0) tail)).run js = _
      rw [hload_run]
      rw [JoltISA.execProgram_instr_run_retire _ _ js_load js_mask hmask]
      rw [JoltISA.execProgram_instr_run_retire _ _ js_mask js' hpext]
      rfl
    · rw [JoltISA.stateAfterWrite_of_isX0_eq_true hx0]
      simp only [js', js_mask, hload_sail]
  · have hx0_false : JoltISA.isX0 rd = false := by
      exact Bool.eq_false_of_not_eq_true hx0
    let tail : JoltISA.Program :=
      .instr (.VirtualWindowMaskB (.vreg v40) (.xreg rs1) imm) <|
      .instr (.VirtualPextSigned (.xreg rd) (.vreg v41) (.vreg v40)) <|
      .done RETIRE_SUCCESS
    rcases LoadProgramBlocks.alignAddrLdBlock tail v41 imm rs1 js hpriv hmprv
        val hrx hbytes_base hload_pmp_base hread_mmio_base hv41 with
      ⟨js_load, hload_run, hload_sail, hload_value⟩
    let dword := loaded_dword_at js.sail
      (compute_aligned_dword_base_address val imm) hbytes_base
      (aligned_dword_addr_is_aligned_dword_access val imm).no_ovf
    let js_mask : SailJoltState :=
      { sail := js_load.sail
        vregs := fun r => if r = v40 then maskValue else js_load.vregs r }
    have hrx_load : rX_bits rs1 js_load.sail = .ok val js_load.sail := by
      simpa only [hload_sail] using hrx
    have hmask :
        (JoltISA.execInstr
          (.VirtualWindowMaskB (.vreg v40) (.xreg rs1) imm)).run js_load =
          .ok RETIRE_SUCCESS js_mask := by
      simpa only [js_mask, maskValue] using
        JoltISA.virtual_window_mask_b_run_vreg_xreg
          v40 rs1 imm js_load val hrx_load hv40
    have hmask_value : js_mask.vregs v40 = maskValue := by
      simp only [js_mask, if_true]
    have hmask_dword : js_mask.vregs v41 = dword := by
      simp only [js_mask, if_neg h40_ne_41.symm, dword]
      exact hload_value
    let finalValue := sign_extend (m := 64)
      (loaded_byte_at js.sail (load_effective_address val imm)
        (by simpa only using hbytes_byte 0 (by omega)))
    have hpext_value :
        jolt_virtual_pext_signed_value (js_mask.vregs v41) (js_mask.vregs v40) =
          finalValue := by
      rw [hmask_dword, hmask_value]
      exact jolt_lb_pext_bridge js.sail val imm hbytes_base
        (aligned_dword_addr_is_aligned_dword_access val imm).no_ovf
        (by simpa only using hbytes_byte 0 (by omega))
    obtain ⟨s', hwrite⟩ := wX_shape rd finalValue js.sail
    have hwrite_mask :
        wX_bits rd
          (jolt_virtual_pext_signed_value (js_mask.vregs v41) (js_mask.vregs v40))
          js_mask.sail = .ok () s' := by
      rw [hload_sail, hpext_value]
      exact hwrite
    let js' : SailJoltState := { sail := s', vregs := js_mask.vregs }
    have hpext :
        (JoltISA.execInstr
          (.VirtualPextSigned (.xreg rd) (.vreg v41) (.vreg v40))).run js_mask =
          .ok RETIRE_SUCCESS js' := by
      simpa only [js'] using
        JoltISA.virtual_pext_signed_run_xreg_vreg_vreg
          rd v41 v40 js_mask s' hwrite_mask
    refine ⟨js', ?_, ?_⟩
    · unfold JoltISA.lbProgramAuto
      rw [hx0_false]
      simp only [Bool.false_eq_true, if_false]
      change (JoltISA.execProgram
        (.instr (.VirtualAlignAddr (.vreg v41) (.xreg rs1) imm) <|
         .instr (.LD .normal (.vreg v41) (.vreg v41) 0) tail)).run js = _
      rw [hload_run]
      rw [JoltISA.execProgram_instr_run_retire _ _ js_load js_mask hmask]
      rw [JoltISA.execProgram_instr_run_retire _ _ js_mask js' hpext]
      rfl
    · exact wX_bits_eq_stateAfterWrite rd finalValue js.sail s' hwrite

/-- The generated `LB` expansion writes only instruction-local scratch vregs. -/
theorem lbProgramAuto_preserves_projected_vregs
    (imm : BitVec 12) (rs1 rd : regidx)
    {js js' : SailJoltState} {result : ExecutionResult}
    (hrun : (JoltISA.execProgram (JoltISA.lbProgramAuto rd rs1 imm)).run js =
      .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe : JoltISA.ProgramWritesNoProtectedVReg
      (JoltISA.lbProgramAuto rd rs1 imm) := by
    unfold JoltISA.lbProgramAuto
    split <;>
      simp only [JoltISA.ProgramWritesNoProtectedVReg,
        JoltISA.InstrWritesNoProtectedVReg, JoltISA.DstWritesNoProtectedVReg,
        JoltISA.sideEffectingDst, and_true] <;>
      norm_num [JoltISA.IsProtectedJoltRegister, JoltISA.joltRegisterSlot,
        JoltISA.JoltRegisterSlot.isProtected]
  exact Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    hsafe hrun

/-- **Main program theorem for LB.**  The structured Jolt-ISA expansion
matches Sail after materializing Jolt's persistent CSR virtual registers. -/
def lbProgramEqSailStatement (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (_h : LoadProgramEqSailAssumptions imm rs1 js) : Prop :=
    System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.lbProgramAuto rd rs1 imm)).run js) =
    (execute_LOAD imm rs1 rd false 1).run js.sail

/-- **Main program theorem for LB.**  The structured Jolt-ISA expansion
matches Sail after materializing Jolt's persistent CSR virtual registers. -/
theorem lbProgram_eq_sail (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    lbProgramEqSailStatement imm rs1 rd js h := by
  unfold lbProgramEqSailStatement
  let ea := load_effective_address h.rs1_val imm
  let base := compute_aligned_dword_base_address h.rs1_val imm
  let offset := (ea &&& (7 : BitVec 64)).toNat
  let hwindow := h.dwordWindowFacts
  have hbase_aligned : AlignedDwordAccess base := by
    simpa only [base, hwindow] using hwindow.aligned
  have hbytes_base : MemBytesPresentAt js.sail base 8 := by
    simpa only [base, hwindow] using hwindow.bytes
  have hload_pmp_base : Assumptions.LoadPmpOk base 8 js.sail := by
    simpa only [base, hwindow] using hwindow.load_pmp
  have hread_mmio_base : Assumptions.NotReadableMmio base 8 js.sail := by
    simpa only [base, hwindow] using hwindow.read_mmio
  have hoffset : offset + 1 ≤ 8 := by
    have hlt : offset < 8 := by
      simpa only [offset] using addr_and_seven_lt_eight ea
    omega
  have haddr : base + BitVec.ofNat 64 offset = ea := by
    simpa only [base, ea, offset, compute_aligned_dword_base_address] using
      addr_split_aligned_offset ea
  have hbytes_byte : MemBytesPresentAt js.sail ea 1 := by
    have hsub := memBytesPresentAt_subaccess (s := js.sail) (base := base)
      (baseWidth := 8) (offset := offset) (accessWidth := 1)
      hbytes_base hoffset (by
        have hbase_no_ovf := hbase_aligned.no_ovf
        omega)
    simpa only [haddr] using hsub
  have hload_pmp_byte : Assumptions.LoadPmpOk ea 1 js.sail := by
    have hsub := h.load_pmp.subaccess (offset := offset) (accessWidth := 1) hoffset
    simpa only [base, haddr] using hsub
  have hread_mmio_byte : Assumptions.NotReadableMmio ea 1 js.sail := by
    have hsub := h.not_readable_mmio.subaccess
      (offset := offset) (accessWidth := 1) hoffset
    simpa only [base, haddr] using hsub
  rcases lbProgramAuto_concrete imm rs1 rd js h.cur_privilege h.mstatus_mprv
      h.rs1_val h.rs1_read
      (by simpa only [base] using hbytes_base)
      (by simpa only [base] using hload_pmp_base)
      (by simpa only [base] using hread_mmio_base)
      (by simpa only [ea] using hbytes_byte) with
    ⟨js', hjolt, hjolt_sail⟩
  have hsail := execute_LB_reduces imm rs1 rd js h.cur_privilege h.mstatus_mprv
    h.rs1_val h.rs1_read
    (by simpa only [ea] using hbytes_byte)
    (by simpa only [ea] using hload_pmp_byte)
    (by simpa only [ea] using hread_mmio_byte)
  have hproject_initial : System.systemProject js = js.sail :=
    Projection.systemProject_eq_sail_of_compatible js h.linkedCSRs
  have hprojected : Projection.ProjectedVRegsPreserved js js' :=
    lbProgramAuto_preserves_projected_vregs imm rs1 rd hjolt
  rw [hjolt, hsail]
  simp only [System.systemProjectResult]
  congr 1
  rw [Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved
    js js' rd
    (sign_extend (m := 64)
      (loaded_byte_at js.sail (load_effective_address h.rs1_val imm)
        (by simpa only [ea] using hbytes_byte 0 (by omega))))
    hjolt_sail hprojected]
  rw [hproject_initial]

end LB_main
