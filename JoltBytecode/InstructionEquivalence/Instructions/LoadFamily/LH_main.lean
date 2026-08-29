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

namespace LH_main

/-!
# LH: Jolt load-halfword (signed) top-level equivalence

From `tracer/src/instruction/lh.rs::inline_sequence_64`:

    VirtualAssertHalfwordAlignment rs1, imm
    ADDI  v0, rs1, imm
    ANDI  v1, v0, -8
    LD    v1, v1, 0
    XORI  v0, v0, 6
    SLLI  v0, v0, 3
    SLL   v1, v1, v0
    SRAI  rd, v1, 48

LH is a hybrid of LW and LB:
* **Has an alignment check** (`addr & 1 = 0`) like LW — so the program
  uses the same "fuse `VirtualAssert…Alignment` with the initial ADDI"
  trick as `jolt_lw`, opening with an explicit
  `let base ← liftSail (rX_bits rs1); if ea & 1 ≠ 0 then … else …`.
* **Writes via SLL+SRAI** like LB — so after the alignment passes, the
  remaining lines use `vreg_ANDI / vreg_LD / vreg_XORI / vreg_SLLI /
  vreg_SLL / vreg_SRAI_to_real`, one Lean line per bytecode line, with
  `XORI v0, v0, 6` and `SRAI rd, v1, 48` in place of LB's `7` / `56`.

## Proof architecture

The Jolt side is the structured `JoltISA.lhProgram`.  The proof composes
program-level helper blocks and uses the pure bridge lemma below to identify
the extracted Jolt value with Sail's direct halfword load.
-/

/-- **Bridge lemma for LH.** The Jolt logic-phase computation (XOR with 6,
    SLL by 3, SLL the dword, arith-shift-right by 48) equals the Sail-
    side direct halfword load sign-extended to 64 bits. Requires halfword
    alignment `halign : addr & 1 = 0`. Pure bit-vector algebra — combines
    `sll_srai_extracts_halfword` with `loaded_halfword_in_dword`,
    mirroring `jolt_lw_bridge`'s shape. -/
theorem jolt_lh_bridge (s : SailState) (addr : BitVec 64)
    (halign : addr &&& 1 = 0)
    (hbytes_base : MemBytesPresentAt s (addr &&& (-8 : BitVec 64)) 8)
    (h_no_ovf_base : (addr &&& (-8 : BitVec 64)).toNat + 7 < 2 ^ 64)
    (hbytes_addr : MemBytesPresentAt s addr 2)
    (h_no_ovf_addr : addr.toNat + 1 < 2 ^ 64) :
    (let dword     := loaded_dword_at s (addr &&& (-8 : BitVec 64))
        hbytes_base h_no_ovf_base
     let xor_addr  := addr ^^^ (6 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6   := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted   := shift_bits_left dword shift_6
     shift_bits_right_arith shifted (48 : BitVec 6))
    = sign_extend (m := 64)
        (loaded_halfword_at s addr hbytes_addr h_no_ovf_addr) := by
  simp only [sll_srai_extracts_halfword _ _ halign,
    ← loaded_halfword_in_dword s addr halign hbytes_base h_no_ovf_base
      hbytes_addr h_no_ovf_addr]

/-- Bridge for the generated fused signed-halfword extraction. -/
theorem jolt_lh_pext_bridge (s : SailState) (base : BitVec 64) (imm : BitVec 12)
    (halign : load_effective_address base imm &&& (1 : BitVec 64) = 0)
    (hbytes : MemBytesPresentAt s (compute_aligned_dword_base_address base imm) 8)
    (h_no_ovf : (compute_aligned_dword_base_address base imm).toNat + 7 < 2 ^ 64)
    (hbytes_addr : MemBytesPresentAt s (load_effective_address base imm) 2)
    (h_no_ovf_addr : (load_effective_address base imm).toNat + 1 < 2 ^ 64) :
    jolt_virtual_pext_signed_value
        (loaded_dword_at s (compute_aligned_dword_base_address base imm)
          hbytes h_no_ovf)
        (jolt_virtual_window_mask_h_value base imm) =
      sign_extend (m := 64)
        (loaded_halfword_at s (load_effective_address base imm)
          hbytes_addr h_no_ovf_addr) := by
  rw [window_mask_h_pext_signed _ _ _ halign]
  have hloaded := loaded_halfword_in_dword s (load_effective_address base imm)
    halign
    (by simpa only [compute_aligned_dword_base_address] using hbytes)
    (by simpa only [compute_aligned_dword_base_address] using h_no_ovf)
    hbytes_addr h_no_ovf_addr
  rw [hloaded]

/-- Sail-side `execute_LOAD imm rs1 rd false 2` reduces to
    `stateAfterWrite rd (sign_extend (loaded_halfword_at ea))` under the
    aligned + translate + phys + no-overflow assumptions. Width-2
    analogue of `execute_LW_reduces`. -/
theorem execute_LH_reduces (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (haligned : AlignedAccess (load_effective_address val imm) 2)
    (hbytes : MemBytesPresentAt js.sail (load_effective_address val imm) 2)
    (hload_pmp : Assumptions.LoadPmpOk (load_effective_address val imm) 2 js.sail)
    (hread_mmio : Assumptions.NotReadableMmio (load_effective_address val imm) 2 js.sail)
    (h_no_ovf : (load_effective_address val imm).toNat + 1 < 2 ^ 64) :
    (execute_LOAD imm rs1 rd false 2).run js.sail =
    .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (loaded_halfword_at js.sail (load_effective_address val imm)
            hbytes h_no_ovf))) := by
  unfold execute_LOAD
  simp only [bind, pure]
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  simp (config := { decide := true }) only []
  simp (config := { decide := true }) only [PreSail.assert, EStateM.bind, pure, EStateM.pure,
       EStateM.run, if_true]
  rw [vmem_read_halfword_reduces imm rs1 js.sail hpriv hmprv val hrx haligned
      (loaded_halfword_at js.sail (load_effective_address val imm) hbytes h_no_ovf)
      (mem_read_2_eq_loaded_halfword _ js.sail hpriv hmprv h_no_ovf hbytes
        hload_pmp hread_mmio)]
  simp only [extend_value, Bool.false_eq_true, if_false, EStateM.bind, EStateM.pure]
  obtain ⟨s', hw⟩ := wX_shape rd
    (sign_extend (m := 64)
      (loaded_halfword_at js.sail (load_effective_address val imm) hbytes h_no_ovf))
    js.sail
  rw [hw]
  simp only [RETIRE_SUCCESS]
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

/-- Sail-side `execute_LOAD` on a misaligned input returns the same
    memory-alignment exception as Jolt. Width-2 variant of
    `execute_LW_misaligned`, using `access_misaligned_2_unaligned_true`. -/
theorem execute_LH_misaligned (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_align : load_effective_address val imm &&& 1 ≠ 0)
    :
    (execute_LOAD imm rs1 rd false 2).run js.sail =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (load_effective_address val imm), ExceptionType.E_Load_Addr_Align ())) js.sail := by
  let ea := load_effective_address val imm
  unfold execute_LOAD
  simp only [bind, pure]
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  simp (config := { decide := true }) only []
  simp (config := { decide := true }) only [PreSail.assert, EStateM.bind, pure, EStateM.pure,
       EStateM.run, if_true]
  unfold vmem_read
  unfold SailME.run PreSail.PreSailME.run
  have hmis :
      access_causes_misaligned_exception (Virtaddr ea) 2 false = true := by
    simpa [ea] using access_misaligned_2_unaligned_true ea h_align
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
        ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
        ExceptT.pure, ExceptT.lift,
        MonadLift.monadLift, liftM, monadLift, Functor.map,
        ext_data_get_addr, hrx,
        vmem_read_addr, hmis, ea]
  rfl

/-!
## Program-level LH theorem

The structured program theorem follows the same architecture as `LB`, with one
additional reusable block at the front: the halfword alignment assertion.
-/

/-- Program-level aligned execution for LH.

The proof is a direct composition of four named facts: successful halfword alignment assertion
plus dword setup, common lane positioning, signed writeback,
and the pure halfword bridge. -/
theorem lhProgram_concrete_aligned (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (halign : load_effective_address val imm &&& 1 = 0)
    (hbytes_base :
      MemBytesPresentAt js.sail (compute_aligned_dword_base_address val imm) 8)
    (hload_pmp_base :
      Assumptions.LoadPmpOk (compute_aligned_dword_base_address val imm) 8 js.sail)
    (hread_mmio_base :
      Assumptions.NotReadableMmio (compute_aligned_dword_base_address val imm) 8 js.sail)
    (hbytes_half : MemBytesPresentAt js.sail (load_effective_address val imm) 2)
    (h_half_no_ovf : (load_effective_address val imm).toNat + 1 < 2 ^ 64) :
    ∃ js' : SailJoltState,
      (JoltISA.execProgram (JoltISA.lhProgram imm rs1 rd)).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (loaded_halfword_at js.sail (load_effective_address val imm)
            hbytes_half h_half_no_ovf)) := by
  let v0 := JoltISA.loadV0For rd
  let v1 := JoltISA.loadV1For rd
  let tmp := JoltISA.loadInlineTmpFor rd
  let dst := JoltISA.loadDstFor rd
  have hv0 : WritableVReg v0 := by simp [v0]
  have hv1 : WritableVReg v1 := by simp [v1]
  have htmp : WritableVReg tmp := by simp [tmp]
  have hv0_ne_v1 : v0 ≠ v1 := by simp [v0, v1]
  have hv0_ne_tmp : v0 ≠ tmp := by simp [v0, tmp]
  have hv1_ne_tmp : v1 ≠ tmp := by simp [v1, tmp]
  let writeTail : JoltISA.Program :=
    .instr (.VirtualSRAI dst (.vreg v1) (JoltISA.sraiBitmask (48 : BitVec 6)))
      (.done RETIRE_SUCCESS)
  let logicTail : JoltISA.Program :=
    .instr (.XORI (.vreg v0) (.vreg v0) (6 : BitVec 12)) <|
    JoltISA.slliBlock (.vreg v0) (.vreg v0) (3 : BitVec 6) <|
    JoltISA.sllBlock (.vreg v1) (.vreg v1) (.vreg v0) tmp writeTail
  rcases LoadProgramBlocks.assertHalfwordSetupBlockAligned logicTail
      v0 v1 imm rs1 js hpriv hmprv val hrx halign hbytes_base hload_pmp_base
      hread_mmio_base hv0 hv1 hv0_ne_v1 with
    ⟨js_load, hload_run, hload_sail, hload_v0, hload_v1⟩
  let dword := loaded_dword_at js.sail (compute_aligned_dword_base_address val imm)
    hbytes_base (aligned_dword_addr_is_aligned_dword_access val imm).no_ovf
  rcases LoadProgramBlocks.xoriSlliSllBlock writeTail v0 v1 tmp imm (6 : BitVec 12)
      js js_load val dword hload_sail hload_v0 hload_v1 hv0 hv1 htmp
      hv0_ne_v1 hv0_ne_tmp hv1_ne_tmp with
    ⟨js_shift, hlogic_run, hshift_sail, _hshift_v0, hshift_v1⟩
  let shiftedValue :=
    shift_bits_left
      dword
      (Sail.BitVec.extractLsb
        (shift_bits_left
          (load_effective_address val imm ^^^ sign_extend (m := 64) (6 : BitVec 12))
          (3 : BitVec 6)) 5 0)
  have hshifted : js_shift.vregs v1 = shiftedValue := by
    simpa [shiftedValue] using hshift_v1
  rcases LoadProgramBlocks.sraiWriteBlock (.done RETIRE_SUCCESS)
      rd v1 (48 : BitVec 6) js js_shift shiftedValue hshift_sail hshifted with
    ⟨js', hwrite_run, hwrite_sail⟩
  refine ⟨js', ?_, ?_⟩
  · unfold JoltISA.lhProgram
    change (JoltISA.execProgram
      (.instr (.VirtualAssertHalfwordAlignment rs1 imm (ExceptionType.E_Load_Addr_Align ())) <|
       .instr (.ADDI (.vreg v0) (.xreg rs1) imm) <|
       .instr (.ANDI (.vreg v1) (.vreg v0) (-8 : BitVec 12)) <|
       .instr (.LD .normal (.vreg v1) (.vreg v1) 0) logicTail)).run js = .ok RETIRE_SUCCESS js'
    rw [hload_run, hlogic_run, hwrite_run]
    rfl
  · rw [hwrite_sail]
    exact congrArg (stateAfterWrite js.sail rd) (by
      have h6 : sign_extend (m := 64) (6 : BitVec 12) = (6 : BitVec 64) := by decide
      simpa [shiftedValue, compute_aligned_dword_base_address, h6] using
        (jolt_lh_bridge js.sail (load_effective_address val imm) halign
          (by simpa [compute_aligned_dword_base_address] using hbytes_base)
          (by
            simpa [compute_aligned_dword_base_address] using
              (aligned_dword_addr_is_aligned_dword_access val imm).no_ovf)
          hbytes_half h_half_no_ovf))

/-- Program-level misaligned execution for LH.

The first instruction is the alignment assertion, so the Jolt program returns
the load-address-alignment exception before the dword setup or writeback code
can run. -/
theorem lhProgram_concrete_misaligned (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_align : load_effective_address val imm &&& 1 ≠ 0) :
    (JoltISA.execProgram (JoltISA.lhProgram imm rs1 rd)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (load_effective_address val imm), ExceptionType.E_Load_Addr_Align ())) js := by
  let e :=
    (Virtaddr (load_effective_address val imm), ExceptionType.E_Load_Addr_Align ())
  let v0 := JoltISA.loadV0For rd
  let v1 := JoltISA.loadV1For rd
  let tmp := JoltISA.loadInlineTmpFor rd
  let dst := JoltISA.loadDstFor rd
  unfold JoltISA.lhProgram
  simpa [e] using
    (LoadProgramBlocks.assertHalfwordBlockMisaligned
      (.instr (.ADDI (.vreg v0) (.xreg rs1) imm) <|
       .instr (.ANDI (.vreg v1) (.vreg v0) (-8 : BitVec 12)) <|
       .instr (.LD .normal (.vreg v1) (.vreg v1) 0) <|
       .instr (.XORI (.vreg v0) (.vreg v0) (6 : BitVec 12)) <|
       JoltISA.slliBlock (.vreg v0) (.vreg v0) (3 : BitVec 6) <|
       JoltISA.sllBlock (.vreg v1) (.vreg v1) (.vreg v0) tmp <|
       .instr (.VirtualSRAI dst (.vreg v1) (JoltISA.sraiBitmask (48 : BitVec 6))) <|
       .done RETIRE_SUCCESS)
      imm rs1 js val hrx h_align)

/-- Aligned execution of the Rust-generated fused `LH` expansion. -/
theorem lhProgramAuto_concrete_aligned (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (halign : load_effective_address val imm &&& (1 : BitVec 64) = 0)
    (hbytes_base :
      MemBytesPresentAt js.sail (compute_aligned_dword_base_address val imm) 8)
    (hload_pmp_base :
      Assumptions.LoadPmpOk (compute_aligned_dword_base_address val imm) 8 js.sail)
    (hread_mmio_base :
      Assumptions.NotReadableMmio (compute_aligned_dword_base_address val imm) 8 js.sail)
    (hbytes_half : MemBytesPresentAt js.sail (load_effective_address val imm) 2)
    (h_half_no_ovf : (load_effective_address val imm).toNat + 1 < 2 ^ 64) :
    ∃ js' : SailJoltState,
      (JoltISA.execProgram (JoltISA.lhProgramAuto rd rs1 imm)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (loaded_halfword_at js.sail (load_effective_address val imm)
            hbytes_half h_half_no_ovf)) := by
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
  let maskValue := jolt_virtual_window_mask_h_value val imm
  by_cases hx0 : JoltISA.isX0 rd = true
  · let tail : JoltISA.Program :=
      .instr (.VirtualWindowMaskH (.vreg v41) (.xreg rs1) imm) <|
      .instr (.VirtualPextSigned (.vreg v40) (.vreg v42) (.vreg v41)) <|
      .done RETIRE_SUCCESS
    rcases LoadProgramBlocks.assertHalfwordAlignAddrLdBlockAligned
        tail v42 imm rs1 js hpriv hmprv val hrx halign
        hbytes_base hload_pmp_base hread_mmio_base hv42 with
      ⟨js_load, hload_run, hload_sail, _hload_value⟩
    let js_mask : SailJoltState :=
      { sail := js_load.sail
        vregs := fun r => if r = v41 then maskValue else js_load.vregs r }
    have hrx_load : rX_bits rs1 js_load.sail = .ok val js_load.sail := by
      simpa only [hload_sail] using hrx
    have hmask :
        (JoltISA.execInstr
          (.VirtualWindowMaskH (.vreg v41) (.xreg rs1) imm)).run js_load =
          .ok RETIRE_SUCCESS js_mask := by
      simpa only [js_mask, maskValue] using
        JoltISA.virtual_window_mask_h_run_vreg_xreg
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
    · unfold JoltISA.lhProgramAuto
      rw [hx0]
      simp only [if_true]
      change (JoltISA.execProgram
        (.instr
          (.VirtualAssertHalfwordAlignment rs1 imm
            (ExceptionType.E_Load_Addr_Align ())) <|
         .instr (.VirtualAlignAddr (.vreg v42) (.xreg rs1) imm) <|
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
      .instr (.VirtualWindowMaskH (.vreg v40) (.xreg rs1) imm) <|
      .instr (.VirtualPextSigned (.xreg rd) (.vreg v41) (.vreg v40)) <|
      .done RETIRE_SUCCESS
    rcases LoadProgramBlocks.assertHalfwordAlignAddrLdBlockAligned
        tail v41 imm rs1 js hpriv hmprv val hrx halign
        hbytes_base hload_pmp_base hread_mmio_base hv41 with
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
          (.VirtualWindowMaskH (.vreg v40) (.xreg rs1) imm)).run js_load =
          .ok RETIRE_SUCCESS js_mask := by
      simpa only [js_mask, maskValue] using
        JoltISA.virtual_window_mask_h_run_vreg_xreg
          v40 rs1 imm js_load val hrx_load hv40
    have hmask_value : js_mask.vregs v40 = maskValue := by
      simp only [js_mask, if_true]
    have hmask_dword : js_mask.vregs v41 = dword := by
      simp only [js_mask, if_neg h40_ne_41.symm, dword]
      exact hload_value
    let finalValue := sign_extend (m := 64)
      (loaded_halfword_at js.sail (load_effective_address val imm)
        hbytes_half h_half_no_ovf)
    have hpext_value :
        jolt_virtual_pext_signed_value (js_mask.vregs v41) (js_mask.vregs v40) =
          finalValue := by
      rw [hmask_dword, hmask_value]
      exact jolt_lh_pext_bridge js.sail val imm halign hbytes_base
        (aligned_dword_addr_is_aligned_dword_access val imm).no_ovf
        hbytes_half h_half_no_ovf
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
    · unfold JoltISA.lhProgramAuto
      rw [hx0_false]
      simp only [Bool.false_eq_true, if_false]
      change (JoltISA.execProgram
        (.instr
          (.VirtualAssertHalfwordAlignment rs1 imm
            (ExceptionType.E_Load_Addr_Align ())) <|
         .instr (.VirtualAlignAddr (.vreg v41) (.xreg rs1) imm) <|
         .instr (.LD .normal (.vreg v41) (.vreg v41) 0) tail)).run js = _
      rw [hload_run]
      rw [JoltISA.execProgram_instr_run_retire _ _ js_load js_mask hmask]
      rw [JoltISA.execProgram_instr_run_retire _ _ js_mask js' hpext]
      rfl
    · exact wX_bits_eq_stateAfterWrite rd finalValue js.sail s' hwrite

/-- Misaligned execution of the generated `LH` expansion stops at its first
instruction, independently of the `rd = x0` specialization. -/
theorem lhProgramAuto_concrete_misaligned (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_align : load_effective_address val imm &&& (1 : BitVec 64) ≠ 0) :
    (JoltISA.execProgram (JoltISA.lhProgramAuto rd rs1 imm)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (load_effective_address val imm),
          ExceptionType.E_Load_Addr_Align ())) js := by
  unfold JoltISA.lhProgramAuto
  split <;>
    exact LoadProgramBlocks.assertHalfwordBlockMisaligned
      _ imm rs1 js val hrx h_align

/-- Aligned public program theorem for LH. -/
theorem lhProgram_eq_sail_aligned (imm : BitVec 12)
    (rs1 rd : regidx)
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
    (hbytes_half : MemBytesPresentAt js.sail (load_effective_address val imm) 2)
    (hload_pmp_half : Assumptions.LoadPmpOk (load_effective_address val imm) 2 js.sail)
    (hread_mmio_half :
      Assumptions.NotReadableMmio (load_effective_address val imm) 2 js.sail)
    (h_half_no_ovf : (load_effective_address val imm).toNat + 1 < 2 ^ 64)
    (h_align : load_effective_address val imm &&& 1 = 0) :
    projectResult ((JoltISA.execProgram (JoltISA.lhProgram imm rs1 rd)).run js) =
    (execute_LOAD imm rs1 rd false 2).run js.sail := by
  let ea := load_effective_address val imm
  have haligned : AlignedAccess (load_effective_address val imm) 2 := by
    refine
      { misalign := ?_
        split := ?_ }
    · simpa [ea] using access_misaligned_2_aligned_false ea h_align
    · simpa [ea] using split_misaligned_aligned_2 ea h_align
  rcases lhProgram_concrete_aligned imm rs1 rd js hpriv hmprv val hrx h_align
      hbytes_base hload_pmp_base hread_mmio_base hbytes_half h_half_no_ovf with
    ⟨js', hjolt, hjolt_sail⟩
  have hsail := execute_LH_reduces imm rs1 rd js hpriv hmprv val hrx haligned
    hbytes_half hload_pmp_half hread_mmio_half h_half_no_ovf
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail, hsail]

/-- Misaligned public program theorem for LH. -/
theorem lhProgram_eq_sail_misaligned (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_align : load_effective_address val imm &&& 1 ≠ 0) :
    projectResult ((JoltISA.execProgram (JoltISA.lhProgram imm rs1 rd)).run js) =
    (execute_LOAD imm rs1 rd false 2).run js.sail := by
  let ea := load_effective_address val imm
  have hjolt :
      (JoltISA.execProgram (JoltISA.lhProgram imm rs1 rd)).run js =
        .ok (ExecutionResult.Memory_Exception
          (Virtaddr ea, ExceptionType.E_Load_Addr_Align ())) js := by
    simpa [ea] using lhProgram_concrete_misaligned imm rs1 rd js val hrx h_align
  have hsail :
      (execute_LOAD imm rs1 rd false 2).run js.sail =
        .ok (ExecutionResult.Memory_Exception
          (Virtaddr ea, ExceptionType.E_Load_Addr_Align ())) js.sail := by
    simpa [ea] using
      (execute_LH_misaligned imm rs1 rd js val hrx h_align)
  rw [hjolt]
  simp only [projectResult, project]
  symm
  exact hsail

/-- Successful `LH` expansions do not modify the persistent CSR virtual
registers materialized by `systemProject`. -/
theorem lhProgram_preserves_projected_vregs
    (imm : BitVec 12) (rs1 rd : regidx)
    {js js' : SailJoltState} {result : ExecutionResult}
    (hrun : (JoltISA.execProgram (JoltISA.lhProgram imm rs1 rd)).run js =
      .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe : JoltISA.ProgramWritesNoProtectedVReg
      (JoltISA.lhProgram imm rs1 rd) := by
    unfold JoltISA.lhProgram JoltISA.slliBlock JoltISA.sllBlock
    simp [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg]
  exact Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    hsafe hrun

/-- The generated `LH` expansion writes only instruction-local scratch vregs. -/
theorem lhProgramAuto_preserves_projected_vregs
    (imm : BitVec 12) (rs1 rd : regidx)
    {js js' : SailJoltState} {result : ExecutionResult}
    (hrun : (JoltISA.execProgram (JoltISA.lhProgramAuto rd rs1 imm)).run js =
      .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe : JoltISA.ProgramWritesNoProtectedVReg
      (JoltISA.lhProgramAuto rd rs1 imm) := by
    unfold JoltISA.lhProgramAuto
    split <;>
      simp only [JoltISA.ProgramWritesNoProtectedVReg,
        JoltISA.InstrWritesNoProtectedVReg, JoltISA.DstWritesNoProtectedVReg,
        JoltISA.sideEffectingDst, and_true] <;>
      norm_num [JoltISA.IsProtectedJoltRegister, JoltISA.joltRegisterSlot,
        JoltISA.JoltRegisterSlot.isProtected]
  exact Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    hsafe hrun

/-- **Main program theorem for LH.**  The structured Jolt-ISA expansion
matches Sail after materializing Jolt's persistent CSR virtual registers. -/
def lhProgramEqSailStatement (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (_h : LoadProgramEqSailAssumptions imm rs1 js) : Prop :=
    System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.lhProgramAuto rd rs1 imm)).run js) =
    (execute_LOAD imm rs1 rd false 2).run js.sail

/-- **Main program theorem for LH.**  The structured Jolt-ISA expansion
matches Sail after materializing Jolt's persistent CSR virtual registers. -/
theorem lhProgram_eq_sail (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    lhProgramEqSailStatement imm rs1 rd js h := by
  unfold lhProgramEqSailStatement
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
  have hproject_initial : System.systemProject js = js.sail :=
    Projection.systemProject_eq_sail_of_compatible js h.linkedCSRs
  by_cases h_align : ea &&& (1 : BitVec 64) = 0
  · have haligned : AlignedAccess (load_effective_address h.rs1_val imm) 2 := by
      refine
        { misalign := ?_
          split := ?_ }
      · simpa only [ea] using access_misaligned_2_aligned_false ea h_align
      · simpa only [ea] using split_misaligned_aligned_2 ea h_align
    have h_half_no_ovf : ea.toNat + 1 < 2 ^ 64 := by
      exact aligned_halfword_addr_no_ovf ea h_align
    have hoffset : offset + 2 ≤ 8 := by
      have hlt : offset < 7 := by
        simpa only [offset] using addr_and_seven_halfword_lt_seven ea h_align
      omega
    have haddr : base + BitVec.ofNat 64 offset = ea := by
      simpa only [base, ea, offset, compute_aligned_dword_base_address] using
        addr_split_aligned_offset ea
    have hbytes_half : MemBytesPresentAt js.sail ea 2 := by
      have hsub := memBytesPresentAt_subaccess (s := js.sail) (base := base)
        (baseWidth := 8) (offset := offset) (accessWidth := 2)
        hbytes_base hoffset (by
          have hbase_no_ovf := hbase_aligned.no_ovf
          omega)
      simpa only [haddr] using hsub
    have hload_pmp_half : Assumptions.LoadPmpOk ea 2 js.sail := by
      have hsub := h.load_pmp.subaccess
        (offset := offset) (accessWidth := 2) hoffset
      simpa only [base, haddr] using hsub
    have hread_mmio_half : Assumptions.NotReadableMmio ea 2 js.sail := by
      have hsub := h.not_readable_mmio.subaccess
        (offset := offset) (accessWidth := 2) hoffset
      simpa only [base, haddr] using hsub
    rcases lhProgramAuto_concrete_aligned imm rs1 rd js
        h.cur_privilege h.mstatus_mprv h.rs1_val h.rs1_read
        (by simpa only [ea] using h_align)
        (by simpa only [base] using hbytes_base)
        (by simpa only [base] using hload_pmp_base)
        (by simpa only [base] using hread_mmio_base)
        (by simpa only [ea] using hbytes_half)
        (by simpa only [ea] using h_half_no_ovf) with
      ⟨js', hjolt, hjolt_sail⟩
    have hsail := execute_LH_reduces imm rs1 rd js
      h.cur_privilege h.mstatus_mprv h.rs1_val h.rs1_read haligned
      (by simpa only [ea] using hbytes_half)
      (by simpa only [ea] using hload_pmp_half)
      (by simpa only [ea] using hread_mmio_half)
      (by simpa only [ea] using h_half_no_ovf)
    have hprojected : Projection.ProjectedVRegsPreserved js js' :=
      lhProgramAuto_preserves_projected_vregs imm rs1 rd hjolt
    rw [hjolt, hsail]
    simp only [System.systemProjectResult]
    congr 1
    rw [Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved
      js js' rd
      (sign_extend (m := 64)
        (loaded_halfword_at js.sail (load_effective_address h.rs1_val imm)
          (by simpa only [ea] using hbytes_half)
          (by simpa only [ea] using h_half_no_ovf)))
      hjolt_sail hprojected]
    rw [hproject_initial]
  · have hjolt := lhProgramAuto_concrete_misaligned imm rs1 rd js h.rs1_val
      h.rs1_read (by simpa only [ea] using h_align)
    have hsail := execute_LH_misaligned imm rs1 rd js h.rs1_val
      h.rs1_read (by simpa only [ea] using h_align)
    rw [hjolt, hsail]
    simp only [System.systemProjectResult]
    rw [hproject_initial]

end LH_main
