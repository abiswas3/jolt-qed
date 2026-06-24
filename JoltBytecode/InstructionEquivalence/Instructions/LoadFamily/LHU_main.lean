import JoltBytecode.InstructionEquivalence.ProofSupport.BundleLemmas
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

namespace LHU_main

/-!
# LHU: Jolt load-halfword (unsigned) top-level equivalence

From `tracer/src/instruction/lhu.rs::inline_sequence_64`:

    VirtualAssertHalfwordAlignment rs1, imm
    ADDI  v0, rs1, imm
    ANDI  v1, v0, -8
    LD    v1, v1, 0
    XORI  v0, v0, 6
    SLLI  v0, v0, 3
    SLL   v1, v1, v0
    SRLI  rd, v1, 48

Identical to `LH_main` except the final `SRLI` (logical right shift —
zero-fill) replaces `SRAI` (arithmetic right shift — sign-fill), and
`execute_LOAD`'s signed/unsigned flag is `true` instead of `false`.
-/

/-- **Bridge lemma for LHU.** Logical sibling of `jolt_lh_bridge`: the
    Jolt logic-phase computation (XOR 6, SLL 3, SLL the dword, SRLI 48)
    equals the Sail-side direct halfword load zero-extended to 64 bits.
    Requires halfword alignment. -/
theorem jolt_lhu_bridge (s : SailState) (addr : BitVec 64)
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
     shift_bits_right shifted (48 : BitVec 6))
    = zero_extend (m := 64)
        (loaded_halfword_at s addr hbytes_addr h_no_ovf_addr) := by
  simp only [sll_srli_extracts_halfword _ _ halign,
    ← loaded_halfword_in_dword s addr halign hbytes_base h_no_ovf_base
      hbytes_addr h_no_ovf_addr]

/-- Sail-side `execute_LOAD … true 2` reduces to `stateAfterWrite rd
    (zero_extend (loaded_halfword_at ea))`. -/
theorem execute_LHU_reduces (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (haligned : AlignedAccess (load_effective_address val imm) 2)
    (hbytes : MemBytesPresentAt js.sail (load_effective_address val imm) 2)
    (hload_pmp : Assumptions.LoadPmpOk (load_effective_address val imm) 2 js.sail)
    (hread_mmio : Assumptions.NotReadableMmio (load_effective_address val imm) 2 js.sail)
    (h_no_ovf : (load_effective_address val imm).toNat + 1 < 2 ^ 64) :
    (execute_LOAD imm rs1 rd true 2).run js.sail =
    .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd
        (zero_extend (m := 64)
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
  simp only [extend_value, if_true, EStateM.bind, EStateM.pure]
  obtain ⟨s', hw⟩ := wX_shape rd
    (zero_extend (m := 64)
      (loaded_halfword_at js.sail (load_effective_address val imm) hbytes h_no_ovf))
    js.sail
  rw [hw]
  simp only [RETIRE_SUCCESS]
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

/-- Sail-side misaligned. -/
theorem execute_LHU_misaligned (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_align : load_effective_address val imm &&& 1 ≠ 0)
    :
    (execute_LOAD imm rs1 rd true 2).run js.sail =
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
## Program-level LHU theorem

This is the unsigned halfword sibling of the program-level `LH` theorem.  The
front of the proof is identical; only the final write block and pure bridge
use logical right shift / zero extension.
-/

/-- Program-level aligned execution for LHU.

The theorem is intentionally phrased in the same boundary language as `LH`:
alignment plus setup, lane positioning, unsigned writeback, then the pure
bridge to Sail's direct halfword load. -/
theorem lhuProgram_concrete_aligned (imm : BitVec 12) (rs1 rd : regidx)
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
      (JoltISA.execProgram (JoltISA.lhuProgram imm rs1 rd)).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (zero_extend (m := 64)
          (loaded_halfword_at js.sail (load_effective_address val imm)
            hbytes_half h_half_no_ovf)) := by
  let writeTail : JoltISA.Program :=
    .instr (.VirtualSRLI (.xreg rd) (.vreg JoltISA.inlineTmp1) (JoltISA.srliBitmask (48 : BitVec 6)))
      (.done RETIRE_SUCCESS)
  let logicTail : JoltISA.Program :=
    .instr (.XORI (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp0) (6 : BitVec 12)) <|
    JoltISA.slliBlock (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp0) (3 : BitVec 6) <|
    JoltISA.sllBlock (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp0) JoltISA.inlineTmp2 writeTail
  rcases LoadProgramBlocks.assertHalfwordSetupBlockAligned logicTail
      imm rs1 js hpriv hmprv val hrx halign hbytes_base hload_pmp_base
      hread_mmio_base with
    ⟨js_load, hload_run, hload_sail, hload_v0, hload_v1⟩
  let dword := loaded_dword_at js.sail (compute_aligned_dword_base_address val imm)
    hbytes_base (aligned_dword_addr_is_aligned_dword_access val imm).no_ovf
  rcases LoadProgramBlocks.xoriSlliSllBlock writeTail imm (6 : BitVec 12)
      js js_load val dword hload_sail hload_v0 hload_v1 with
    ⟨js_shift, hlogic_run, hshift_sail, _hshift_v0, hshift_v1⟩
  let shiftedValue :=
    shift_bits_left
      dword
      (Sail.BitVec.extractLsb
        (shift_bits_left
          (load_effective_address val imm ^^^ sign_extend (m := 64) (6 : BitVec 12))
          (3 : BitVec 6)) 5 0)
  have hshifted : js_shift.vregs JoltISA.inlineTmp1 = shiftedValue := by
    simpa [shiftedValue] using hshift_v1
  rcases LoadProgramBlocks.srliWriteBlock (.done RETIRE_SUCCESS)
      rd (48 : BitVec 6) js js_shift shiftedValue hshift_sail hshifted with
    ⟨js', hwrite_run, hwrite_sail⟩
  refine ⟨js', ?_, ?_⟩
  · unfold JoltISA.lhuProgram
    change (JoltISA.execProgram
      (.instr (.VirtualAssertHalfwordAlignment rs1 imm (ExceptionType.E_Load_Addr_Align ())) <|
       .instr (.ADDI (.vreg JoltISA.inlineTmp0) (.xreg rs1) imm) <|
       .instr (.ANDI (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp0) (-8 : BitVec 12)) <|
       .instr (.LD .normal (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp1) 0) logicTail)).run js = .ok RETIRE_SUCCESS js'
    rw [hload_run, hlogic_run, hwrite_run]
    rfl
  · rw [hwrite_sail]
    exact congrArg (stateAfterWrite js.sail rd) (by
      have h6 : sign_extend (m := 64) (6 : BitVec 12) = (6 : BitVec 64) := by decide
      simpa [shiftedValue, compute_aligned_dword_base_address, h6] using
        (jolt_lhu_bridge js.sail (load_effective_address val imm) halign
          (by simpa [compute_aligned_dword_base_address] using hbytes_base)
          (by
            simpa [compute_aligned_dword_base_address] using
              (aligned_dword_addr_is_aligned_dword_access val imm).no_ovf)
          hbytes_half h_half_no_ovf))

/-- Program-level misaligned execution for LHU. -/
theorem lhuProgram_concrete_misaligned (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_align : load_effective_address val imm &&& 1 ≠ 0) :
    (JoltISA.execProgram (JoltISA.lhuProgram imm rs1 rd)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (load_effective_address val imm), ExceptionType.E_Load_Addr_Align ())) js := by
  let e :=
    (Virtaddr (load_effective_address val imm), ExceptionType.E_Load_Addr_Align ())
  unfold JoltISA.lhuProgram
  simpa [e] using
    (LoadProgramBlocks.assertHalfwordBlockMisaligned
      (.instr (.ADDI (.vreg JoltISA.inlineTmp0) (.xreg rs1) imm) <|
       .instr (.ANDI (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp0) (-8 : BitVec 12)) <|
       .instr (.LD .normal (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp1) 0) <|
       .instr (.XORI (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp0) (6 : BitVec 12)) <|
       JoltISA.slliBlock (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp0) (3 : BitVec 6) <|
       JoltISA.sllBlock (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp0) JoltISA.inlineTmp2 <|
       .instr (.VirtualSRLI (.xreg rd) (.vreg JoltISA.inlineTmp1) (JoltISA.srliBitmask (48 : BitVec 6))) <|
       .done RETIRE_SUCCESS)
      imm rs1 js val hrx h_align)

/-- Aligned public program theorem for LHU. -/
theorem lhuProgram_eq_sail_aligned (imm : BitVec 12)
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
    projectResult ((JoltISA.execProgram (JoltISA.lhuProgram imm rs1 rd)).run js) =
    (execute_LOAD imm rs1 rd true 2).run js.sail := by
  let ea := load_effective_address val imm
  have haligned : AlignedAccess (load_effective_address val imm) 2 := by
    refine
      { misalign := ?_
        split := ?_ }
    · simpa [ea] using access_misaligned_2_aligned_false ea h_align
    · simpa [ea] using split_misaligned_aligned_2 ea h_align
  rcases lhuProgram_concrete_aligned imm rs1 rd js hpriv hmprv val hrx h_align
      hbytes_base hload_pmp_base hread_mmio_base hbytes_half h_half_no_ovf with
    ⟨js', hjolt, hjolt_sail⟩
  have hsail := execute_LHU_reduces imm rs1 rd js hpriv hmprv val hrx haligned
    hbytes_half hload_pmp_half hread_mmio_half h_half_no_ovf
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail, hsail]

/-- Misaligned public program theorem for LHU. -/
theorem lhuProgram_eq_sail_misaligned (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_align : load_effective_address val imm &&& 1 ≠ 0) :
    projectResult ((JoltISA.execProgram (JoltISA.lhuProgram imm rs1 rd)).run js) =
    (execute_LOAD imm rs1 rd true 2).run js.sail := by
  let ea := load_effective_address val imm
  have hjolt :
      (JoltISA.execProgram (JoltISA.lhuProgram imm rs1 rd)).run js =
        .ok (ExecutionResult.Memory_Exception
          (Virtaddr ea, ExceptionType.E_Load_Addr_Align ())) js := by
    simpa [ea] using lhuProgram_concrete_misaligned imm rs1 rd js val hrx h_align
  have hsail :
      (execute_LOAD imm rs1 rd true 2).run js.sail =
        .ok (ExecutionResult.Memory_Exception
          (Virtaddr ea, ExceptionType.E_Load_Addr_Align ())) js.sail := by
    simpa [ea] using
      (execute_LHU_misaligned imm rs1 rd js val hrx h_align)
  rw [hjolt]
  simp only [projectResult, project]
  symm
  exact hsail

/-- Successful `LHU` expansions do not modify the persistent CSR virtual
registers materialized by `systemProject`. -/
theorem lhuProgram_preserves_projected_vregs
    (imm : BitVec 12) (rs1 rd : regidx)
    {js js' : SailJoltState} {result : ExecutionResult}
    (hrun : (JoltISA.execProgram (JoltISA.lhuProgram imm rs1 rd)).run js =
      .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe : JoltISA.ProgramWritesNoProtectedVReg
      (JoltISA.lhuProgram imm rs1 rd) := by
    unfold JoltISA.lhuProgram JoltISA.slliBlock JoltISA.sllBlock
    simp [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg,
      JoltISA.DstWritesNoProtectedVReg,
      JoltISA.loadV0, JoltISA.loadV1, JoltISA.loadInlineTmp]
  exact Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    hsafe hrun

/-- **Main program theorem for LHU.**  The structured Jolt-ISA expansion
matches Sail after materializing Jolt's persistent CSR virtual registers. -/
def lhuProgramEqSailStatement (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (_h : LoadProgramEqSailAssumptions imm rs1 js) : Prop :=
    System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.lhuProgram imm rs1 rd)).run js) =
    (execute_LOAD imm rs1 rd true 2).run js.sail

/-- **Main program theorem for LHU.**  The structured Jolt-ISA expansion
matches Sail after materializing Jolt's persistent CSR virtual registers. -/
theorem lhuProgram_eq_sail (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    lhuProgramEqSailStatement imm rs1 rd js h := by
  unfold lhuProgramEqSailStatement
  let ea := load_effective_address h.rs1_val imm
  let base := compute_aligned_dword_base_address h.rs1_val imm
  let offset := (ea &&& (7 : BitVec 64)).toNat
  have h_base_aligned : AlignedDwordAccess base := by
    simpa [base, compute_aligned_dword_base_address, aligned_dword_addr_eq,
      load_effective_address] using
      aligned_dword_addr_is_aligned_dword_access h.rs1_val imm
  have hbytes_base : MemBytesPresentAt js.sail base 8 := by
    simpa [base] using h.dword_present.memBytesPresentAt
  have hload_pmp_base : Assumptions.LoadPmpOk base 8 js.sail := by
    simpa [base] using h.load_pmp.subaccess (offset := 0) (accessWidth := 8) (by omega)
  have hread_mmio_base : Assumptions.NotReadableMmio base 8 js.sail := by
    simpa [base] using h.not_readable_mmio.subaccess
      (offset := 0) (accessWidth := 8) (by omega)
  have h_project_initial : System.systemProject js = js.sail :=
    Projection.systemProject_eq_sail_of_compatible js h.linkedCSRs
  by_cases h_align : ea &&& (1 : BitVec 64) = 0
  · have haligned : AlignedAccess (load_effective_address h.rs1_val imm) 2 := by
      refine
        { misalign := ?_
          split := ?_ }
      · simpa [ea] using access_misaligned_2_aligned_false ea h_align
      · simpa [ea] using split_misaligned_aligned_2 ea h_align
    have h_half_no_ovf : ea.toNat + 1 < 2 ^ 64 := by
      simpa [ea] using aligned_halfword_addr_no_ovf ea h_align
    have hoff : offset + 2 ≤ 8 := by
      have hlt : offset < 7 := by
        simpa only [offset] using addr_and_seven_halfword_lt_seven ea h_align
      omega
    have haddr : base + BitVec.ofNat 64 offset = ea := by
      simpa [base, ea, offset, compute_aligned_dword_base_address] using
        addr_split_aligned_offset ea
    have hbytes_half : MemBytesPresentAt js.sail ea 2 := by
      have hsub : MemBytesPresentAt js.sail (base + BitVec.ofNat 64 offset) 2 :=
        memBytesPresentAt_subaccess (s := js.sail) (base := base) (baseWidth := 8)
          (offset := offset) (accessWidth := 2) hbytes_base hoff (by
            have hbase_no_ovf := h_base_aligned.no_ovf
            omega)
      simpa [haddr] using hsub
    have hload_pmp_half : Assumptions.LoadPmpOk ea 2 js.sail := by
      have hsub : Assumptions.LoadPmpOk (base + BitVec.ofNat 64 offset) 2 js.sail :=
        h.load_pmp.subaccess (offset := offset) (accessWidth := 2) hoff
      simpa [base, haddr] using hsub
    have hread_mmio_half : Assumptions.NotReadableMmio ea 2 js.sail := by
      have hsub : Assumptions.NotReadableMmio (base + BitVec.ofNat 64 offset) 2 js.sail :=
        h.not_readable_mmio.subaccess (offset := offset) (accessWidth := 2) hoff
      simpa [base, haddr] using hsub
    rcases lhuProgram_concrete_aligned imm rs1 rd js h.cur_privilege h.mstatus_mprv
        h.rs1_val
        h.rs1_read (by simpa [ea] using h_align)
        (by simpa [base] using hbytes_base)
        (by simpa [base] using hload_pmp_base)
        (by simpa [base] using hread_mmio_base)
        (by simpa [ea] using hbytes_half)
        (by simpa [ea] using h_half_no_ovf) with
      ⟨js', hjolt, hjolt_sail⟩
    have hsail := execute_LHU_reduces imm rs1 rd js h.cur_privilege h.mstatus_mprv
      h.rs1_val h.rs1_read haligned
      (by simpa [ea] using hbytes_half)
      (by simpa [ea] using hload_pmp_half)
      (by simpa [ea] using hread_mmio_half)
      (by simpa [ea] using h_half_no_ovf)
    have h_projected_vregs : Projection.ProjectedVRegsPreserved js js' :=
      lhuProgram_preserves_projected_vregs imm rs1 rd hjolt
    rw [hjolt, hsail]
    simp only [System.systemProjectResult]
    congr 1
    rw [Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved
      js js' rd
      (zero_extend (m := 64)
        (loaded_halfword_at js.sail (load_effective_address h.rs1_val imm)
          (by simpa [ea] using hbytes_half)
          (by simpa [ea] using h_half_no_ovf)))
      hjolt_sail h_projected_vregs]
    rw [h_project_initial]
  · have hjolt := lhuProgram_concrete_misaligned imm rs1 rd js h.rs1_val
      h.rs1_read (by simpa [ea] using h_align)
    have hsail := execute_LHU_misaligned imm rs1 rd js h.rs1_val
      h.rs1_read (by simpa [ea] using h_align)
    rw [hjolt, hsail]
    simp only [System.systemProjectResult]
    rw [h_project_initial]

end LHU_main
