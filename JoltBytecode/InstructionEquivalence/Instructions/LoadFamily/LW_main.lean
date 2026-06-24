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

namespace LW_main

/-!
# LW: Jolt load-word (signed) top-level equivalence

From `tracer/src/instruction/lw.rs::inline_sequence_64`:

    VirtualAssertWordAlignment rs1, imm
    ADDI  v0, rs1, imm
    ANDI  rd, v0, -8
    LD    rd, rd, 0
    SLLI  v0, v0, 3
    SRL   rd, rd, v0
    VirtualSignExtendWord rd, rd, 0

This file proves equivalence for the structured `JoltISA.lwProgram`, using
the bridge lemma (a pure bit-vector identity specialised to LW), the Sail-side
load-pipeline helpers, and separate aligned/misaligned cases.

## What lives here (by role)

* `jolt_lw_bridge` — specialisation of the DwordArithmetic identities to
  LW: Jolt's logic-phase expression equals `sign_extend (loaded_word_at …)`.
* `execute_LW_reduces`, `execute_LW_misaligned` — Sail-side `execute_LOAD`
  reductions for the two cases.
* `lwProgram_concrete_aligned`, `lwProgram_concrete_misaligned` —
  program-level Jolt execution facts.
* `lwProgram_eq_sail_aligned`, `lwProgram_eq_sail_misaligned`,
  `lwProgram_eq_sail` — main equivalence theorems.

Shared pure bit-vector, memory-shape, and phase-composition helpers live in
`DwordArithmetic.lean`, `LoadDefUtils.lean`, and `ProgramBlocks.lean`.
-/

/-!
## Program-proof architecture

The public Jolt-side object is `JoltISA.lwProgram`. The proof keeps Ari's
three-block decomposition:

* **load block**: alignment guard, effective-address setup, aligned dword load;
* **logic block**: shift the dword so the requested word is in the low 32 bits;
* **write block**: apply the final signed 32-to-64 extension.

The reusable block lemmas live in `LoadFamily.ProgramBlocks`.  They are
deliberately stated for an arbitrary remaining `Program` tail.  That makes
each block a theorem about `execProgram` composition rather than a one-off
tactic script for the full expansion.
-/

/-- **Bridge lemma for LW.** The Jolt logic-phase computation (shift the
    enclosing dword right by `(ea mod 8) * 8`, take the low 32 bits, then
    sign-extend to 64 bits) equals the Sail-side direct word load
    sign-extended to 64 bits. Requires word alignment `halign : ea & 3 = 0`.
    Pure bit-vector algebra — just combines
    `srl_sign_extend_word_extracts_word` with `loaded_word_in_dword`. -/
theorem jolt_lw_bridge (s : SailState) (addr : BitVec 64)
    (halign : addr &&& 3 = 0)
    (hbytes_base : MemBytesPresentAt s (addr &&& (-8 : BitVec 64)) 8)
    (h_no_ovf_base : (addr &&& (-8 : BitVec 64)).toNat + 7 < 2 ^ 64)
    (hbytes_addr : MemBytesPresentAt s addr 4)
    (h_no_ovf_addr : addr.toNat + 3 < 2 ^ 64) :
    (let dword := loaded_dword_at s (addr &&& (-8 : BitVec 64))
        hbytes_base h_no_ovf_base
     let shift := Sail.BitVec.extractLsb (shift_bits_left addr (3 : BitVec 6)) 5 0
     let shifted := shift_bits_right dword shift
     sign_extend (m := 64) ((Sail.BitVec.extractLsb shifted 31 0) : BitVec 32))
    = sign_extend (m := 64) (loaded_word_at s addr hbytes_addr h_no_ovf_addr) := by
  simp only [srl_sign_extend_word_extracts_word _ _ halign,
    ← loaded_word_in_dword s addr halign hbytes_base h_no_ovf_base
      hbytes_addr h_no_ovf_addr]

-- ============================================================================
-- Top-level LW ↔ Sail equivalence theorems
-- ============================================================================

/-- Sail-side `execute_LOAD imm rs1 rd false 4` reduces to
    `stateAfterWrite rd (sign_extend (loaded_word_at ea))` under aligned,
    translate, physical-memory, and no-overflow evidence. -/
theorem execute_LW_reduces (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (haligned : AlignedAccess (load_effective_address val imm) 4)
    (hbytes : MemBytesPresentAt js.sail (load_effective_address val imm) 4)
    (hload_pmp : Assumptions.LoadPmpOk (load_effective_address val imm) 4 js.sail)
    (hread_mmio : Assumptions.NotReadableMmio (load_effective_address val imm) 4 js.sail)
    (h_no_ovf : (load_effective_address val imm).toNat + 3 < 2 ^ 64) :
    (execute_LOAD imm rs1 rd false 4).run js.sail =
    .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (loaded_word_at js.sail (load_effective_address val imm)
            hbytes h_no_ovf))) := by
  unfold execute_LOAD
  simp only [bind, pure]
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  simp (config := { decide := true }) only []
  simp (config := { decide := true }) only [PreSail.assert, EStateM.bind, pure, EStateM.pure,
       EStateM.run, if_true]
  rw [vmem_read_word_reduces imm rs1 js.sail hpriv hmprv val hrx haligned
      (loaded_word_at js.sail (load_effective_address val imm) hbytes h_no_ovf)
      (mem_read_4_eq_loaded_word _ js.sail hpriv hmprv h_no_ovf hbytes
        hload_pmp hread_mmio)]
  simp only [extend_value, Bool.false_eq_true, if_false, EStateM.bind, EStateM.pure]
  obtain ⟨s', hw⟩ := wX_shape rd
    (sign_extend (m := 64)
      (loaded_word_at js.sail (load_effective_address val imm) hbytes h_no_ovf))
    js.sail
  rw [hw]
  simp only [RETIRE_SUCCESS]
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

/-- Sail-side `execute_LOAD` on a misaligned input returns the same
    memory-alignment exception as Jolt. Uses
    `access_misaligned_4_unaligned_true` from `MemoryUtils`. -/
theorem execute_LW_misaligned (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_align : load_effective_address val imm &&& 3 ≠ 0)
    :
    (execute_LOAD imm rs1 rd false 4).run js.sail =
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
      access_causes_misaligned_exception (Virtaddr ea) 4 false = true := by
    simpa [ea] using access_misaligned_4_unaligned_true ea h_align
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
        ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
        ExceptT.pure, ExceptT.lift,
        MonadLift.monadLift, liftM, monadLift, Functor.map,
        ext_data_get_addr, hrx,
        vmem_read_addr, hmis, ea]
  rfl

/-- Program-level aligned execution for LW.

This is the design pilot for load-family Jolt-ISA proofs. The program is the
structured bytecode object that Rust extraction should eventually emit. The
proof therefore traces the actual interpreter:

* `VirtualAssertWordAlignment` checks `ea & 3 = 0`; on the aligned path it retires and
  leaves the whole Jolt state unchanged.
* `ADDI`, `ANDI`, and `LD` build the enclosing aligned dword address and load
  the dword into virtual register `v1`.
* `slliBlock` prepares the shift amount, and `srlBlock` leaves the selected
  word in `v1`.
* `VirtualSignExtendWord` sign-extends `v1[31:0]` into the real destination.

The theorem is intentionally a trace rather than a black-box simplification:
each local `have` names one bytecode instruction.  That is the pattern we want
for paper-facing proofs, because it lets the reader line the Lean proof up
against the Rust expansion and the Jolt-ISA interpreter. -/
theorem lwProgram_concrete_aligned (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (halign : load_effective_address val imm &&& 3 = 0)
    (hbytes_base :
      MemBytesPresentAt js.sail (compute_aligned_dword_base_address val imm) 8)
    (hload_pmp_base :
      Assumptions.LoadPmpOk (compute_aligned_dword_base_address val imm) 8 js.sail)
    (hread_mmio_base :
      Assumptions.NotReadableMmio (compute_aligned_dword_base_address val imm) 8 js.sail)
    (hbytes_word : MemBytesPresentAt js.sail (load_effective_address val imm) 4)
    (h_word_no_ovf : (load_effective_address val imm).toNat + 3 < 2 ^ 64) :
    ∃ js' : SailJoltState,
      (JoltISA.execProgram (JoltISA.lwProgram imm rs1 rd)).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (loaded_word_at js.sail (load_effective_address val imm)
            hbytes_word h_word_no_ovf)) := by
  let writeTail : JoltISA.Program :=
    .instr (.VirtualSignExtendWord (.xreg rd) (.vreg JoltISA.inlineTmp1)) (.done RETIRE_SUCCESS)
  let logicTail : JoltISA.Program :=
    JoltISA.slliBlock (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp0) (3 : BitVec 6) <|
    JoltISA.srlBlock (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp0) JoltISA.inlineTmp2 writeTail
  rcases LoadProgramBlocks.assertWordSetupBlockAligned logicTail
      imm rs1 js hpriv hmprv val hrx halign hbytes_base hload_pmp_base
      hread_mmio_base with
    ⟨js_load, hload_run, hload_sail, hload_v0, hload_v1⟩
  let dword := loaded_dword_at js.sail (compute_aligned_dword_base_address val imm)
    hbytes_base (aligned_dword_addr_is_aligned_dword_access val imm).no_ovf
  rcases LoadProgramBlocks.lwSrlBlock writeTail imm js js_load val dword
      hload_sail hload_v0 hload_v1 with
    ⟨js_logic, logic_val, hlogic_run, hlogic_val, hlogic_sail, hlogic_v1⟩
  rcases LoadProgramBlocks.sextwWriteBlock rd js js_logic logic_val hlogic_sail hlogic_v1 with
    ⟨js', hwrite_run, hwrite_sail⟩
  refine ⟨js', ?_, ?_⟩
  · unfold JoltISA.lwProgram
    change (JoltISA.execProgram
      (.instr (.VirtualAssertWordAlignment rs1 imm (ExceptionType.E_Load_Addr_Align ())) <|
       .instr (.ADDI (.vreg JoltISA.inlineTmp0) (.xreg rs1) imm) <|
       .instr (.ANDI (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp0) (-8 : BitVec 12)) <|
       .instr (.LD .normal (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp1) 0) logicTail)).run js = .ok RETIRE_SUCCESS js'
    rw [hload_run, hlogic_run, hwrite_run]
  · rw [hwrite_sail, hlogic_val]
    exact congrArg (stateAfterWrite js.sail rd)
      (jolt_lw_bridge js.sail (load_effective_address val imm) halign
        (by
          simpa [compute_aligned_dword_base_address] using hbytes_base)
        (by
          simpa [compute_aligned_dword_base_address] using
            (aligned_dword_addr_is_aligned_dword_access val imm).no_ovf)
        hbytes_word h_word_no_ovf)

/-- Program-level misaligned execution for LW.

This is the control-flow half of the pilot.  The leading `VirtualAssertWordAlignment`
returns `Memory_Exception`; `execProgram` sees that the result is not
`Retire_Success` and therefore does not execute `ADDI`, `LD`, or the writeback
tail.  This is exactly why `Program.instr` carries retire-checking semantics
instead of being a plain list fold over state updates. -/
theorem lwProgram_concrete_misaligned (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_align : load_effective_address val imm &&& 3 ≠ 0) :
    (JoltISA.execProgram (JoltISA.lwProgram imm rs1 rd)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (load_effective_address val imm), ExceptionType.E_Load_Addr_Align ())) js := by
  let e :=
    (Virtaddr (load_effective_address val imm), ExceptionType.E_Load_Addr_Align ())
  unfold JoltISA.lwProgram
  simpa [e] using
    (LoadProgramBlocks.assertWordBlockMisaligned
      (.instr (.ADDI (.vreg JoltISA.inlineTmp0) (.xreg rs1) imm) <|
       .instr (.ANDI (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp0) (-8 : BitVec 12)) <|
       .instr (.LD .normal (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp1) 0) <|
       JoltISA.slliBlock (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp0) (3 : BitVec 6) <|
       JoltISA.srlBlock (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp0) JoltISA.inlineTmp2 <|
       .instr (.VirtualSignExtendWord (.xreg rd) (.vreg JoltISA.inlineTmp1)) <|
       .done RETIRE_SUCCESS)
      imm rs1 js val hrx h_align)

/-- Aligned public program theorem for LW. The Jolt side is the structured
Jolt-ISA program. -/
theorem lwProgram_eq_sail_aligned (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (hbytes_base :
      MemBytesPresentAt js.sail (compute_aligned_dword_base_address val imm) 8)
    (hload_pmp_base :
      Assumptions.LoadPmpOk (compute_aligned_dword_base_address val imm) 8 js.sail)
    (hread_mmio_base :
      Assumptions.NotReadableMmio (compute_aligned_dword_base_address val imm) 8 js.sail)
    (hbytes_word : MemBytesPresentAt js.sail (load_effective_address val imm) 4)
    (hload_pmp_word : Assumptions.LoadPmpOk (load_effective_address val imm) 4 js.sail)
    (hread_mmio_word :
      Assumptions.NotReadableMmio (load_effective_address val imm) 4 js.sail)
    (h_word_no_ovf : (load_effective_address val imm).toNat + 3 < 2 ^ 64)
    (h_align : load_effective_address val imm &&& 3 = 0) :
    projectResult ((JoltISA.execProgram (JoltISA.lwProgram imm rs1 rd)).run js) =
    (execute_LOAD imm rs1 rd false 4).run js.sail := by
  let ea := load_effective_address val imm
  have haligned : AlignedAccess (load_effective_address val imm) 4 := by
    refine
      { misalign := ?_
        split := ?_ }
    · simpa [ea] using access_misaligned_4_aligned_false ea h_align
    · simpa [ea] using split_misaligned_aligned_4 ea h_align
  rcases lwProgram_concrete_aligned imm rs1 rd js hpriv hmprv val hrx h_align
      hbytes_base hload_pmp_base hread_mmio_base hbytes_word h_word_no_ovf with
    ⟨js', hjolt, hjolt_sail⟩
  have hsail := execute_LW_reduces imm rs1 rd js hpriv hmprv val hrx haligned
    hbytes_word hload_pmp_word hread_mmio_word h_word_no_ovf
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail, hsail]

/-- Misaligned public program theorem for LW.  Both sides return the same
load-address-alignment exception, and the Jolt side does so at the explicit
word alignment assertion. -/
theorem lwProgram_eq_sail_misaligned (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_align : load_effective_address val imm &&& 3 ≠ 0) :
    projectResult ((JoltISA.execProgram (JoltISA.lwProgram imm rs1 rd)).run js) =
    (execute_LOAD imm rs1 rd false 4).run js.sail := by
  let ea := load_effective_address val imm
  have hjolt :
      (JoltISA.execProgram (JoltISA.lwProgram imm rs1 rd)).run js =
        .ok (ExecutionResult.Memory_Exception
          (Virtaddr ea, ExceptionType.E_Load_Addr_Align ())) js := by
    simpa [ea] using lwProgram_concrete_misaligned imm rs1 rd js val hrx h_align
  have hsail :
      (execute_LOAD imm rs1 rd false 4).run js.sail =
        .ok (ExecutionResult.Memory_Exception
          (Virtaddr ea, ExceptionType.E_Load_Addr_Align ())) js.sail := by
    simpa [ea] using
      (execute_LW_misaligned imm rs1 rd js val hrx h_align)
  rw [hjolt]
  simp only [projectResult, project]
  symm
  exact hsail

/-- **Main program theorem for LW.**  The structured Jolt-ISA expansion
`lwProgram`, interpreted by `execProgram`, agrees with Sail's `execute_LOAD`
for signed word loads.  The proof dispatches on the same alignment predicate
that the first Jolt virtual instruction checks. -/
theorem lwProgram_eq_sail_of_setup (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (hbytes_base :
      MemBytesPresentAt js.sail (compute_aligned_dword_base_address val imm) 8)
    (hload_pmp_base :
      Assumptions.LoadPmpOk (compute_aligned_dword_base_address val imm) 8 js.sail)
    (hread_mmio_base :
      Assumptions.NotReadableMmio (compute_aligned_dword_base_address val imm) 8 js.sail)
    (hbytes_word : MemBytesPresentAt js.sail (load_effective_address val imm) 4)
    (hload_pmp_word : Assumptions.LoadPmpOk (load_effective_address val imm) 4 js.sail)
    (hread_mmio_word :
      Assumptions.NotReadableMmio (load_effective_address val imm) 4 js.sail)
    (h_word_no_ovf : (load_effective_address val imm).toNat + 3 < 2 ^ 64) :
    projectResult ((JoltISA.execProgram (JoltISA.lwProgram imm rs1 rd)).run js) =
    (execute_LOAD imm rs1 rd false 4).run js.sail := by
  let ea := load_effective_address val imm
  by_cases h_align : ea &&& 3 = 0
  · exact lwProgram_eq_sail_aligned imm rs1 rd js val hrx
      hpriv hmprv hbytes_base hload_pmp_base hread_mmio_base hbytes_word
      hload_pmp_word hread_mmio_word h_word_no_ovf h_align
  · exact lwProgram_eq_sail_misaligned imm rs1 rd js val hrx
      h_align

/-- Successful `LW` expansions do not modify the persistent CSR virtual
registers materialized by `systemProject`. -/
theorem lwProgram_preserves_projected_vregs
    (imm : BitVec 12) (rs1 rd : regidx)
    {js js' : SailJoltState} {result : ExecutionResult}
    (hrun : (JoltISA.execProgram (JoltISA.lwProgram imm rs1 rd)).run js =
      .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe : JoltISA.ProgramWritesNoProtectedVReg
      (JoltISA.lwProgram imm rs1 rd) := by
    unfold JoltISA.lwProgram JoltISA.slliBlock JoltISA.srlBlock
    simp [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg,
      JoltISA.DstWritesNoProtectedVReg,
      JoltISA.loadV0, JoltISA.loadV1, JoltISA.loadInlineTmp]
  exact Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    hsafe hrun

/-- **Main program theorem for LW.**

The public theorem takes one instruction-specific primitive assumption bundle,
and matches Sail after materializing Jolt's persistent CSR virtual registers. -/
def lwProgramEqSailStatement (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (_h : LoadProgramEqSailAssumptions imm rs1 js) : Prop :=
    System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.lwProgram imm rs1 rd)).run js) =
    (execute_LOAD imm rs1 rd false 4).run js.sail

/-- **Main program theorem for LW.**

The public theorem takes one instruction-specific primitive assumption bundle,
and matches Sail after materializing Jolt's persistent CSR virtual registers. -/
theorem lwProgram_eq_sail (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    lwProgramEqSailStatement imm rs1 rd js h := by
  unfold lwProgramEqSailStatement
  -- 
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
  by_cases h_align : ea &&& (3 : BitVec 64) = 0
  · have haligned : AlignedAccess (load_effective_address h.rs1_val imm) 4 := by
      refine
        { misalign := ?_
          split := ?_ }
      · simpa [ea] using access_misaligned_4_aligned_false ea h_align
      · simpa [ea] using split_misaligned_aligned_4 ea h_align
    have h_word_no_ovf : ea.toNat + 3 < 2 ^ 64 := by
      simpa [ea] using aligned_word_addr_no_ovf ea h_align
    have hoff : offset + 4 ≤ 8 := by
      have hcases := word_offset_cases ea h_align
      rcases hcases with h0 | h4
      · simp [offset, h0]
      · simp [offset, h4]
    have haddr : base + BitVec.ofNat 64 offset = ea := by
      simpa [base, ea, offset, compute_aligned_dword_base_address] using
        addr_split_aligned_offset ea
    have hbytes_word : MemBytesPresentAt js.sail ea 4 := by
      have hsub : MemBytesPresentAt js.sail (base + BitVec.ofNat 64 offset) 4 :=
        memBytesPresentAt_subaccess (s := js.sail) (base := base) (baseWidth := 8)
          (offset := offset) (accessWidth := 4) hbytes_base hoff (by
            have hbase_no_ovf := h_base_aligned.no_ovf
            omega)
      simpa [haddr] using hsub
    have hload_pmp_word : Assumptions.LoadPmpOk ea 4 js.sail := by
      have hsub : Assumptions.LoadPmpOk (base + BitVec.ofNat 64 offset) 4 js.sail :=
        h.load_pmp.subaccess (offset := offset) (accessWidth := 4) hoff
      simpa [base, haddr] using hsub
    have hread_mmio_word : Assumptions.NotReadableMmio ea 4 js.sail := by
      have hsub : Assumptions.NotReadableMmio (base + BitVec.ofNat 64 offset) 4 js.sail :=
        h.not_readable_mmio.subaccess (offset := offset) (accessWidth := 4) hoff
      simpa [base, haddr] using hsub
    rcases lwProgram_concrete_aligned imm rs1 rd js h.cur_privilege h.mstatus_mprv
        h.rs1_val
        h.rs1_read (by simpa [ea] using h_align)
        (by simpa [base] using hbytes_base)
        (by simpa [base] using hload_pmp_base)
        (by simpa [base] using hread_mmio_base)
        (by simpa [ea] using hbytes_word)
        (by simpa [ea] using h_word_no_ovf) with
      ⟨js', hjolt, hjolt_sail⟩
    have hsail := execute_LW_reduces imm rs1 rd js h.cur_privilege h.mstatus_mprv
      h.rs1_val h.rs1_read haligned
      (by simpa [ea] using hbytes_word)
      (by simpa [ea] using hload_pmp_word)
      (by simpa [ea] using hread_mmio_word)
      (by simpa [ea] using h_word_no_ovf)
    have h_projected_vregs : Projection.ProjectedVRegsPreserved js js' :=
      lwProgram_preserves_projected_vregs imm rs1 rd hjolt
    rw [hjolt, hsail]
    simp only [System.systemProjectResult]
    congr 1
    rw [Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved
      js js' rd
      (sign_extend (m := 64)
        (loaded_word_at js.sail (load_effective_address h.rs1_val imm)
          (by simpa [ea] using hbytes_word)
          (by simpa [ea] using h_word_no_ovf)))
      hjolt_sail h_projected_vregs]
    rw [h_project_initial]
  · have hjolt := lwProgram_concrete_misaligned imm rs1 rd js h.rs1_val
      h.rs1_read (by simpa [ea] using h_align)
    have hsail := execute_LW_misaligned imm rs1 rd js h.rs1_val
      h.rs1_read (by simpa [ea] using h_align)
    rw [hjolt, hsail]
    simp only [System.systemProjectResult]
    rw [h_project_initial]

end LW_main
