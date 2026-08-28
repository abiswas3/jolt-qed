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

namespace LWU_main

/-!
# LWU: Jolt load-word (unsigned) top-level equivalence

From `tracer/src/instruction/lwu.rs::inline_sequence_64`:

    VirtualAssertWordAlignment rs1, imm
    ADDI  v0, rs1, imm
    ANDI  v1, v0, -8
    LD    v1, v1, 0
    XORI  v0, v0, 4
    SLLI  v0, v0, 3
    SLL   v1, v1, v0
    SRLI  rd, v1, 32

Unlike `LW` (which uses SRL + `VirtualSignExtendWord`), LWU uses the
byte-family SLL+SRLI pattern. XORI 4 computes the left-shift distance
that positions the target word at the top of the 64-bit register; SRLI
32 then pulls it down with zero-extension.

Alignment guard structurally matches `jolt_lw`: the initial
`VirtualAssertWordAlignment` is fused with the first real-register read.
-/

/-- **Bridge lemma for LWU.** The Jolt logic-phase computation (XOR 4,
    SLL 3, SLL the dword, SRLI 32) equals the Sail-side direct word
    load zero-extended to 64 bits. Requires word alignment. -/
theorem jolt_lwu_bridge (s : SailState) (addr : BitVec 64)
    (halign : addr &&& 3 = 0)
    (hbytes_base : MemBytesPresentAt s (addr &&& (-8 : BitVec 64)) 8)
    (h_no_ovf_base : (addr &&& (-8 : BitVec 64)).toNat + 7 < 2 ^ 64)
    (hbytes_addr : MemBytesPresentAt s addr 4)
    (h_no_ovf_addr : addr.toNat + 3 < 2 ^ 64) :
    (let dword     := loaded_dword_at s (addr &&& (-8 : BitVec 64))
        hbytes_base h_no_ovf_base
     let xor_addr  := addr ^^^ (4 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6   := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted   := shift_bits_left dword shift_6
     shift_bits_right shifted (32 : BitVec 6))
    = zero_extend (m := 64) (loaded_word_at s addr hbytes_addr h_no_ovf_addr) := by
  simp only [sll_srli_extracts_word _ _ halign,
    ← loaded_word_in_dword s addr halign hbytes_base h_no_ovf_base
      hbytes_addr h_no_ovf_addr]

/-- Sail-side `execute_LOAD … true 4` reduces to `stateAfterWrite rd
    (zero_extend (loaded_word_at ea))`. -/
theorem execute_LWU_reduces (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (haligned : AlignedAccess (load_effective_address val imm) 4)
    (hbytes : MemBytesPresentAt js.sail (load_effective_address val imm) 4)
    (hload_pmp : Assumptions.LoadPmpOk (load_effective_address val imm) 4 js.sail)
    (hread_mmio : Assumptions.NotReadableMmio (load_effective_address val imm) 4 js.sail)
    (h_no_ovf : (load_effective_address val imm).toNat + 3 < 2 ^ 64) :
    (execute_LOAD imm rs1 rd true 4).run js.sail =
    .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd
        (zero_extend (m := 64)
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
  simp only [extend_value, if_true, EStateM.bind, EStateM.pure]
  obtain ⟨s', hw⟩ := wX_shape rd
    (zero_extend (m := 64)
      (loaded_word_at js.sail (load_effective_address val imm) hbytes h_no_ovf))
    js.sail
  rw [hw]
  simp only [RETIRE_SUCCESS]
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

/-- Sail-side misaligned. -/
theorem execute_LWU_misaligned (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_align : load_effective_address val imm &&& 3 ≠ 0)
    :
    (execute_LOAD imm rs1 rd true 4).run js.sail =
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

/-!
## Program-level LWU theorem

The Jolt side is the structured `JoltISA.lwuProgram`. The proof is Ari's
three-block decomposition:

* `assertSetupBlockAligned` handles the alignment assertion and dword load;
* `xoriSlliSllBlock` handles the lane-to-top virtual-register work; and
* `srliWriteBlock` performs the unsigned real-register writeback.
-/

/-- Program-level aligned execution for LWU.

The key point is that all monadic plumbing is discharged by reusable
program-block lemmas.  The only LWU-specific step left in this theorem is the
pure bridge `jolt_lwu_bridge`, which identifies the bytecode extraction value
with Sail's direct unsigned word load. -/
theorem lwuProgram_concrete_aligned (imm : BitVec 12) (rs1 rd : regidx)
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
      (JoltISA.execProgram (JoltISA.lwuProgram imm rs1 rd)).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (zero_extend (m := 64)
          (loaded_word_at js.sail (load_effective_address val imm)
            hbytes_word h_word_no_ovf)) := by
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
    .instr (.VirtualSRLI dst (.vreg v1) (JoltISA.srliBitmask (32 : BitVec 6)))
      (.done RETIRE_SUCCESS)
  let logicTail : JoltISA.Program :=
    .instr (.XORI (.vreg v0) (.vreg v0) (4 : BitVec 12)) <|
    JoltISA.slliBlock (.vreg v0) (.vreg v0) (3 : BitVec 6) <|
    JoltISA.sllBlock (.vreg v1) (.vreg v1) (.vreg v0) tmp writeTail
  rcases LoadProgramBlocks.assertWordSetupBlockAligned logicTail
      v0 v1 imm rs1 js hpriv hmprv val hrx halign hbytes_base hload_pmp_base
      hread_mmio_base hv0 hv1 hv0_ne_v1 with
    ⟨js_load, hload_run, hload_sail, hload_v0, hload_v1⟩
  let dword := loaded_dword_at js.sail (compute_aligned_dword_base_address val imm)
    hbytes_base (aligned_dword_addr_is_aligned_dword_access val imm).no_ovf
  rcases LoadProgramBlocks.xoriSlliSllBlock writeTail v0 v1 tmp imm (4 : BitVec 12)
      js js_load val dword hload_sail hload_v0 hload_v1 hv0 hv1 htmp
      hv0_ne_v1 hv0_ne_tmp hv1_ne_tmp with
    ⟨js_shift, hlogic_run, hshift_sail, _hshift_v0, hshift_v1⟩
  let shiftedValue :=
    shift_bits_left
      dword
      (Sail.BitVec.extractLsb
        (shift_bits_left
          (load_effective_address val imm ^^^ sign_extend (m := 64) (4 : BitVec 12))
          (3 : BitVec 6)) 5 0)
  have hshifted : js_shift.vregs v1 = shiftedValue := by
    simpa [shiftedValue] using hshift_v1
  rcases LoadProgramBlocks.srliWriteBlock (.done RETIRE_SUCCESS)
      rd v1 (32 : BitVec 6) js js_shift shiftedValue hshift_sail hshifted with
    ⟨js', hwrite_run, hwrite_sail⟩
  refine ⟨js', ?_, ?_⟩
  · unfold JoltISA.lwuProgram
    change (JoltISA.execProgram
      (.instr (.VirtualAssertWordAlignment rs1 imm (ExceptionType.E_Load_Addr_Align ())) <|
       .instr (.ADDI (.vreg v0) (.xreg rs1) imm) <|
       .instr (.ANDI (.vreg v1) (.vreg v0) (-8 : BitVec 12)) <|
       .instr (.LD .normal (.vreg v1) (.vreg v1) 0) logicTail)).run js = .ok RETIRE_SUCCESS js'
    rw [hload_run, hlogic_run, hwrite_run]
    rfl
  · rw [hwrite_sail]
    exact congrArg (stateAfterWrite js.sail rd) (by
      have h4 : sign_extend (m := 64) (4 : BitVec 12) = (4 : BitVec 64) := by decide
      simpa [shiftedValue, compute_aligned_dword_base_address, h4] using
        (jolt_lwu_bridge js.sail (load_effective_address val imm) halign
          (by simpa [compute_aligned_dword_base_address] using hbytes_base)
          (by
            simpa [compute_aligned_dword_base_address] using
              (aligned_dword_addr_is_aligned_dword_access val imm).no_ovf)
          hbytes_word h_word_no_ovf))

/-- Program-level misaligned execution for LWU.

The leading word alignment assertion returns the load-address-alignment exception and
the structured interpreter does not execute the dword load or writeback tail. -/
theorem lwuProgram_concrete_misaligned (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_align : load_effective_address val imm &&& 3 ≠ 0) :
    (JoltISA.execProgram (JoltISA.lwuProgram imm rs1 rd)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (load_effective_address val imm), ExceptionType.E_Load_Addr_Align ())) js := by
  let e :=
    (Virtaddr (load_effective_address val imm), ExceptionType.E_Load_Addr_Align ())
  let v0 := JoltISA.loadV0For rd
  let v1 := JoltISA.loadV1For rd
  let tmp := JoltISA.loadInlineTmpFor rd
  let dst := JoltISA.loadDstFor rd
  unfold JoltISA.lwuProgram
  simpa [e] using
    (LoadProgramBlocks.assertWordBlockMisaligned
      (.instr (.ADDI (.vreg v0) (.xreg rs1) imm) <|
       .instr (.ANDI (.vreg v1) (.vreg v0) (-8 : BitVec 12)) <|
       .instr (.LD .normal (.vreg v1) (.vreg v1) 0) <|
       .instr (.XORI (.vreg v0) (.vreg v0) (4 : BitVec 12)) <|
       JoltISA.slliBlock (.vreg v0) (.vreg v0) (3 : BitVec 6) <|
       JoltISA.sllBlock (.vreg v1) (.vreg v1) (.vreg v0) tmp <|
       .instr (.VirtualSRLI dst (.vreg v1) (JoltISA.srliBitmask (32 : BitVec 6))) <|
       .done RETIRE_SUCCESS)
      imm rs1 js val hrx h_align)

/-- Aligned public program theorem for LWU. -/
theorem lwuProgram_eq_sail_aligned (imm : BitVec 12)
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
    (hbytes_word : MemBytesPresentAt js.sail (load_effective_address val imm) 4)
    (hload_pmp_word : Assumptions.LoadPmpOk (load_effective_address val imm) 4 js.sail)
    (hread_mmio_word :
      Assumptions.NotReadableMmio (load_effective_address val imm) 4 js.sail)
    (h_word_no_ovf : (load_effective_address val imm).toNat + 3 < 2 ^ 64)
    (h_align : load_effective_address val imm &&& 3 = 0) :
    projectResult ((JoltISA.execProgram (JoltISA.lwuProgram imm rs1 rd)).run js) =
    (execute_LOAD imm rs1 rd true 4).run js.sail := by
  let ea := load_effective_address val imm
  have haligned : AlignedAccess (load_effective_address val imm) 4 := by
    refine
      { misalign := ?_
        split := ?_ }
    · simpa [ea] using access_misaligned_4_aligned_false ea h_align
    · simpa [ea] using split_misaligned_aligned_4 ea h_align
  rcases lwuProgram_concrete_aligned imm rs1 rd js hpriv hmprv val hrx h_align
      hbytes_base hload_pmp_base hread_mmio_base hbytes_word h_word_no_ovf with
    ⟨js', hjolt, hjolt_sail⟩
  have hsail := execute_LWU_reduces imm rs1 rd js hpriv hmprv val hrx haligned
    hbytes_word hload_pmp_word hread_mmio_word h_word_no_ovf
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail, hsail]

/-- Misaligned public program theorem for LWU. -/
theorem lwuProgram_eq_sail_misaligned (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_align : load_effective_address val imm &&& 3 ≠ 0) :
    projectResult ((JoltISA.execProgram (JoltISA.lwuProgram imm rs1 rd)).run js) =
    (execute_LOAD imm rs1 rd true 4).run js.sail := by
  let ea := load_effective_address val imm
  have hjolt :
      (JoltISA.execProgram (JoltISA.lwuProgram imm rs1 rd)).run js =
        .ok (ExecutionResult.Memory_Exception
          (Virtaddr ea, ExceptionType.E_Load_Addr_Align ())) js := by
    simpa [ea] using lwuProgram_concrete_misaligned imm rs1 rd js val hrx h_align
  have hsail :
      (execute_LOAD imm rs1 rd true 4).run js.sail =
        .ok (ExecutionResult.Memory_Exception
          (Virtaddr ea, ExceptionType.E_Load_Addr_Align ())) js.sail := by
    simpa [ea] using
      (execute_LWU_misaligned imm rs1 rd js val hrx h_align)
  rw [hjolt]
  simp only [projectResult, project]
  symm
  exact hsail

/-- Successful `LWU` expansions do not modify the persistent CSR virtual
registers materialized by `systemProject`. -/
theorem lwuProgram_preserves_projected_vregs
    (imm : BitVec 12) (rs1 rd : regidx)
    {js js' : SailJoltState} {result : ExecutionResult}
    (hrun : (JoltISA.execProgram (JoltISA.lwuProgram imm rs1 rd)).run js =
      .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe : JoltISA.ProgramWritesNoProtectedVReg
      (JoltISA.lwuProgram imm rs1 rd) := by
    unfold JoltISA.lwuProgram JoltISA.slliBlock JoltISA.sllBlock
    simp [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg]
  exact Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    hsafe hrun

/-- **Main program theorem for LWU.**  The structured Jolt-ISA expansion
matches Sail after materializing Jolt's persistent CSR virtual registers. -/
def lwuProgramEqSailStatement (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (_h : LoadProgramEqSailAssumptions imm rs1 js) : Prop :=
    System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.lwuProgramAuto rd rs1 imm)).run js) =
    (execute_LOAD imm rs1 rd true 4).run js.sail

/-- **Main program theorem for LWU.**  The structured Jolt-ISA expansion
matches Sail after materializing Jolt's persistent CSR virtual registers. -/
theorem lwuProgram_eq_sail (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    lwuProgramEqSailStatement imm rs1 rd js h := by
  sorry

end LWU_main
