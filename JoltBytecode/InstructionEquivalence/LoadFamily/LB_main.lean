import JoltBytecode.JoltISA.Environment
import JoltBytecode.JoltISA.Expansions.Load
import JoltBytecode.InstructionEquivalence.Memory.Utils
import JoltBytecode.InstructionEquivalence.LoadDefUtils
import JoltBytecode.InstructionEquivalence.LoadFamily.PhaseHelpers
import JoltBytecode.InstructionEquivalence.LoadFamily.DwordArithmetic
import JoltBytecode.InstructionEquivalence.LoadFamily.Derived
import JoltBytecode.InstructionEquivalence.LoadFamily.ProgramBlocks
import JoltBytecode.InstructionEquivalence.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport
import Mathlib.Tactic.IntervalCases

set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace LB_main

/-!
# LB: Jolt load-byte (signed) top-level equivalence

From `tracer/src/instruction/lb.rs::inline_sequence_64`:

    ADDI  v0, rs1, imm         -- real rs1 → virtual v0
    ANDI  v1, v0, -8           -- virtual → virtual
    LD    v1, v1, 0            -- virtual → virtual (memory load)
    XORI  v0, v0, 7            -- virtual → virtual
    SLLI  v0, v0, 3            -- virtual → virtual
    SLL   v1, v1, v0           -- virtual → virtual
    SRAI  rd, v1, 56           -- virtual v1 → real rd (arith-shift + sign-extend)

This file proves equivalence for the structured `JoltISA.lbProgram`. Unlike
LW, byte loads have no alignment failure case, so there is no
aligned/misaligned split.

## What lives here (by role)

* `jolt_lb_bridge` — specialisation of `sll_srai_extracts_byte` and
  `loaded_byte_in_dword` from `DwordArithmetic` to LB's shape: Jolt's
  logic-phase expression equals `sign_extend (loaded_byte_at …)`.
* `lbProgram_concrete` — the program-level Jolt execution fact.
* `execute_LB_reduces` — the Sail-side `execute_LOAD` reduction.
* `lbProgram_eq_sail` — the main equivalence theorem.

Shared pure bit-vector, memory-shape, and phase-composition helpers live
in `DwordArithmetic.lean`, `LoadDefUtils.lean`, and `PhaseHelpers.lean`.
-/

/-- **Bridge lemma for LB.** The Jolt logic-phase computation (XOR with 7,
    SLL by 3, SLL the dword, arith-shift-right by 56) equals the Sail-side
    direct byte load sign-extended to 64 bits. Pure bit-vector algebra —
    just combines `sll_srai_extracts_byte` with `loaded_byte_in_dword`. -/
theorem jolt_lb_bridge (s : SailState) (addr : BitVec 64) :
    (let dword     := loaded_dword_at s (addr &&& (-8 : BitVec 64))
     let xor_addr  := addr ^^^ (7 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6   := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted   := shift_bits_left dword shift_6
     shift_bits_right_arith shifted (56 : BitVec 6))
    = sign_extend (m := 64) (loaded_byte_at s addr) := by
  simp only [sll_srai_extracts_byte, ← loaded_byte_in_dword]

-- ============================================================================
-- Top-level LB ↔ Sail equivalence theorems
-- ============================================================================

/-- Sail-side `execute_LOAD imm rs1 rd false 1` reduces to
    `stateAfterWrite rd (sign_extend (loaded_byte_at ea))` under the
    `LoadReadEvidence` bundle for size 1. No `h_no_ovf` needed —
    single-byte reads cannot overflow the 64-bit address space. -/
theorem execute_LB_reduces (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (hphys : FlatPhysMem (load_effective_address val imm) 1 js.sail) :
    (execute_LOAD imm rs1 rd false 1).run js.sail =
    .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (loaded_byte_at js.sail (load_effective_address val imm)))) := by
  have hload : LoadReadEvidence (load_effective_address val imm) 1 js.sail :=
    loadReadEvidence_of_aligned_phys
      (load_effective_address val imm) 1 js.sail
      (aligned_access_1 (load_effective_address val imm)) hphys
  unfold execute_LOAD
  simp only [bind, pure]
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  simp (config := { decide := true }) only []
  simp (config := { decide := true }) only [PreSail.assert, EStateM.bind, pure, EStateM.pure,
       EStateM.run, if_true]
  rw [vmem_read_byte_reduces imm rs1 js.sail hcfg val hrx hload.aligned
      (mem_read_1_eq_loaded_byte _ js.sail hcfg hload.phys)]
  simp only [extend_value, Bool.false_eq_true, if_false, EStateM.bind, EStateM.pure]
  obtain ⟨s', hw⟩ := wX_shape rd
    (sign_extend (m := 64) (loaded_byte_at js.sail (load_effective_address val imm)))
    js.sail
  rw [hw]
  simp only [RETIRE_SUCCESS]
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

/-!
## Program-level LB theorem

The Jolt side is the structured `JoltISA.lbProgram`, so the proof follows the
generated instruction sequence directly.
-/

/-- Program-level execution for LB.

Byte loads have no alignment assertion.  The proof therefore composes exactly
three reusable blocks: common dword setup, common `XORI/SLLI/SLL` lane
positioning, and signed `SRAI` writeback.  The only LB-specific ingredient is
`jolt_lb_bridge`, the pure bit-vector fact connecting that shifted dword to
Sail's direct byte load. -/
theorem lbProgram_concrete (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail) :
    ∃ js' : SailJoltState,
      (JoltISA.execProgram (JoltISA.lbProgram imm rs1 rd)).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (loaded_byte_at js.sail (load_effective_address val imm))) := by
  let writeTail : JoltISA.Program :=
    .instr (.VirtualSRAI (.xreg rd) (.vreg JoltISA.inlineTmp1) (JoltISA.sraiBitmask (56 : BitVec 6)))
      (.done RETIRE_SUCCESS)
  let logicTail : JoltISA.Program :=
    .instr (.XORI (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp0) (7 : BitVec 12)) <|
    JoltISA.slliBlock (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp0) (3 : BitVec 6) <|
    JoltISA.sllBlock (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp0) JoltISA.inlineTmp2 writeTail
  rcases LoadProgramBlocks.setupBlock logicTail imm rs1 js hcfg val hrx
      h_dword_phys with
    ⟨js_load, hload_run, hload_sail, hload_v0, hload_v1⟩
  rcases LoadProgramBlocks.xoriSlliSllBlock writeTail imm (7 : BitVec 12)
      js js_load val hload_sail hload_v0 hload_v1 with
    ⟨js_shift, hlogic_run, hshift_sail, _hshift_v0, hshift_v1⟩
  let shiftedValue :=
    shift_bits_left
      (loaded_dword_at js.sail (compute_aligned_dword_base_address val imm))
      (Sail.BitVec.extractLsb
        (shift_bits_left
          (load_effective_address val imm ^^^ sign_extend (m := 64) (7 : BitVec 12))
          (3 : BitVec 6)) 5 0)
  have hshifted : js_shift.vregs JoltISA.inlineTmp1 = shiftedValue := by
    simpa [shiftedValue] using hshift_v1
  rcases LoadProgramBlocks.sraiWriteBlock (.done RETIRE_SUCCESS)
      rd (56 : BitVec 6) js js_shift shiftedValue hshift_sail hshifted with
    ⟨js', hwrite_run, hwrite_sail⟩
  refine ⟨js', ?_, ?_⟩
  · unfold JoltISA.lbProgram
    change (JoltISA.execProgram
      (.instr (.ADDI (.vreg JoltISA.inlineTmp0) (.xreg rs1) imm) <|
       .instr (.ANDI (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp0) (-8 : BitVec 12)) <|
       .instr (.LD (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp1) 0) logicTail)).run js = .ok RETIRE_SUCCESS js'
    rw [hload_run, hlogic_run, hwrite_run]
    rfl
  · rw [hwrite_sail]
    exact congrArg (stateAfterWrite js.sail rd) (by
      have h7 : sign_extend (m := 64) (7 : BitVec 12) = (7 : BitVec 64) := by decide
      simpa [shiftedValue, compute_aligned_dword_base_address, h7] using
        (jolt_lb_bridge js.sail (load_effective_address val imm)))

/-- Successful `LB` expansions do not modify the persistent CSR virtual
registers materialized by `systemProject`. -/
theorem lbProgram_preserves_projected_vregs
    (imm : BitVec 12) (rs1 rd : regidx)
    {js js' : SailJoltState} {result : ExecutionResult}
    (hrun : (JoltISA.execProgram (JoltISA.lbProgram imm rs1 rd)).run js =
      .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe : JoltISA.ProgramWritesNoProtectedVReg
      (JoltISA.lbProgram imm rs1 rd) := by
    unfold JoltISA.lbProgram JoltISA.slliBlock JoltISA.sllBlock
    simp [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg,
      JoltISA.DstWritesNoProtectedVReg,
      JoltISA.loadV0, JoltISA.loadV1, JoltISA.loadInlineTmp]
  exact Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    hsafe hrun

/-- **Main program theorem for LB.**  The structured Jolt-ISA expansion
matches Sail after materializing Jolt's persistent CSR virtual registers. -/
def lbProgramEqSailStatement (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (_h : LoadFamily.LoadProgramEqSailAssumptions imm rs1 js) : Prop :=
    System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.lbProgram imm rs1 rd)).run js) =
    (execute_LOAD imm rs1 rd false 1).run js.sail

/-- **Main program theorem for LB.**  The structured Jolt-ISA expansion
matches Sail after materializing Jolt's persistent CSR virtual registers. -/
theorem lbProgram_eq_sail (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (h : LoadFamily.LoadProgramEqSailAssumptions imm rs1 js) :
    lbProgramEqSailStatement imm rs1 rd js h := by
  unfold lbProgramEqSailStatement
  rcases lbProgram_concrete imm rs1 rd js h.cfg h.rs1_val h.rs1_read
      h.dwordPhys with
    ⟨js', hjolt, hjolt_sail⟩
  have hsail := execute_LB_reduces imm rs1 rd js h.cfg h.rs1_val
    h.rs1_read h.bytePhys
  have h_project_initial : System.systemProject js = js.sail :=
    Projection.systemProject_eq_sail_of_compatible js h.linkedCSRs
  have h_projected_vregs : Projection.ProjectedVRegsPreserved js js' :=
    lbProgram_preserves_projected_vregs imm rs1 rd hjolt
  rw [hjolt, hsail]
  simp only [System.systemProjectResult]
  congr 1
  rw [Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved
    js js' rd
    (sign_extend (m := 64)
      (loaded_byte_at js.sail (load_effective_address h.rs1_val imm)))
    hjolt_sail h_projected_vregs]
  rw [h_project_initial]

end LB_main
