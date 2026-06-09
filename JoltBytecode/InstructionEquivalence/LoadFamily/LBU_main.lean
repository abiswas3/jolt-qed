import JoltBytecode.JoltISA.Environment
import JoltBytecode.JoltISA.Expansions.Load
import JoltBytecode.InstructionEquivalence.Memory.Utils
import JoltBytecode.InstructionEquivalence.LoadDefUtils
import JoltBytecode.InstructionEquivalence.LoadFamily.PhaseHelpers
import JoltBytecode.InstructionEquivalence.LoadFamily.DwordArithmetic
import JoltBytecode.InstructionEquivalence.LoadFamily.ProgramBlocks
import JoltBytecode.InstructionEquivalence.ProofSupport
import Mathlib.Tactic.IntervalCases

set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace LBU_main

/-!
# LBU: Jolt load-byte (unsigned) top-level equivalence

From `tracer/src/instruction/lbu.rs::inline_sequence_64`:

    ADDI  v0, rs1, imm
    ANDI  v1, v0, -8
    LD    v1, v1, 0
    XORI  v0, v0, 7
    SLLI  v0, v0, 3
    SLL   v1, v1, v0
    SRLI  rd, v1, 56

This is identical to `LB` (see `LB_main.lean`) except the final step is
`SRLI` (logical right shift) instead of `SRAI` (arithmetic right shift).
Logical shift zero-fills the upper 56 bits; arithmetic shift replicates the
sign bit. Accordingly:

* The write phase uses `shift_bits_right` in place of
  `shift_bits_right_arith`.
* The bridge's RHS and the final `rd` value use `zero_extend` in place of
  `sign_extend`.
* `execute_LOAD`'s signed/unsigned flag is `true` (unsigned) instead of
  `false`.

## What lives here (by role)

* `jolt_lbu_bridge` — specialisation: Jolt's logic-phase expression equals
  `zero_extend (loaded_byte_at …)`.
* `lbuProgram_concrete` — the program-level Jolt execution fact.
* `execute_LBU_reduces` — the Sail-side `execute_LOAD … true 1` reduction.
* `lbuProgram_eq_sail` — the main equivalence theorem.
-/

/-- **Bridge lemma for LBU.** The Jolt logic-phase computation (XOR with 7,
    SLL by 3, SLL the dword, logical-shift-right by 56) equals the
    Sail-side direct byte load zero-extended to 64 bits. Pure bit-vector
    algebra — combines `sll_srli_extracts_byte` with
    `loaded_byte_in_dword`, mirroring `jolt_lb_bridge` modulo
    sign→zero-extend. -/
theorem jolt_lbu_bridge (s : SailState) (addr : BitVec 64) :
    (let dword     := loaded_dword_at s (addr &&& (-8 : BitVec 64))
     let xor_addr  := addr ^^^ (7 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6   := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted   := shift_bits_left dword shift_6
     shift_bits_right shifted (56 : BitVec 6))
    = zero_extend (m := 64) (loaded_byte_at s addr) := by
  simp only [sll_srli_extracts_byte, ← loaded_byte_in_dword]

-- ============================================================================
-- Top-level LBU ↔ Sail equivalence theorems
-- ============================================================================

/-- Sail-side `execute_LOAD imm rs1 rd true 1` reduces to
    `stateAfterWrite rd (zero_extend (loaded_byte_at ea))`. The `true`
    flag selects the unsigned branch in Sail's `extend_value`.

    Structurally identical to `execute_LB_reduces` in `LB_main.lean`; the
    only differences from the LB version are marked `-- DIFF:` below. -/
theorem execute_LBU_reduces (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (hload : LoadReadAssumptions (load_effective_address val imm) 1 js.sail) :
    -- DIFF: `execute_LOAD` is called with `true` (unsigned) not `false`.
    (execute_LOAD imm rs1 rd true 1).run js.sail =
    .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd
        -- DIFF: `zero_extend` not `sign_extend`.
        (zero_extend (m := 64)
          (loaded_byte_at js.sail (load_effective_address val imm)))) := by
  unfold execute_LOAD
  simp only [bind, pure]
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  simp (config := { decide := true }) only []
  simp (config := { decide := true }) only [PreSail.assert, EStateM.bind, pure, EStateM.pure,
       EStateM.run, if_true]
  rw [vmem_read_byte_reduces imm rs1 js.sail hcfg val hrx hload.aligned
      (mem_read_1_eq_loaded_byte _ js.sail hcfg hload.phys)]
  -- DIFF: `if_true` instead of `Bool.false_eq_true, if_false` — the unsigned
  --       branch in `extend_value` is gated on the `true` signed flag, so the
  --       opposite branch fires compared to LB.
  simp only [extend_value, if_true, EStateM.bind, EStateM.pure]
  obtain ⟨s', hw⟩ := wX_shape rd
    -- DIFF: `zero_extend` not `sign_extend`, as in the goal.
    (zero_extend (m := 64) (loaded_byte_at js.sail (load_effective_address val imm)))
    js.sail
  rw [hw]
  simp only [RETIRE_SUCCESS]
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

/-!
## Program-level LBU theorem

The Jolt side is now the structured `JoltISA.lbuProgram`.  This is identical
to the program-level `LB` proof except for the final unsigned `SRLI` writeback
and the pure bridge theorem's `zero_extend` result.
-/

/-- Program-level execution for LBU.

The common setup and lane-positioning facts are shared with `LB`; the final
write block is the logical-right-shift version, which zero-fills the result
before writing the architectural destination. -/
theorem lbuProgram_concrete (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail) :
    ∃ js' : SailJoltState,
      (JoltISA.execProgram (JoltISA.lbuProgram imm rs1 rd)).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (zero_extend (m := 64)
          (loaded_byte_at js.sail (load_effective_address val imm))) := by
  let writeTail : JoltISA.Program :=
    .instr (.VirtualSRLI (.xreg rd) (.vreg JoltISA.inlineTmp1) (JoltISA.srliBitmask (56 : BitVec 6)))
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
  rcases LoadProgramBlocks.srliWriteBlock (.done RETIRE_SUCCESS)
      rd (56 : BitVec 6) js js_shift shiftedValue hshift_sail hshifted with
    ⟨js', hwrite_run, hwrite_sail⟩
  refine ⟨js', ?_, ?_⟩
  · unfold JoltISA.lbuProgram
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
        (jolt_lbu_bridge js.sail (load_effective_address val imm)))

/-- **Main program theorem for LBU.**  The structured Jolt-ISA expansion
`lbuProgram`, interpreted by `execProgram`, agrees with Sail's unsigned
byte-load execution. -/
theorem lbuProgram_eq_sail (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail)
    (hphys : FlatPhysMem (load_effective_address val imm) 1 js.sail) :
    projectResult ((JoltISA.execProgram (JoltISA.lbuProgram imm rs1 rd)).run js) =
    (execute_LOAD imm rs1 rd true 1).run js.sail := by
  have hload : LoadReadAssumptions (load_effective_address val imm) 1 js.sail :=
    loadReadAssumptions_of_aligned_phys
      (load_effective_address val imm) 1 js.sail
      (aligned_access_1 (load_effective_address val imm)) hphys
  rcases lbuProgram_concrete imm rs1 rd js hcfg val hrx
      h_dword_phys with
    ⟨js', hjolt, hjolt_sail⟩
  have hsail := execute_LBU_reduces imm rs1 rd js hcfg val hrx hload
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail, hsail]

end LBU_main
