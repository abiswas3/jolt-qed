import JoltBytecode.EmbeddedSailJoltState.Defs
import JoltBytecode.EmbeddedSailJoltState.MemoryUtils
import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadDefUtils
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadFamily.PhaseHelpers
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadFamily.DwordArithmetic
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadFamily.LB_decomposed
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadFamily.LBU_decomposed
import JoltBytecode.EmbeddedSailJoltState.RtypeW
import Mathlib.Tactic.IntervalCases

set_option maxHeartbeats 1_000_000_000
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

* `jolt_lbu` — the Jolt LBU program as a `JoltMonad ExecutionResult`.
* `jolt_lbu_bridge` — specialisation: Jolt's logic-phase expression equals
  `zero_extend (loaded_byte_at …)`.
* `jolt_lbu_concrete`, `execute_LBU_reduces`, `jolt_lbu_eq_sail` — the
  run-level Jolt fact, the Sail-side `execute_LOAD … true 1` reduction,
  and the main equivalence theorem combining the two.
-/

/-- The original Jolt LBU program. No alignment check — byte loads are
    always aligned. One Lean line per line of the tracer bytecode
    (`tracer/src/instruction/lbu.rs::inline_sequence_64`). Identical to
    `jolt_lb` except the final step uses `vreg_SRLI_to_real` (logical
    right shift, zero-fills) instead of `vreg_SRAI_to_real` (arithmetic
    right shift, sign-fills). -/
def jolt_lbu (imm : BitVec 12) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let _ ← vreg_ADDI_from_real 0 rs1 imm               -- ADDI v0, rs1, imm
  let _ ← vreg_ANDI 1 0 (-8 : BitVec 12)              -- ANDI v1, v0, -8
  match ← vreg_LD 1 1 0 with                           -- LD   v1, v1, 0
  | .Retire_Success () =>
      let _ ← vreg_XORI 0 0 7                          -- XORI v0, v0, 7
      let _ ← vreg_SLLI 0 0 3                          -- SLLI v0, v0, 3
      let _ ← vreg_SLL 1 1 0                           -- SLL  v1, v1, v0
      vreg_SRLI_to_real rd 1 (56 : BitVec 6)           -- SRLI rd, v1, 56
  | other => pure other

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

/-- `jolt_lbu` is just `jolt_lbu_decomposed` with the phase calls inlined.
    No alignment hypothesis required: byte loads have no alignment check.
    Structure mirrors `jolt_lb_run_eq_decomposed`, but the unfold list
    references LB's phase defs (reused by `jolt_lbu_decomposed`) plus
    LBU's own `jolt_lbu_write_phase`. -/
theorem jolt_lbu_run_eq_decomposed (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState) (val : BitVec 64)
    (hrx : rX_bits rs1 js.sail = .ok val js.sail) :
    (jolt_lbu imm rs1 rd).run js = (jolt_lbu_decomposed imm rs1 rd).run js := by
  unfold jolt_lbu jolt_lbu_decomposed vreg_ADDI_from_real vreg_SRLI_to_real
    LB_main.jolt_lb_load_phase LB_main.jolt_lb_logic_phase jolt_lbu_write_phase
  simp only [liftSail, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
  rw [hrx]
  rfl

/-- `jolt_lbu` succeeds and leaves `rd` holding
    `zero_extend (loaded_byte_at js.sail ea)`. Composes
    `jolt_lbu_decomposed_writes_logic_value` with `jolt_lbu_bridge` via
    `congrArg`, same pattern as `jolt_lb_concrete`. -/
theorem jolt_lbu_concrete (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail) :
    ∃ js' : SailJoltState,
      (jolt_lbu imm rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (zero_extend (m := 64)
          (loaded_byte_at js.sail (load_effective_address val imm))) := by
  have hrun_eq :
      (jolt_lbu imm rs1 rd).run js = (jolt_lbu_decomposed imm rs1 rd).run js := by
    simpa using jolt_lbu_run_eq_decomposed imm rs1 rd js val hrx
  rcases jolt_lbu_decomposed_writes_logic_value imm rs1 rd js val
      hrd hcfg hrx h_dword_translate h_dword_phys with
    ⟨js', logic_val, hdecomp_run, hlogic_val, hwrite_sail⟩
  refine ⟨js', ?_, ?_⟩
  · rw [hrun_eq]
    exact hdecomp_run
  · rw [hwrite_sail, hlogic_val]
    exact congrArg (stateAfterWrite js.sail rd)
      (jolt_lbu_bridge js.sail (load_effective_address val imm))

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
  rw [vmem_read_byte_reduces imm rs1 js.sail val hrx hload.aligned hload.translate
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

/-- **Main theorem.** Jolt LBU equals Sail LBU on every input. No
    aligned/misaligned case split — byte loads can't misalign. -/
theorem jolt_lbu_eq_sail (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail)
    (hload : LoadReadAssumptions (load_effective_address val imm) 1 js.sail) :
    projectResult ((jolt_lbu imm rs1 rd).run js) =
    (execute_LOAD imm rs1 rd true 1).run js.sail := by
  have hjolt :=
    jolt_lbu_concrete imm rs1 rd hrd js hcfg val hrx h_dword_translate h_dword_phys
  have hsail := execute_LBU_reduces imm rs1 rd js hcfg val hrx hload
  rcases hjolt with ⟨js', hjolt_run, hjolt_sail⟩
  rw [hjolt_run]
  simp only [projectResult, project]
  rw [hjolt_sail, hsail]

end LBU_main
