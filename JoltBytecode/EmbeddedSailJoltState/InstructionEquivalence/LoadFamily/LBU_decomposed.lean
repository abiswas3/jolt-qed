import JoltBytecode.EmbeddedSailJoltState.Defs
import JoltBytecode.EmbeddedSailJoltState.MemoryUtils
import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadDefUtils
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadFamily.PhaseHelpers
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadFamily.LB_decomposed
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
# LBU: Decomposed-form lemmas

LBU shares **every** bytecode step with LB except the final write: LBU uses
`SRLI` (logical right shift — zero-fill) where LB uses `SRAI` (arithmetic
right shift — sign-fill). Accordingly, this file reuses the LB load and
logic phases verbatim and only defines its own write phase + downstream
decomposed lemmas.

## What lives here (by role)

* **Reused from `LB_decomposed`** (no redefinition):
  * `LB_main.jolt_lb_load_phase` — the shared `writeVReg 0 ea;
    vreg_ANDI 1 0 -8; vreg_LD 1 1 0` sequence.
  * `LB_main.jolt_lb_logic_phase` — the shared `XORI; SLLI; SLL; readVReg 1`
    sequence.
  * `LB_main.jolt_lb_logic_phase_concrete` — the run+value package for the
    logic phase. LBU calls this directly in its decomposed-writes proof.

* **LBU-specific (defined here):**
  * `jolt_lbu_write_phase` — `wX_bits rd (shift_bits_right v1 56)`. The only
    per-instruction difference from LB.
  * `jolt_lbu_decomposed` — LB's load+logic phases composed with LBU's
    write phase.
  * `jolt_lbu_write_phase_concrete` — the write phase writes
    `shift_bits_right logic_val 56` to `rd`.
  * `jolt_lbu_decomposed_from_phase_runs` — three-phase composition.
  * `jolt_lbu_decomposed_writes_logic_value` — top-level decomposed fact.

The original program `jolt_lbu`, the bridge lemma `jolt_lbu_bridge`, and the
top-level equivalence theorem live in `LBU_main.lean`, which imports this
file.
-/

-- ============================================================================
-- Phase definitions (reusing LB)
-- ============================================================================
-- Load and logic phases are reused directly from `LB_main` — no aliasing,
-- no redefinition. See `LB_decomposed.lean` for their definitions and the
-- concrete lemmas about them.

/-- LBU write phase: `wX_bits rd (shift_bits_right v1 56)`. The SRLI zero-
    fills the upper 56 bits, giving the zero-extended byte. This is the
    **only** monadic difference from LB — `jolt_lb_write_phase` uses
    `shift_bits_right_arith` in the same slot. -/
def jolt_lbu_write_phase (rd : regidx) (v1 : BitVec 64) : JoltMonad ExecutionResult := do
  liftSail (wX_bits rd (shift_bits_right v1 (56 : BitVec 6)))
  pure RETIRE_SUCCESS

/-- The decomposed LBU program: read rs1, form `ea`, run LB's load phase,
    run LB's logic phase, then run LBU's write phase. -/
def jolt_lbu_decomposed (imm : BitVec 12) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let base ← liftSail (rX_bits rs1)
  let ea := base + sign_extend (m := 64) imm
  match ← LB_main.jolt_lb_load_phase ea with
  | .Retire_Success () =>
      let v1 ← LB_main.jolt_lb_logic_phase
      jolt_lbu_write_phase rd v1
  | other => pure other

-- ============================================================================
-- Write-phase lemma (LBU-specific)
-- ============================================================================

/-- The LBU write phase takes `logic_val` and writes
    `shift_bits_right logic_val 56` to `rd`, leaving vregs and all other
    memory untouched. Structurally identical to
    `LB_main.jolt_lb_write_phase_concrete`, just with `shift_bits_right`
    instead of `shift_bits_right_arith`. -/
theorem jolt_lbu_write_phase_concrete (rd : regidx) (js : SailJoltState)
    (js_logic : SailJoltState) (logic_val : BitVec 64)
    (hlogic_sail : js_logic.sail = js.sail) :
    ∃ js',
      (jolt_lbu_write_phase rd logic_val).run js_logic = .ok RETIRE_SUCCESS js' ∧
      js'.sail =
        stateAfterWrite js.sail rd (shift_bits_right logic_val (56 : BitVec 6)) := by
  unfold jolt_lbu_write_phase
  obtain ⟨s', hw⟩ := wX_shape rd (shift_bits_right logic_val (56 : BitVec 6)) js.sail
  let js' : SailJoltState := { sail := s', vregs := js_logic.vregs }
  refine ⟨js', ?_, ?_⟩
  · simp only [liftSail, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
    rw [hlogic_sail, hw]
  · exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

-- ============================================================================
-- Three-phase composition + top-level decomposed fact
-- ============================================================================

/-- If LB's load and logic phases plus LBU's write phase all run
    successfully in sequence, then `jolt_lbu_decomposed` itself runs
    successfully with the same final state. Pure threading lemma —
    structurally identical to `LB_main.jolt_lb_decomposed_from_phase_runs`,
    just with `jolt_lbu_write_phase` in place of `jolt_lb_write_phase`. -/
theorem jolt_lbu_decomposed_from_phase_runs (imm : BitVec 12) (rs1 rd : regidx)
    (js js_load js_logic js' : SailJoltState)
    (val logic_val : BitVec 64)
    (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (hload_run :
      (LB_main.jolt_lb_load_phase (load_effective_address val imm)).run js = .ok RETIRE_SUCCESS js_load)
    (hlogic_run :
      (LB_main.jolt_lb_logic_phase).run js_load = .ok logic_val js_logic)
    (hwrite_run :
      (jolt_lbu_write_phase rd logic_val).run js_logic = .ok RETIRE_SUCCESS js') :
    (jolt_lbu_decomposed imm rs1 rd).run js = .ok RETIRE_SUCCESS js' := by
  have hload_run' :
      LB_main.jolt_lb_load_phase (val + sign_extend (m := 64) imm) js = .ok RETIRE_SUCCESS js_load := by
    simpa [load_effective_address, EStateM.run] using hload_run
  have hlogic_run' :
      LB_main.jolt_lb_logic_phase js_load = .ok logic_val js_logic := by
    simpa [EStateM.run] using hlogic_run
  have hwrite_run' :
      jolt_lbu_write_phase rd logic_val js_logic = .ok RETIRE_SUCCESS js' := by
    simpa [EStateM.run] using hwrite_run
  unfold jolt_lbu_decomposed
  simp only [liftSail, bind, EStateM.bind, pure, EStateM.run]
  rw [hrx]
  simp only []
  rw [hload_run']
  change (EStateM.bind LB_main.jolt_lb_logic_phase (fun v1 => jolt_lbu_write_phase rd v1)) js_load =
    .ok RETIRE_SUCCESS js'
  simp only [EStateM.bind]
  rw [hlogic_run']
  simpa using hwrite_run'

/-- Under the standing Jolt + dword-load assumptions, the decomposed LBU
    program
      1. succeeds with some final state `js'`,
      2. its logic phase returns the same `logic_val` shape as LB (since
         LBU reuses LB's logic phase), and
      3. `rd` holds `shift_bits_right logic_val 56` (zero-extended byte).
    Differs from `LB_main.jolt_lb_decomposed_writes_logic_value` only in
    the third component: `shift_bits_right` instead of
    `shift_bits_right_arith`.

    Top-level fact for the decomposed file; consumed by `jolt_lbu_concrete`
    in `LBU_main.lean`. -/
theorem jolt_lbu_decomposed_writes_logic_value (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (val : BitVec 64)
    (hrd : rd ≠ regidx.Regidx 0)
    (hcfg : JoltConfig js.sail)
    (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail) :
    ∃ js' logic_val,
      (jolt_lbu_decomposed imm rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      logic_val =
        shift_bits_left
          (loaded_dword_at js.sail (compute_aligned_dword_base_address val imm))
          (Sail.BitVec.extractLsb
            (shift_bits_left
              ((load_effective_address val imm) ^^^ (7 : BitVec 64))
              (3 : BitVec 6)) 5 0) ∧
      js'.sail =
        stateAfterWrite js.sail rd
          (shift_bits_right logic_val (56 : BitVec 6)) := by
  -- Setup + load phase: reuse LB's plumbing via `load_phase_setup_concrete_andi`
  -- and `vreg_LD_phase_from_setup_er`.
  rcases InstructionEquivalence.load_phase_setup_concrete_andi imm js val with
    ⟨js1, hsetup_run, hsetup_sail, hsetup_v0, hsetup_v1⟩
  have h_daddr_aligned : AlignedDwordAccess (compute_aligned_dword_base_address val imm) := by
    simpa [compute_aligned_dword_base_address, load_effective_address, aligned_dword_addr_eq] using
      (aligned_dword_addr_is_aligned_dword_access val imm)
  rcases InstructionEquivalence.vreg_LD_step_concrete js js1 (compute_aligned_dword_base_address val imm)
      hcfg hsetup_sail hsetup_v1 h_daddr_aligned h_dword_translate h_dword_phys with
    ⟨js_load, hld, hload_sail, hload_v0_raw, hload_v1⟩
  -- Assemble the LB load-phase run (which is the same monadic program as
  -- what LBU wants, since LBU reuses LB's load phase).
  have hload_run :
      (LB_main.jolt_lb_load_phase (load_effective_address val imm)).run js = .ok RETIRE_SUCCESS js_load := by
    simpa [LB_main.jolt_lb_load_phase, bind, EStateM.bind, EStateM.run] using
      (InstructionEquivalence.vreg_LD_phase_from_setup_er
        ((do
          writeVReg 0 (load_effective_address val imm)
          vreg_ANDI 1 0 (-8 : BitVec 12)) : JoltMonad ExecutionResult)
        js js1 js_load hsetup_run hld)
  have hload_v0 : js_load.vregs 0 = load_effective_address val imm := by
    rw [hload_v0_raw, hsetup_v0]
  -- Logic phase: reuse LB's concrete lemma verbatim.
  rcases LB_main.jolt_lb_logic_phase_concrete imm js js_load val hload_sail hload_v0 hload_v1 with
    ⟨js_logic, logic_val, hlogic_run, hlogic_v1, hlogic_val, hlogic_sail⟩
  -- Write phase: LBU-specific.
  rcases jolt_lbu_write_phase_concrete rd js js_logic logic_val hlogic_sail with
    ⟨js', hwrite_run, hwrite_sail⟩
  refine ⟨js', logic_val, ?_, hlogic_val, hwrite_sail⟩
  exact jolt_lbu_decomposed_from_phase_runs imm rs1 rd js js_load js_logic js' val logic_val
    hrx hload_run hlogic_run hwrite_run

end LBU_main
