import JoltBytecode.EmbeddedSailJoltState.Defs
import JoltBytecode.EmbeddedSailJoltState.MemoryUtils
import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadDefUtils
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadFamily.PhaseHelpers
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadFamily.LB_decomposed
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadFamily.LH_decomposed
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

namespace LHU_main

/-!
# LHU: Decomposed-form lemmas

LHU shares every bytecode step with LH except the final write: LHU uses
`SRLI rd, v1, 48` (logical right shift — zero-fill) where LH uses
`SRAI rd, v1, 48` (arithmetic right shift — sign-fill).

## Reuse

* **Load phase** — reused from `LB_decomposed`
  (`LB_main.jolt_lb_load_phase`), identical bytecode across LB/LH/LBU/LHU.
* **Logic phase** — reused from `LH_decomposed`
  (`LH_main.jolt_lh_logic_phase`), identical XORI 6 / SLLI 3 / SLL pattern
  across LH and LHU.
* **Logic phase concrete lemma** — reused from `LH_decomposed`
  (`LH_main.jolt_lh_logic_phase_concrete`) for the same reason.

## LHU-specific

* `jolt_lhu_write_phase` — `wX_bits rd (shift_bits_right v1 48)` (SRLI).
* `jolt_lhu_decomposed` — composes LB's load + LH's logic + LHU's write.
* `jolt_lhu_write_phase_concrete`, `jolt_lhu_decomposed_from_phase_runs`,
  `jolt_lhu_decomposed_writes_logic_value`.
-/

/-- LHU write phase: `wX_bits rd (shift_bits_right v1 48)` — logical shift
    right, zero-fills the upper 48 bits. Only monadic difference from
    `jolt_lh_write_phase`. -/
def jolt_lhu_write_phase (rd : regidx) (v1 : BitVec 64) : JoltMonad ExecutionResult := do
  liftSail (wX_bits rd (shift_bits_right v1 (48 : BitVec 6)))
  pure RETIRE_SUCCESS

/-- The decomposed LHU program: read rs1, form `ea`, run LB's load phase,
    run LH's logic phase, then run LHU's write phase. -/
def jolt_lhu_decomposed (imm : BitVec 12) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let base ← liftSail (rX_bits rs1)
  let ea := base + sign_extend (m := 64) imm
  match ← LB_main.jolt_lb_load_phase ea with
  | .Retire_Success () =>
      let v1 ← LH_main.jolt_lh_logic_phase
      jolt_lhu_write_phase rd v1
  | other => pure other

/-- The LHU write phase writes `shift_bits_right logic_val 48` to `rd`.
    Structurally identical to `LH_main.jolt_lh_write_phase_concrete`,
    with `shift_bits_right` in place of `shift_bits_right_arith`. -/
theorem jolt_lhu_write_phase_concrete (rd : regidx) (js : SailJoltState)
    (js_logic : SailJoltState) (logic_val : BitVec 64)
    (hlogic_sail : js_logic.sail = js.sail) :
    ∃ js',
      (jolt_lhu_write_phase rd logic_val).run js_logic = .ok RETIRE_SUCCESS js' ∧
      js'.sail =
        stateAfterWrite js.sail rd (shift_bits_right logic_val (48 : BitVec 6)) := by
  unfold jolt_lhu_write_phase
  obtain ⟨s', hw⟩ := wX_shape rd (shift_bits_right logic_val (48 : BitVec 6)) js.sail
  let js' : SailJoltState := { sail := s', vregs := js_logic.vregs }
  refine ⟨js', ?_, ?_⟩
  · simp only [liftSail, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
    rw [hlogic_sail, hw]
  · exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

/-- If LB's load + LH's logic + LHU's write phases all run successfully
    in sequence, then `jolt_lhu_decomposed` runs successfully with the
    same final state. -/
theorem jolt_lhu_decomposed_from_phase_runs (imm : BitVec 12) (rs1 rd : regidx)
    (js js_load js_logic js' : SailJoltState)
    (val logic_val : BitVec 64)
    (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (hload_run :
      (LB_main.jolt_lb_load_phase (load_effective_address val imm)).run js = .ok RETIRE_SUCCESS js_load)
    (hlogic_run :
      (LH_main.jolt_lh_logic_phase).run js_load = .ok logic_val js_logic)
    (hwrite_run :
      (jolt_lhu_write_phase rd logic_val).run js_logic = .ok RETIRE_SUCCESS js') :
    (jolt_lhu_decomposed imm rs1 rd).run js = .ok RETIRE_SUCCESS js' := by
  have hload_run' :
      LB_main.jolt_lb_load_phase (val + sign_extend (m := 64) imm) js = .ok RETIRE_SUCCESS js_load := by
    simpa [load_effective_address, EStateM.run] using hload_run
  have hlogic_run' :
      LH_main.jolt_lh_logic_phase js_load = .ok logic_val js_logic := by
    simpa [EStateM.run] using hlogic_run
  have hwrite_run' :
      jolt_lhu_write_phase rd logic_val js_logic = .ok RETIRE_SUCCESS js' := by
    simpa [EStateM.run] using hwrite_run
  unfold jolt_lhu_decomposed
  simp only [liftSail, bind, EStateM.bind, pure, EStateM.run]
  rw [hrx]
  simp only []
  rw [hload_run']
  change (EStateM.bind LH_main.jolt_lh_logic_phase (fun v1 => jolt_lhu_write_phase rd v1)) js_load =
    .ok RETIRE_SUCCESS js'
  simp only [EStateM.bind]
  rw [hlogic_run']
  simpa using hwrite_run'

/-- Under the standing Jolt + dword-load assumptions, the decomposed LHU
    program
      1. succeeds with some final state `js'`,
      2. its logic phase (LH's) returns `logic_val = shift_left dword
         (shift_left (ea XOR 6) 3)[5:0]`, and
      3. `rd` holds `shift_bits_right logic_val 48` (zero-extended
         halfword).
    Mirrors `jolt_lh_decomposed_writes_logic_value` with `shift_bits_right`
    in place of `shift_bits_right_arith` in the final value. -/
theorem jolt_lhu_decomposed_writes_logic_value (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (val : BitVec 64)
    (hrd : rd ≠ regidx.Regidx 0)
    (hcfg : JoltConfig js.sail)
    (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail) :
    ∃ js' logic_val,
      (jolt_lhu_decomposed imm rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      logic_val =
        shift_bits_left
          (loaded_dword_at js.sail (compute_aligned_dword_base_address val imm))
          (Sail.BitVec.extractLsb
            (shift_bits_left
              ((load_effective_address val imm) ^^^ (6 : BitVec 64))
              (3 : BitVec 6)) 5 0) ∧
      js'.sail =
        stateAfterWrite js.sail rd
          (shift_bits_right logic_val (48 : BitVec 6)) := by
  rcases InstructionEquivalence.load_phase_setup_concrete_andi imm js val with
    ⟨js1, hsetup_run, hsetup_sail, hsetup_v0, hsetup_v1⟩
  have h_daddr_aligned : AlignedDwordAccess (compute_aligned_dword_base_address val imm) := by
    simpa [compute_aligned_dword_base_address, load_effective_address, aligned_dword_addr_eq] using
      (aligned_dword_addr_is_aligned_dword_access val imm)
  rcases InstructionEquivalence.vreg_LD_step_concrete js js1 (compute_aligned_dword_base_address val imm)
      hcfg hsetup_sail hsetup_v1 h_daddr_aligned h_dword_translate h_dword_phys with
    ⟨js_load, hld, hload_sail, hload_v0_raw, hload_v1⟩
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
  rcases LH_main.jolt_lh_logic_phase_concrete imm js js_load val hload_sail hload_v0 hload_v1 with
    ⟨js_logic, logic_val, hlogic_run, hlogic_v1, hlogic_val, hlogic_sail⟩
  rcases jolt_lhu_write_phase_concrete rd js js_logic logic_val hlogic_sail with
    ⟨js', hwrite_run, hwrite_sail⟩
  refine ⟨js', logic_val, ?_, hlogic_val, hwrite_sail⟩
  exact jolt_lhu_decomposed_from_phase_runs imm rs1 rd js js_load js_logic js' val logic_val
    hrx hload_run hlogic_run hwrite_run

end LHU_main
