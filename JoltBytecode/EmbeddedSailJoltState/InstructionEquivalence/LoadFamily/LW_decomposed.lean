import JoltBytecode.EmbeddedSailJoltState.Defs
import JoltBytecode.EmbeddedSailJoltState.MemoryUtils
import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadDefUtils
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadFamily.PhaseHelpers
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

namespace LW_main

/-!
# LW: Decomposed-form lemmas

Phase definitions (`jolt_lw_load_phase`, `jolt_lw_logic_phase`,
`jolt_lw_write_phase`), the decomposed program `jolt_lw_decomposed`, and the
phase-level concrete lemmas used to reason about it — up to and including
`jolt_lw_decomposed_writes_logic_value`.

The original program `jolt_lw`, the bridge lemma `jolt_lw_bridge`, and the
top-level equivalence theorems live in `LW_main.lean`, which imports this
file.

## What lives here (by role)

* Phase definitions: `jolt_lw_load_phase`, `jolt_lw_logic_phase`,
  `jolt_lw_write_phase`, and the composed `jolt_lw_decomposed`.
* Logic-phase lemmas (chain: value → run → concrete):
  `jolt_lw_logic_phase_value` unfolds the symbolic vreg reads,
  `jolt_lw_logic_phase_run` shows the monadic run succeeds and produces
  the expected shift-and-extract expression, `jolt_lw_logic_phase_concrete`
  packages both.
* Write-phase lemma: `jolt_lw_write_phase_concrete` — running
  `wX_bits rd v1; jolt_virtual_sign_extend_word rd` writes the sign-extended
  lower 32 bits of `v1` to `rd`.
* Three-phase composition: `jolt_lw_decomposed_from_phase_runs` threads a
  successful load/logic/write triple into a `jolt_lw_decomposed` run.
* Top-level decomposed fact: `jolt_lw_decomposed_writes_logic_value` says
  the decomposed program succeeds and leaves `rd` holding
  `sign_extend (extractLsb logic_val 31 0)` for the long shift expression.
-/

-- ============================================================================
-- Phase definitions
-- ============================================================================

/-- Load phase: write `ea` to v0, set v1 to the aligned-down base via an
    explicit `readVReg 0; writeVReg 1 (v0 &&& -8)` pair, then `vreg_LD`. -/
def jolt_lw_load_phase (ea : BitVec 64) : JoltMonad ExecutionResult := do
  writeVReg 0 ea
  let v0 ← readVReg 0
  writeVReg 1 (v0 &&& (-8 : BitVec 64))
  vreg_LD 1 1 0

/-- Logic phase: `SLLI v0 0 3` puts `ea * 8` into v0; `SRL v1 1 0` shifts v1
    right by the low 6 bits of v0. Returns the shifted dword from v1. -/
def jolt_lw_logic_phase : JoltMonad (BitVec 64) := do
  let _ ← vreg_SLLI 0 0 3
  let _ ← vreg_SRL 1 1 0
  readVReg 1

/-- Write phase: write `v1` to rd in full, then apply the virtual
    sign-extend-word primitive, which sign-extends the lower 32 bits of rd
    back into rd. -/
def jolt_lw_write_phase (rd : regidx) (v1 : BitVec 64) : JoltMonad ExecutionResult := do
  liftSail (wX_bits rd v1)
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

/-- The decomposed LW program: read rs1, form `ea`, run the three phases. -/
def jolt_lw_decomposed (imm : BitVec 12) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let base ← liftSail (rX_bits rs1)
  let ea := base + sign_extend (m := 64) imm
  match ← jolt_lw_load_phase ea with
  | .Retire_Success () =>
      let v1 ← jolt_lw_logic_phase
      jolt_lw_write_phase rd v1
  | other => pure other

-- ============================================================================
-- Logic-phase lemmas (value → run → concrete)
-- ============================================================================

/-- Pure value-level identity: rewrites the symbolic `js_load.vregs 0` and
    `js_load.vregs 1` in the logic-phase output to the concrete
    `load_effective_address` / `loaded_dword_at` expressions. -/
theorem jolt_lw_logic_phase_value (imm : BitVec 12) (js : SailJoltState) (js_load : SailJoltState) (val : BitVec 64)
    (hload_v0 : js_load.vregs 0 = load_effective_address val imm)
    (hload_v1 : js_load.vregs 1 = loaded_dword_at js.sail (compute_aligned_dword_base_address val imm))
    :
    shift_bits_right
      (js_load.vregs 1)
      (Sail.BitVec.extractLsb (shift_bits_left (js_load.vregs 0) (3 : BitVec 6)) 5 0) =
    shift_bits_right
      (loaded_dword_at js.sail (compute_aligned_dword_base_address val imm))
      (Sail.BitVec.extractLsb
        (shift_bits_left (load_effective_address val imm) (3 : BitVec 6)) 5 0) := by
  rw [hload_v0, hload_v1]

/-- Running the logic phase from any `js_load` succeeds: it leaves the
    shifted dword in vreg 1, doesn't touch the Sail state, and returns the
    same value via `readVReg 1`. -/
theorem jolt_lw_logic_phase_run (js_load : SailJoltState) :
    ∃ js_logic,
      (jolt_lw_logic_phase).run js_load = .ok (js_logic.vregs 1) js_logic ∧
      js_logic.sail = js_load.sail ∧
      js_logic.vregs 1 =
        shift_bits_right
          (js_load.vregs 1)
          (Sail.BitVec.extractLsb (shift_bits_left (js_load.vregs 0) (3 : BitVec 6)) 5 0) := by
  let js_shift0 : SailJoltState :=
    { sail := js_load.sail
      vregs := fun r => if r = 0 then shift_bits_left (js_load.vregs 0) (3 : BitVec 6) else js_load.vregs r }
  let js_logic : SailJoltState :=
    { sail := js_load.sail
      vregs := fun r =>
        if r = 1 then
          shift_bits_right
            (js_load.vregs 1)
            (Sail.BitVec.extractLsb (shift_bits_left (js_load.vregs 0) (3 : BitVec 6)) 5 0)
        else js_shift0.vregs r }
  have hslli : vreg_SLLI 0 0 3 js_load = .ok RETIRE_SUCCESS js_shift0 := by
    change vreg_SLLI 0 0 3 js_load = .ok RETIRE_SUCCESS
      { sail := js_load.sail
        vregs := fun r => if r = 0 then shift_bits_left (js_load.vregs 0) (3 : BitVec 6) else js_load.vregs r }
    simpa [js_shift0] using (vreg_SLLI_run 0 0 3 js_load)
  have hsrl : vreg_SRL 1 1 0 js_shift0 = .ok RETIRE_SUCCESS js_logic := by
    change vreg_SRL 1 1 0 js_shift0 = .ok RETIRE_SUCCESS
      { sail := js_shift0.sail
        vregs := fun r =>
          if r = 1 then
            shift_bits_right (js_shift0.vregs 1) (Sail.BitVec.extractLsb (js_shift0.vregs 0) 5 0)
          else js_shift0.vregs r }
    simpa [js_shift0, js_logic] using (vreg_SRL_run 1 1 0 js_shift0)
  have hread_v1 : readVReg 1 js_logic = .ok (js_logic.vregs 1) js_logic := by
    simpa using (readVReg_run 1 js_logic)
  refine ⟨js_logic, ?_, rfl, ?_⟩
  · simp only [jolt_lw_logic_phase, bind, EStateM.bind, EStateM.run]
    rw [hslli]
    simp only [EStateM.bind, EStateM.pure]
    rw [hsrl]
    simp only [EStateM.bind, EStateM.pure]
    exact hread_v1
  · simp [js_logic, js_shift0]

/-- Combines `jolt_lw_logic_phase_run` with `jolt_lw_logic_phase_value`:
    running the logic phase on a post-load state produces `logic_val` in
    its long shift-and-extract form, leaves the Sail state untouched, and
    stores `logic_val` in vreg 1. -/
theorem jolt_lw_logic_phase_concrete (imm : BitVec 12) (js : SailJoltState) (js_load : SailJoltState) (val : BitVec 64)
    (hload_sail : js_load.sail = js.sail)
    (hload_v0 : js_load.vregs 0 = load_effective_address val imm)
    (hload_v1 : js_load.vregs 1 = loaded_dword_at js.sail (compute_aligned_dword_base_address val imm))
    :
    ∃ js_logic logic_val,
      (jolt_lw_logic_phase).run js_load = .ok logic_val js_logic ∧
      js_logic.vregs 1 = logic_val ∧
      logic_val =
        shift_bits_right
          (loaded_dword_at js.sail (compute_aligned_dword_base_address val imm))
          (Sail.BitVec.extractLsb
            (shift_bits_left (load_effective_address val imm) (3 : BitVec 6)) 5 0) ∧
      js_logic.sail = js.sail := by
  rcases jolt_lw_logic_phase_run js_load with ⟨js_logic, hrun, hsail, hv1⟩
  refine ⟨js_logic, js_logic.vregs 1, hrun, rfl, ?_, ?_⟩
  · rw [hv1]
    exact jolt_lw_logic_phase_value imm js js_load val hload_v0 hload_v1
  · simpa [hload_sail] using hsail

-- ============================================================================
-- Write-phase lemma (LW-specific)
-- ============================================================================

/-- The LW write phase takes `logic_val` and writes its sign-extended lower
    32 bits to `rd`, leaving vregs and all other memory untouched. Uses
    `wX_shape` for the unprimed write, then the `@[simp]` virtual-sign-
    extend-word concrete lemma. -/
theorem jolt_lw_write_phase_concrete (rd : regidx) (js : SailJoltState) (js_logic : SailJoltState) (logic_val : BitVec 64)
    (hrd : rd ≠ regidx.Regidx 0)
    (hlogic_sail : js_logic.sail = js.sail)
    :
    ∃ js',
      (jolt_lw_write_phase rd logic_val).run js_logic = .ok RETIRE_SUCCESS js' ∧
      js'.sail =
        stateAfterWrite js.sail rd
          (sign_extend (m := 64) ((Sail.BitVec.extractLsb logic_val 31 0) : BitVec 32)) := by
  unfold jolt_lw_write_phase
  obtain ⟨s', hw⟩ := wX_shape rd logic_val js.sail
  let js_write : SailJoltState := { sail := s', vregs := js_logic.vregs }
  have hwrite : liftSail (wX_bits rd logic_val) js_logic = .ok () js_write := by
    unfold liftSail js_write
    rw [hlogic_sail, hw]
  have hs_write : js_write.sail = stateAfterWrite js.sail rd logic_val := by
    exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw
  have hread_rd : rX_bits rd js_write.sail = .ok logic_val js_write.sail := by
    rw [hs_write]
    exact rX_after_stateAfterWrite rd logic_val js.sail hrd
  obtain ⟨js', hvsew, hvsew_sail⟩ :=
    jolt_virtual_sign_extend_word_concrete rd js_write logic_val hrd hread_rd
  refine ⟨js', ?_, ?_⟩
  · simp only [liftSail, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
    rw [hlogic_sail, hw]
    simp only [EStateM.bind, EStateM.pure]
    cases hlast : jolt_virtual_sign_extend_word rd js_write with
    | ok a s =>
        have hs : s = js' := by
          simp [EStateM.run, hlast] at hvsew
          exact hvsew
        subst hs
        simp [hlast]
    | error e s =>
        have : False := by
          simp [EStateM.run, hlast] at hvsew
        exact False.elim this
  · rw [hvsew_sail, hs_write, stateAfterWrite_stateAfterWrite]

-- ============================================================================
-- Three-phase composition + top-level decomposed fact
-- ============================================================================

/-- If the load, logic, and write phases all run successfully in sequence,
    then `jolt_lw_decomposed` itself runs successfully with the same final
    state. Pure threading lemma. -/
theorem jolt_lw_decomposed_from_phase_runs (imm : BitVec 12) (rs1 rd : regidx) (js js_load js_logic js' : SailJoltState)
    (val logic_val : BitVec 64)
    (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (hload_run :
      (jolt_lw_load_phase (load_effective_address val imm)).run js = .ok RETIRE_SUCCESS js_load)
    (hlogic_run :
      (jolt_lw_logic_phase).run js_load = .ok logic_val js_logic)
    (hwrite_run :
      (jolt_lw_write_phase rd logic_val).run js_logic = .ok RETIRE_SUCCESS js')
    :
    (jolt_lw_decomposed imm rs1 rd).run js = .ok RETIRE_SUCCESS js' := by
  have hload_run' :
      jolt_lw_load_phase (val + sign_extend (m := 64) imm) js = .ok RETIRE_SUCCESS js_load := by
    simpa [load_effective_address, EStateM.run] using hload_run
  have hlogic_run' :
      jolt_lw_logic_phase js_load = .ok logic_val js_logic := by
    simpa [EStateM.run] using hlogic_run
  have hwrite_run' :
      jolt_lw_write_phase rd logic_val js_logic = .ok RETIRE_SUCCESS js' := by
    simpa [EStateM.run] using hwrite_run
  unfold jolt_lw_decomposed
  simp only [liftSail, bind, EStateM.bind, pure, EStateM.run]
  rw [hrx]
  simp only []
  rw [hload_run']
  change (EStateM.bind jolt_lw_logic_phase (fun v1 => jolt_lw_write_phase rd v1)) js_load =
    .ok RETIRE_SUCCESS js'
  simp only [EStateM.bind]
  rw [hlogic_run']
  simpa using hwrite_run'

/-- Under the standing Jolt + dword-load assumptions + word-alignment, the
    decomposed LW program
      1. succeeds with some final state `js'`,
      2. its logic phase returns `logic_val = shift_right(dword,
         extractLsb(ea << 3) 5 0)` (target word positioned in the lower
         32 bits), and
      3. `rd` holds `sign_extend (extractLsb logic_val 31 0)`.
    Top-level fact for the decomposed file; consumed by `jolt_lw_concrete`
    in `LW_main.lean`. -/
theorem jolt_lw_decomposed_writes_logic_value (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState) (val : BitVec 64)
    (hrd : rd ≠ regidx.Regidx 0)
    (hcfg : JoltConfig js.sail)
    (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (halign : (val + sign_extend (m := 64) imm) &&& 3 = 0)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail)
    :
    ∃ js' logic_val,
      (jolt_lw_decomposed imm rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      logic_val =
        shift_bits_right
          (loaded_dword_at js.sail (compute_aligned_dword_base_address val imm))
          (Sail.BitVec.extractLsb
            (shift_bits_left (load_effective_address val imm) (3 : BitVec 6)) 5 0) ∧
      js'.sail =
        stateAfterWrite js.sail rd
          (sign_extend (m := 64) ((Sail.BitVec.extractLsb logic_val 31 0) : BitVec 32)) := by
  rcases InstructionEquivalence.load_phase_setup_concrete imm js val with
    ⟨js1, hsetup_run, hsetup_sail, hsetup_v0, hsetup_v1⟩
  have h_daddr_aligned : AlignedDwordAccess (compute_aligned_dword_base_address val imm) := by
    simpa [compute_aligned_dword_base_address, load_effective_address, aligned_dword_addr_eq] using
      (aligned_dword_addr_is_aligned_dword_access val imm)
  rcases InstructionEquivalence.vreg_LD_step_concrete js js1 (compute_aligned_dword_base_address val imm)
      hcfg hsetup_sail hsetup_v1 h_daddr_aligned h_dword_translate h_dword_phys with
    ⟨js_load, hld, hload_sail, hload_v0_raw, hload_v1⟩
  have hload_run :
      (jolt_lw_load_phase (load_effective_address val imm)).run js = .ok RETIRE_SUCCESS js_load := by
    simpa [jolt_lw_load_phase, bind, EStateM.bind, EStateM.run] using
      (InstructionEquivalence.vreg_LD_phase_from_setup
        (do
          writeVReg 0 (load_effective_address val imm)
          let v0 ← readVReg 0
          writeVReg 1 (v0 &&& (-8 : BitVec 64)))
        js js1 js_load hsetup_run hld)
  have hload_v0 : js_load.vregs 0 = load_effective_address val imm := by
    rw [hload_v0_raw, hsetup_v0]
  rcases jolt_lw_logic_phase_concrete imm js js_load val hload_sail hload_v0 hload_v1 with
    ⟨js_logic, logic_val, hlogic_run, hlogic_v1, hlogic_val, hlogic_sail⟩
  rcases jolt_lw_write_phase_concrete rd js js_logic logic_val hrd hlogic_sail with
    ⟨js', hwrite_run, hwrite_sail⟩
  refine ⟨js', logic_val, ?_, hlogic_val, hwrite_sail⟩
  exact jolt_lw_decomposed_from_phase_runs imm rs1 rd js js_load js_logic js' val logic_val
    hrx hload_run hlogic_run hwrite_run

end LW_main
