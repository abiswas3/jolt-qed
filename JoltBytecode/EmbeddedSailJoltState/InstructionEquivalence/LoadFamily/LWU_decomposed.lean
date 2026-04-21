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

namespace LWU_main

/-!
# LWU: Decomposed-form lemmas

LWU uses the **byte-family extraction pattern** (SLL+SRLI with an XORI-
based shift amount) — unlike `LW`, which uses SRL + `VirtualSignExtend-
Word`. From the tracer bytecode:

    VirtualAssertWordAlignment rs1, imm
    ADDI  v0, rs1, imm
    ANDI  v1, v0, -8
    LD    v1, v1, 0
    XORI  v0, v0, 4
    SLLI  v0, v0, 3
    SLL   v1, v1, v0
    SRLI  rd, v1, 32

## Reuse

* **Load phase** — reused from `LB_decomposed`.

## LWU-specific

* `jolt_lwu_logic_phase` — XORI 4 (not 6 or 7), SLLI 3, SLL, readVReg 1.
* `jolt_lwu_write_phase` — `wX_bits rd (shift_bits_right v1 32)`.
* `jolt_lwu_decomposed`, logic/write phase concrete lemmas, composition.
-/

/-- LWU logic phase: XORI 4 encodes `4 - (ea & 4)`, which is the left-
    shift distance that pushes the target word to the top 32 bits. -/
def jolt_lwu_logic_phase : JoltMonad (BitVec 64) := do
  let _ ← vreg_XORI 0 0 4
  let _ ← vreg_SLLI 0 0 3
  let _ ← vreg_SLL 1 1 0
  readVReg 1

/-- LWU write phase: `wX_bits rd (shift_bits_right v1 32)` — SRLI 32 pulls
    the target word down to the low 32 bits and zero-fills the upper 32. -/
def jolt_lwu_write_phase (rd : regidx) (v1 : BitVec 64) : JoltMonad ExecutionResult := do
  liftSail (wX_bits rd (shift_bits_right v1 (32 : BitVec 6)))
  pure RETIRE_SUCCESS

/-- The decomposed LWU program: read rs1, form `ea`, run LB's load phase,
    run LWU's logic and write phases. -/
def jolt_lwu_decomposed (imm : BitVec 12) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let base ← liftSail (rX_bits rs1)
  let ea := base + sign_extend (m := 64) imm
  match ← LB_main.jolt_lb_load_phase ea with
  | .Retire_Success () =>
      let v1 ← jolt_lwu_logic_phase
      jolt_lwu_write_phase rd v1
  | other => pure other

/-- Pure value-level identity for the LWU logic phase. Mirrors
    `jolt_lh_logic_phase_value` with `4` in place of `6`. -/
theorem jolt_lwu_logic_phase_value (imm : BitVec 12) (js : SailJoltState)
    (js_load : SailJoltState) (val : BitVec 64)
    (hload_v0 : js_load.vregs 0 = load_effective_address val imm)
    (hload_v1 : js_load.vregs 1 = loaded_dword_at js.sail (compute_aligned_dword_base_address val imm)) :
    shift_bits_left
      (js_load.vregs 1)
      (Sail.BitVec.extractLsb
        (shift_bits_left
          ((js_load.vregs 0) ^^^ (sign_extend (m := 64) (4 : BitVec 12)))
          (3 : BitVec 6)) 5 0) =
    shift_bits_left
      (loaded_dword_at js.sail (compute_aligned_dword_base_address val imm))
      (Sail.BitVec.extractLsb
        (shift_bits_left
          ((load_effective_address val imm) ^^^ (4 : BitVec 64))
          (3 : BitVec 6)) 5 0) := by
  have h4 : sign_extend (m := 64) (4 : BitVec 12) = (4 : BitVec 64) := by decide
  rw [hload_v0, hload_v1, h4]

/-- Running LWU's logic phase succeeds. -/
theorem jolt_lwu_logic_phase_run (js_load : SailJoltState) :
    ∃ js_logic,
      (jolt_lwu_logic_phase).run js_load = .ok (js_logic.vregs 1) js_logic ∧
      js_logic.sail = js_load.sail ∧
      js_logic.vregs 1 =
        shift_bits_left
          (js_load.vregs 1)
          (Sail.BitVec.extractLsb
            (shift_bits_left
              ((js_load.vregs 0) ^^^ (sign_extend (m := 64) (4 : BitVec 12)))
              (3 : BitVec 6)) 5 0) := by
  let js_xor : SailJoltState :=
    { sail := js_load.sail
      vregs := fun r =>
        if r = 0 then js_load.vregs 0 ^^^ sign_extend (m := 64) (4 : BitVec 12)
        else js_load.vregs r }
  let js_shift0 : SailJoltState :=
    { sail := js_load.sail
      vregs := fun r =>
        if r = 0 then shift_bits_left (js_xor.vregs 0) (3 : BitVec 6)
        else js_xor.vregs r }
  let js_logic : SailJoltState :=
    { sail := js_load.sail
      vregs := fun r =>
        if r = 1 then
          shift_bits_left (js_shift0.vregs 1)
            (Sail.BitVec.extractLsb (js_shift0.vregs 0) 5 0)
        else js_shift0.vregs r }
  have hxori : vreg_XORI 0 0 (4 : BitVec 12) js_load = .ok RETIRE_SUCCESS js_xor := by
    change vreg_XORI 0 0 (4 : BitVec 12) js_load = .ok RETIRE_SUCCESS
      { sail := js_load.sail
        vregs := fun r =>
          if r = 0 then js_load.vregs 0 ^^^ sign_extend (m := 64) (4 : BitVec 12)
          else js_load.vregs r }
    simpa [js_xor] using (vreg_XORI_run 0 0 (4 : BitVec 12) js_load)
  have hslli : vreg_SLLI 0 0 3 js_xor = .ok RETIRE_SUCCESS js_shift0 := by
    change vreg_SLLI 0 0 3 js_xor = .ok RETIRE_SUCCESS
      { sail := js_xor.sail
        vregs := fun r =>
          if r = 0 then shift_bits_left (js_xor.vregs 0) (3 : BitVec 6)
          else js_xor.vregs r }
    simpa [js_xor, js_shift0] using (vreg_SLLI_run 0 0 3 js_xor)
  have hsll : vreg_SLL 1 1 0 js_shift0 = .ok RETIRE_SUCCESS js_logic := by
    change vreg_SLL 1 1 0 js_shift0 = .ok RETIRE_SUCCESS
      { sail := js_shift0.sail
        vregs := fun r =>
          if r = 1 then
            shift_bits_left (js_shift0.vregs 1) (Sail.BitVec.extractLsb (js_shift0.vregs 0) 5 0)
          else js_shift0.vregs r }
    simpa [js_shift0, js_logic] using (vreg_SLL_run 1 1 0 js_shift0)
  have hread_v1 : readVReg 1 js_logic = .ok (js_logic.vregs 1) js_logic := by
    simpa using (readVReg_run 1 js_logic)
  refine ⟨js_logic, ?_, rfl, ?_⟩
  · simp only [jolt_lwu_logic_phase, bind, EStateM.bind, EStateM.run]
    rw [hxori]
    simp only [EStateM.bind, EStateM.pure]
    rw [hslli]
    simp only [EStateM.bind, EStateM.pure]
    rw [hsll]
    simp only [EStateM.bind, EStateM.pure]
    exact hread_v1
  · simp [js_logic, js_shift0, js_xor]

/-- Logic phase concrete. -/
theorem jolt_lwu_logic_phase_concrete (imm : BitVec 12) (js : SailJoltState)
    (js_load : SailJoltState) (val : BitVec 64)
    (hload_sail : js_load.sail = js.sail)
    (hload_v0 : js_load.vregs 0 = load_effective_address val imm)
    (hload_v1 : js_load.vregs 1 = loaded_dword_at js.sail (compute_aligned_dword_base_address val imm)) :
    ∃ js_logic logic_val,
      (jolt_lwu_logic_phase).run js_load = .ok logic_val js_logic ∧
      js_logic.vregs 1 = logic_val ∧
      logic_val =
        shift_bits_left
          (loaded_dword_at js.sail (compute_aligned_dword_base_address val imm))
          (Sail.BitVec.extractLsb
            (shift_bits_left
              ((load_effective_address val imm) ^^^ (4 : BitVec 64))
              (3 : BitVec 6)) 5 0) ∧
      js_logic.sail = js.sail := by
  rcases jolt_lwu_logic_phase_run js_load with ⟨js_logic, hrun, hsail, hv1⟩
  refine ⟨js_logic, js_logic.vregs 1, hrun, rfl, ?_, ?_⟩
  · rw [hv1]
    exact jolt_lwu_logic_phase_value imm js js_load val hload_v0 hload_v1
  · simpa [hload_sail] using hsail

/-- LWU write phase writes `shift_bits_right logic_val 32` to `rd`. -/
theorem jolt_lwu_write_phase_concrete (rd : regidx) (js : SailJoltState)
    (js_logic : SailJoltState) (logic_val : BitVec 64)
    (hlogic_sail : js_logic.sail = js.sail) :
    ∃ js',
      (jolt_lwu_write_phase rd logic_val).run js_logic = .ok RETIRE_SUCCESS js' ∧
      js'.sail =
        stateAfterWrite js.sail rd (shift_bits_right logic_val (32 : BitVec 6)) := by
  unfold jolt_lwu_write_phase
  obtain ⟨s', hw⟩ := wX_shape rd (shift_bits_right logic_val (32 : BitVec 6)) js.sail
  let js' : SailJoltState := { sail := s', vregs := js_logic.vregs }
  refine ⟨js', ?_, ?_⟩
  · simp only [liftSail, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
    rw [hlogic_sail, hw]
  · exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

/-- Three-phase composition. -/
theorem jolt_lwu_decomposed_from_phase_runs (imm : BitVec 12) (rs1 rd : regidx)
    (js js_load js_logic js' : SailJoltState)
    (val logic_val : BitVec 64)
    (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (hload_run :
      (LB_main.jolt_lb_load_phase (load_effective_address val imm)).run js = .ok RETIRE_SUCCESS js_load)
    (hlogic_run :
      (jolt_lwu_logic_phase).run js_load = .ok logic_val js_logic)
    (hwrite_run :
      (jolt_lwu_write_phase rd logic_val).run js_logic = .ok RETIRE_SUCCESS js') :
    (jolt_lwu_decomposed imm rs1 rd).run js = .ok RETIRE_SUCCESS js' := by
  have hload_run' :
      LB_main.jolt_lb_load_phase (val + sign_extend (m := 64) imm) js = .ok RETIRE_SUCCESS js_load := by
    simpa [load_effective_address, EStateM.run] using hload_run
  have hlogic_run' :
      jolt_lwu_logic_phase js_load = .ok logic_val js_logic := by
    simpa [EStateM.run] using hlogic_run
  have hwrite_run' :
      jolt_lwu_write_phase rd logic_val js_logic = .ok RETIRE_SUCCESS js' := by
    simpa [EStateM.run] using hwrite_run
  unfold jolt_lwu_decomposed
  simp only [liftSail, bind, EStateM.bind, pure, EStateM.run]
  rw [hrx]
  simp only []
  rw [hload_run']
  change (EStateM.bind jolt_lwu_logic_phase (fun v1 => jolt_lwu_write_phase rd v1)) js_load =
    .ok RETIRE_SUCCESS js'
  simp only [EStateM.bind]
  rw [hlogic_run']
  simpa using hwrite_run'

/-- Top-level decomposed fact. -/
theorem jolt_lwu_decomposed_writes_logic_value (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (val : BitVec 64)
    (hrd : rd ≠ regidx.Regidx 0)
    (hcfg : JoltConfig js.sail)
    (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail) :
    ∃ js' logic_val,
      (jolt_lwu_decomposed imm rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      logic_val =
        shift_bits_left
          (loaded_dword_at js.sail (compute_aligned_dword_base_address val imm))
          (Sail.BitVec.extractLsb
            (shift_bits_left
              ((load_effective_address val imm) ^^^ (4 : BitVec 64))
              (3 : BitVec 6)) 5 0) ∧
      js'.sail =
        stateAfterWrite js.sail rd
          (shift_bits_right logic_val (32 : BitVec 6)) := by
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
  rcases jolt_lwu_logic_phase_concrete imm js js_load val hload_sail hload_v0 hload_v1 with
    ⟨js_logic, logic_val, hlogic_run, hlogic_v1, hlogic_val, hlogic_sail⟩
  rcases jolt_lwu_write_phase_concrete rd js js_logic logic_val hlogic_sail with
    ⟨js', hwrite_run, hwrite_sail⟩
  refine ⟨js', logic_val, ?_, hlogic_val, hwrite_sail⟩
  exact jolt_lwu_decomposed_from_phase_runs imm rs1 rd js js_load js_logic js' val logic_val
    hrx hload_run hlogic_run hwrite_run

end LWU_main
