import JoltBytecode.JoltISA.Environment
import JoltBytecode.JoltISA.Expansions.Load
import JoltBytecode.InstructionEquivalence.Memory.Utils
import JoltBytecode.VirtualInstructions
import JoltBytecode.InstructionEquivalence.LoadDefUtils
import JoltBytecode.InstructionEquivalence.LoadFamily.PhaseHelpers
import JoltBytecode.InstructionEquivalence.LoadFamily.DwordArithmetic
import JoltBytecode.InstructionEquivalence.LoadFamily.ProgramBlocks
import JoltBytecode.InstructionEquivalence.LoadFamily.LB_decomposed
import JoltBytecode.InstructionEquivalence.ProofSupport
import Mathlib.Tactic.IntervalCases

set_option maxHeartbeats 1_000_000_000
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

This file contains the original `jolt_lb` monadic program, the bridge
lemma (a pure bit-vector identity specialised to LB), and the top-level
equivalence theorem. Unlike LW, byte loads have no alignment failure case,
so there is no aligned/misaligned split.

## What lives here (by role)

* `jolt_lb` — the Jolt LB program as a `JoltMonad ExecutionResult`.
* `jolt_lb_run_eq_decomposed` — connects `jolt_lb` to the decomposed-file
  version. Byte loads have no alignment branch, so this is a simple
  unfold + rw.
* `jolt_lb_bridge` — specialisation of `sll_srai_extracts_byte` and
  `loaded_byte_in_dword` from `DwordArithmetic` to LB's shape: Jolt's
  logic-phase expression equals `sign_extend (loaded_byte_at …)`.
* `jolt_lb_concrete`, `execute_LB_reduces`, `jolt_lb_eq_sail` — the
  run-level Jolt fact, the Sail-side `execute_LOAD` reduction, and the
  main equivalence theorem combining the two.

Shared pure bit-vector, memory-shape, and phase-composition helpers live
in `DwordArithmetic.lean`, `LoadDefUtils.lean`, and `PhaseHelpers.lean`.
-/

/-- The original Jolt LB program. No alignment check — byte loads are
    always aligned. One Lean line per line of the tracer bytecode
    (`tracer/src/instruction/lb.rs::inline_sequence_64`). -/
def jolt_lb (imm : BitVec 12) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let _ ← vreg_ADDI_from_real 0 rs1 imm               -- ADDI v0, rs1, imm
  let _ ← vreg_ANDI 1 0 (-8 : BitVec 12)              -- ANDI v1, v0, -8
  match ← vreg_LD 1 1 0 with                           -- LD   v1, v1, 0
  | .Retire_Success () =>
      let _ ← vreg_XORI 0 0 7                          -- XORI v0, v0, 7
      let _ ← vreg_SLLI 0 0 3                          -- SLLI v0, v0, 3
      let _ ← vreg_SLL 1 1 0                           -- SLL  v1, v1, v0
      vreg_SRAI_to_real rd 1 (56 : BitVec 6)           -- SRAI rd, v1, 56
  | other => pure other

/-- `jolt_lb` is just `jolt_lb_decomposed` with the phase calls inlined.
    No alignment hypothesis required: byte loads have no alignment check,
    so we just need `hrx` to pin `rX_bits`. -/
theorem jolt_lb_run_eq_decomposed (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState) (val : BitVec 64)
    (hrx : rX_bits rs1 js.sail = .ok val js.sail) :
    (jolt_lb imm rs1 rd).run js = (jolt_lb_decomposed imm rs1 rd).run js := by
  -- The new boundary-crossing combinators need unfolding to match the
  -- inlined form in `jolt_lb_decomposed`'s phase defs.
  unfold jolt_lb jolt_lb_decomposed vreg_ADDI_from_real vreg_SRAI_to_real
    jolt_lb_load_phase jolt_lb_logic_phase jolt_lb_write_phase
  simp only [liftSail, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
  rw [hrx]
  rfl

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

/-- `jolt_lb` succeeds and leaves `rd` holding
    `sign_extend (loaded_byte_at js.sail ea)`. Composes
    `jolt_lb_decomposed_writes_logic_value` with `jolt_lb_bridge` via
    `congrArg`. -/
theorem jolt_lb_concrete (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail) :
    ∃ js' : SailJoltState,
      (jolt_lb imm rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (loaded_byte_at js.sail (load_effective_address val imm))) := by
  have hrun_eq :
      (jolt_lb imm rs1 rd).run js = (jolt_lb_decomposed imm rs1 rd).run js := by
    simpa using jolt_lb_run_eq_decomposed imm rs1 rd js val hrx
  rcases jolt_lb_decomposed_writes_logic_value imm rs1 rd js val
      hrd hcfg hrx h_dword_translate h_dword_phys with
    ⟨js', logic_val, hdecomp_run, hlogic_val, hwrite_sail⟩
  refine ⟨js', ?_, ?_⟩
  · rw [hrun_eq]
    exact hdecomp_run
  · rw [hwrite_sail, hlogic_val]
    exact congrArg (stateAfterWrite js.sail rd)
      (jolt_lb_bridge js.sail (load_effective_address val imm))

/-- Sail-side `execute_LOAD imm rs1 rd false 1` reduces to
    `stateAfterWrite rd (sign_extend (loaded_byte_at ea))` under the
    `LoadReadAssumptions` bundle for size 1. No `h_no_ovf` needed —
    single-byte reads cannot overflow the 64-bit address space. -/
theorem execute_LB_reduces (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (hload : LoadReadAssumptions (load_effective_address val imm) 1 js.sail) :
    (execute_LOAD imm rs1 rd false 1).run js.sail =
    .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (loaded_byte_at js.sail (load_effective_address val imm)))) := by
  unfold execute_LOAD
  simp only [bind, pure]
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  simp (config := { decide := true }) only []
  simp (config := { decide := true }) only [PreSail.assert, EStateM.bind, pure, EStateM.pure,
       EStateM.run, if_true]
  rw [vmem_read_byte_reduces imm rs1 js.sail val hrx hload.aligned hload.translate
      (mem_read_1_eq_loaded_byte _ js.sail hcfg hload.phys)]
  simp only [extend_value, Bool.false_eq_true, if_false, EStateM.bind, EStateM.pure]
  obtain ⟨s', hw⟩ := wX_shape rd
    (sign_extend (m := 64) (loaded_byte_at js.sail (load_effective_address val imm)))
    js.sail
  rw [hw]
  simp only [RETIRE_SUCCESS]
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

/-- **Main theorem.** Jolt LB equals Sail LB on every input. No
    aligned/misaligned case split — byte loads can't misalign. -/
theorem jolt_lb_eq_sail (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail)
    (hload : LoadReadAssumptions (load_effective_address val imm) 1 js.sail) :
    projectResult ((jolt_lb imm rs1 rd).run js) =
    (execute_LOAD imm rs1 rd false 1).run js.sail := by
  have hjolt :=
    jolt_lb_concrete imm rs1 rd hrd js hcfg val hrx h_dword_translate h_dword_phys
  have hsail := execute_LB_reduces imm rs1 rd js hcfg val hrx hload
  rcases hjolt with ⟨js', hjolt_run, hjolt_sail⟩
  rw [hjolt_run]
  simp only [projectResult, project]
  rw [hjolt_sail, hsail]

/-!
## Program-level LB theorem

The theorem below is the new public shape for signed byte loads.  The Jolt side
is the structured `JoltISA.lbProgram`, so the proof follows the generated
instruction sequence rather than the old proof-oriented do-block.
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
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail) :
    ∃ js' : SailJoltState,
      (JoltISA.execProgram (JoltISA.lbProgram imm rs1 rd)).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (loaded_byte_at js.sail (load_effective_address val imm))) := by
  let writeTail : JoltISA.Program :=
    .instr (.SRAI (.xreg rd) (.vreg 1) (56 : BitVec 6)) (.done RETIRE_SUCCESS)
  let logicTail : JoltISA.Program :=
    .instr (.XORI (.vreg 0) (.vreg 0) (7 : BitVec 12)) <|
    .instr (.SLLI (.vreg 0) (.vreg 0) (3 : BitVec 6)) <|
    .instr (.SLL (.vreg 1) (.vreg 1) (.vreg 0)) writeTail
  rcases LoadProgramBlocks.setupBlock logicTail imm rs1 js hcfg val hrx
      h_dword_translate h_dword_phys with
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
  have hshifted : js_shift.vregs 1 = shiftedValue := by
    simpa [shiftedValue] using hshift_v1
  rcases LoadProgramBlocks.sraiWriteBlock (.done RETIRE_SUCCESS)
      rd (56 : BitVec 6) js js_shift shiftedValue hshift_sail hshifted with
    ⟨js', hwrite_run, hwrite_sail⟩
  refine ⟨js', ?_, ?_⟩
  · unfold JoltISA.lbProgram
    change (JoltISA.execProgram
      (.instr (.ADDI (.vreg 0) (.xreg rs1) imm) <|
       .instr (.ANDI (.vreg 1) (.vreg 0) (-8 : BitVec 12)) <|
       .instr (.LD 1 1 0) logicTail)).run js = .ok RETIRE_SUCCESS js'
    rw [hload_run, hlogic_run, hwrite_run]
    rfl
  · rw [hwrite_sail]
    exact congrArg (stateAfterWrite js.sail rd) (by
      have h7 : sign_extend (m := 64) (7 : BitVec 12) = (7 : BitVec 64) := by decide
      simpa [shiftedValue, compute_aligned_dword_base_address, h7] using
        (jolt_lb_bridge js.sail (load_effective_address val imm)))

/-- **Main program theorem for LB.**  The structured Jolt-ISA expansion
`lbProgram`, interpreted by `execProgram`, agrees with Sail's signed byte-load
execution. -/
theorem lbProgram_eq_sail (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail)
    (hload : LoadReadAssumptions (load_effective_address val imm) 1 js.sail) :
    projectResult ((JoltISA.execProgram (JoltISA.lbProgram imm rs1 rd)).run js) =
    (execute_LOAD imm rs1 rd false 1).run js.sail := by
  rcases lbProgram_concrete imm rs1 rd js hcfg val hrx
      h_dword_translate h_dword_phys with
    ⟨js', hjolt, hjolt_sail⟩
  have hsail := execute_LB_reduces imm rs1 rd js hcfg val hrx hload
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail, hsail]

end LB_main
