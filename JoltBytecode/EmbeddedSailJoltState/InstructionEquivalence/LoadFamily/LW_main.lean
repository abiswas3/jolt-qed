import JoltBytecode.EmbeddedSailJoltState.Defs
import JoltBytecode.EmbeddedSailJoltState.MemoryUtils
import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadDefUtils
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadFamily.PhaseHelpers
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadFamily.DwordArithmetic
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadFamily.LW_decomposed
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
# LW: Jolt load-word (signed) top-level equivalence

From `tracer/src/instruction/lw.rs::inline_sequence_64`:

    VirtualAssertWordAlignment rs1, imm
    ADDI  v0, rs1, imm
    ANDI  rd, v0, -8
    LD    rd, rd, 0
    SLLI  v0, v0, 3
    SRL   rd, rd, v0
    VirtualSignExtendWord rd, rd, 0

This file contains the original `jolt_lw` monadic program, the bridge lemma
(a pure bit-vector identity specialised to LW), the Sail-side load-pipeline
helpers (`LWDwordReadAssumptions` and friends), and the top-level
equivalence theorems for both the aligned and misaligned cases.

## What lives here (by role)

* `jolt_lw` — the Jolt LW program as a `JoltMonad ExecutionResult`.
* `jolt_lw_bridge` — specialisation of the DwordArithmetic identities to
  LW: Jolt's logic-phase expression equals `sign_extend (loaded_word_at …)`.
* `LWDwordReadAssumptions` + `lw_dword_*_of_*` — Sail-side structures
  packaging the dword-translate / phys assumptions.
* `jolt_lw_run_eq_decomposed` — connects `jolt_lw` to the decomposed-file
  version via unfolding + `vreg_ANDI` substitution.
* `jolt_lw_concrete`, `jolt_lw_concrete_misaligned` — run-level facts about
  what `jolt_lw` produces on aligned / misaligned inputs.
* `execute_LW_reduces`, `execute_LW_misaligned` — Sail-side `execute_LOAD`
  reductions for the two cases.
* `jolt_lw_eq_sail_aligned`, `jolt_lw_eq_sail_misaligned`,
  `jolt_lw_eq_sail` — main equivalence theorems.

Shared pure bit-vector, memory-shape, and phase-composition helpers live in
`DwordArithmetic.lean`, `LoadDefUtils.lean`, and `PhaseHelpers.lean`.
-/

/-- The original Jolt LW program. Structurally close to the tracer
    bytecode (`tracer/src/instruction/lw.rs::inline_sequence_64`), with
    two asymmetries relative to the `LB` / `LBU` format:

    1. The leading `VirtualAssertWordAlignment rs1, imm` is fused with
       the ADDI (they both read `rs1`; we read once and share the value).
       This matches the decomposed program's shape and avoids a double-
       read of `rs1` that would break `jolt_lw_run_eq_decomposed`.
    2. The middle "rd" registers in the bytecode are actually virtual
       register 1 (the bytecode's `rd` alias); only the final `SRL` and
       `VirtualSignExtendWord` target the real destination. -/
def jolt_lw (imm : BitVec 12) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  -- VirtualAssertWordAlignment rs1, imm + ADDI v0, rs1, imm (fused)
  let base ← liftSail (rX_bits rs1)
  let ea := base + sign_extend (m := 64) imm
  if ea &&& 3 ≠ 0 then
    pure (ExecutionResult.Memory_Exception
      (Virtaddr ea, ExceptionType.E_Load_Addr_Align ()))
  else do
    writeVReg 0 ea                                        -- (ADDI v0, rs1, imm writes ea)
    let _ ← vreg_ANDI 1 0 (-8 : BitVec 12)                -- ANDI v1, v0, -8
    match ← vreg_LD 1 1 0 with                             -- LD   v1, v1, 0
    | .Retire_Success () =>
        let _ ← vreg_SLLI 0 0 3                            -- SLLI v0, v0, 3
        let _ ← vreg_SRL 1 1 0                             -- SRL  v1, v1, v0
        -- Copy v1 to real rd (implicit in the bytecode's "SRL rd, rd, v0"
        -- naming convention, where the destination "rd" is the real reg).
        let v1 ← readVReg 1
        liftSail (wX_bits rd v1)
        jolt_virtual_sign_extend_word rd                   -- VirtualSignExtendWord rd, rd, 0
        pure RETIRE_SUCCESS
    | other => pure other

/-- **Bridge lemma for LW.** The Jolt logic-phase computation (shift the
    enclosing dword right by `(ea mod 8) * 8`, take the low 32 bits, then
    sign-extend to 64 bits) equals the Sail-side direct word load
    sign-extended to 64 bits. Requires word alignment `halign : ea & 3 = 0`.
    Pure bit-vector algebra — just combines
    `srl_sign_extend_word_extracts_word` with `loaded_word_in_dword`. -/
theorem jolt_lw_bridge (s : SailState) (addr : BitVec 64)
    (halign : addr &&& 3 = 0) :
    (let dword := loaded_dword_at s (addr &&& (-8 : BitVec 64))
     let shift := Sail.BitVec.extractLsb (shift_bits_left addr (3 : BitVec 6)) 5 0
     let shifted := shift_bits_right dword shift
     sign_extend (m := 64) ((Sail.BitVec.extractLsb shifted 31 0) : BitVec 32))
    = sign_extend (m := 64) (loaded_word_at s addr) := by
  simp only [srl_sign_extend_word_extracts_word _ _ halign, ← loaded_word_in_dword _ _ halign]

-- ============================================================================
-- Sail-side dword-read assumption bundles (LW-specific)
-- ============================================================================

/-- LW-flavoured dword read assumptions: the aligned dword base
    `aligned_dword_addr val imm` is bare-translatable and lives in ordinary
    RAM (not MMIO). Currently unused; kept for callers that want a bundled
    assumption type. -/
structure LWDwordReadAssumptions (val : BitVec 64) (imm : BitVec 12) (s : SailState) : Prop where
  translate : BareTranslation (aligned_dword_addr val imm) s
  phys : FlatPhysMem (aligned_dword_addr val imm) 8 s

/-- Promote `LWDwordReadAssumptions` to the generic
    `DwordLoadAssumptions`. -/
theorem lw_dword_load_assumptions_of_local
    (val : BitVec 64) (imm : BitVec 12) (s : SailState)
    (h : LWDwordReadAssumptions val imm s) :
    DwordLoadAssumptions (aligned_dword_addr val imm) s := by
  refine
    { aligned := aligned_dword_addr_is_aligned_dword_access val imm
      translate := h.translate
      phys := h.phys }

/-- Construct `LWDwordReadAssumptions` from the `compute_aligned_dword_base_address`-phrased
    translate / phys hypotheses. (The two addresses are definitionally
    equal; `aligned_dword_addr_eq` bridges the notation.) -/
theorem lw_dword_read_assumptions_of_addr
    (val : BitVec 64)
    (imm : BitVec 12)
    (s : SailState)
    (htranslate : BareTranslation (compute_aligned_dword_base_address val imm) s)
    (hphys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 s) :
    LWDwordReadAssumptions val imm s := by
  have haddr : aligned_dword_addr val imm = compute_aligned_dword_base_address val imm := by
    simp [compute_aligned_dword_base_address, load_effective_address, aligned_dword_addr_eq]
  refine
    { translate := ?_
      phys := ?_ }
  · simpa [haddr] using htranslate
  · simpa [haddr] using hphys

-- ============================================================================
-- Top-level LW ↔ Sail equivalence theorems
-- ============================================================================

/-- `jolt_lw` and `jolt_lw_decomposed` produce the same final state on an
    aligned input. Both have the same load / logic / write shape once the
    alignment guard passes and the boundary-crossing combinators are
    unfolded. -/
theorem jolt_lw_run_eq_decomposed (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState) (val : BitVec 64)
    (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (halign : (val + sign_extend (m := 64) imm) &&& 3 = 0)
    :
    (jolt_lw imm rs1 rd).run js = (jolt_lw_decomposed imm rs1 rd).run js := by
  have h8 : sign_extend (m := 64) (-8 : BitVec 12) = (-8 : BitVec 64) := by decide
  unfold jolt_lw jolt_lw_decomposed jolt_lw_load_phase vreg_ANDI
  simp only [liftSail, bind, EStateM.bind, pure, EStateM.run, h8]
  rw [hrx]
  simp only []
  rw [if_neg (by simpa using halign)]
  rfl

/-- Aligned case: `jolt_lw` succeeds and leaves `rd` holding
    `sign_extend (loaded_word_at js.sail ea)`. Composes
    `jolt_lw_decomposed_writes_logic_value` with `jolt_lw_bridge` via
    `congrArg`. -/
theorem jolt_lw_concrete (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (halign : load_effective_address val imm &&& 3 = 0)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail) :
    ∃ js' : SailJoltState,
      (jolt_lw imm rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (loaded_word_at js.sail (load_effective_address val imm))) := by
  have hrun_eq :
      (jolt_lw imm rs1 rd).run js = (jolt_lw_decomposed imm rs1 rd).run js := by
    simpa using jolt_lw_run_eq_decomposed imm rs1 rd js val hrx (by simpa [load_effective_address] using halign)
  rcases jolt_lw_decomposed_writes_logic_value imm rs1 rd js val
      hrd hcfg hrx (by simpa [load_effective_address] using halign)
      h_dword_translate h_dword_phys with
    ⟨js', logic_val, hdecomp_run, hlogic_val, hwrite_sail⟩
  refine ⟨js', ?_, ?_⟩
  · rw [hrun_eq]
    exact hdecomp_run
  · rw [hwrite_sail, hlogic_val]
    exact congrArg (stateAfterWrite js.sail rd)
      (jolt_lw_bridge js.sail (load_effective_address val imm) halign)

/-- Misaligned case: `jolt_lw` immediately returns
    `Memory_Exception (ea, E_Load_Addr_Align)`. Pure unfolding + `if_pos`. -/
theorem jolt_lw_concrete_misaligned (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_align : load_effective_address val imm &&& 3 ≠ 0)
    :
    (jolt_lw imm rs1 rd).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (load_effective_address val imm), ExceptionType.E_Load_Addr_Align ())) js := by
  unfold jolt_lw
  simp only [liftSail, bind, EStateM.bind, pure,  EStateM.run]
  rw [hrx]
  simp only []
  rw [if_pos h_align]
  rfl

/-- Sail-side `execute_LOAD imm rs1 rd false 4` reduces to
    `stateAfterWrite rd (sign_extend (loaded_word_at ea))` under aligned +
    translate + phys + no-overflow assumptions. -/
theorem execute_LW_reduces (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (hload : LoadReadAssumptions (load_effective_address val imm) 4 js.sail)
    (h_no_ovf : (load_effective_address val imm).toNat + 3 < 2 ^ 64) :
    (execute_LOAD imm rs1 rd false 4).run js.sail =
    .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (loaded_word_at js.sail (load_effective_address val imm)))) := by
  unfold execute_LOAD
  simp only [bind, pure]
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  simp (config := { decide := true }) only []
  simp (config := { decide := true }) only [PreSail.assert, EStateM.bind, pure, EStateM.pure,
       EStateM.run, if_true]
  rw [vmem_read_word_reduces imm rs1 js.sail val hrx hload.aligned hload.translate
      (mem_read_4_eq_loaded_word _ js.sail hcfg h_no_ovf hload.phys)]
  simp only [extend_value, Bool.false_eq_true, if_false, EStateM.bind, EStateM.pure]
  obtain ⟨s', hw⟩ := wX_shape rd
    (sign_extend (m := 64) (loaded_word_at js.sail (load_effective_address val imm)))
    js.sail
  rw [hw]
  simp only [RETIRE_SUCCESS]
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

/-- Aligned equivalence: on an aligned input, `jolt_lw` and `execute_LOAD`
    produce the same state. Combines `jolt_lw_concrete` and
    `execute_LW_reduces`, building `LoadReadAssumptions` from the
    width-4 alignment helpers in `MemoryUtils`. -/
theorem jolt_lw_eq_sail_aligned (imm : BitVec 12)
    (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail)
    (htranslate : BareTranslation (load_effective_address val imm) js.sail)
    (hphys : FlatPhysMem (load_effective_address val imm) 4 js.sail)
    (h_word_no_ovf : (load_effective_address val imm).toNat + 3 < 2 ^ 64)
    (h_align : load_effective_address val imm &&& 3 = 0)
    :
    projectResult ((jolt_lw imm rs1 rd).run js) =
    (execute_LOAD imm rs1 rd false 4).run js.sail := by
  let ea := load_effective_address val imm
  have hload : LoadReadAssumptions (load_effective_address val imm) 4 js.sail := by
    refine
      { aligned := ?_
        translate := htranslate
        phys := hphys }
    refine
      { misalign := ?_
        split := ?_ }
    · simpa [ea] using access_misaligned_4_aligned_false ea h_align
    · simpa [ea] using split_misaligned_aligned_4 ea h_align
  have hjolt_aligned := jolt_lw_concrete imm rs1 rd hrd js hcfg val hrx h_align h_dword_translate h_dword_phys
  have hsail_aligned := execute_LW_reduces imm rs1 rd js hcfg val hrx hload h_word_no_ovf
  rcases hjolt_aligned with ⟨js', hjolt, hjolt_sail⟩
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail, hsail_aligned]

/-- Sail-side `execute_LOAD` on a misaligned input returns the same
    memory-alignment exception as Jolt. Uses
    `access_misaligned_4_unaligned_true` from `MemoryUtils`. -/
theorem execute_LW_misaligned (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (htranslate : BareTranslation (load_effective_address val imm) js.sail)
    (hphys : FlatPhysMem (load_effective_address val imm) 4 js.sail)
    (h_no_ovf : (load_effective_address val imm).toNat + 3 < 2 ^ 64)
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

/-- Misaligned equivalence: on a misaligned input, both Jolt and Sail
    return the same `Memory_Exception`. -/
theorem jolt_lw_eq_sail_misaligned (imm : BitVec 12)
    (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail)
    (htranslate : BareTranslation (load_effective_address val imm) js.sail)
    (hphys : FlatPhysMem (load_effective_address val imm) 4 js.sail)
    (h_word_no_ovf : (load_effective_address val imm).toNat + 3 < 2 ^ 64)
    (h_align : load_effective_address val imm &&& 3 ≠ 0)
    :
    projectResult ((jolt_lw imm rs1 rd).run js) =
    (execute_LOAD imm rs1 rd false 4).run js.sail := by
  let ea := load_effective_address val imm
  have hjolt_misaligned :
      (jolt_lw imm rs1 rd).run js =
        .ok (ExecutionResult.Memory_Exception (Virtaddr ea, ExceptionType.E_Load_Addr_Align ())) js := by
    simpa [ea] using
      (jolt_lw_concrete_misaligned imm rs1 rd hrd js hcfg val hrx h_align)
  have hsail_misaligned :
      (execute_LOAD imm rs1 rd false 4).run js.sail =
        .ok (ExecutionResult.Memory_Exception (Virtaddr ea, ExceptionType.E_Load_Addr_Align ())) js.sail := by
    simpa [ea] using
      (execute_LW_misaligned imm rs1 rd js hcfg val hrx htranslate hphys h_word_no_ovf h_align)
  rw [hjolt_misaligned]
  simp only [projectResult, project]
  symm
  exact hsail_misaligned

/-- **Main theorem.** `jolt_lw = execute_LOAD … false 4` on every input:
    dispatch on alignment. -/
theorem jolt_lw_eq_sail (imm : BitVec 12)
    (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail)
    (htranslate : BareTranslation (load_effective_address val imm) js.sail)
    (hphys : FlatPhysMem (load_effective_address val imm) 4 js.sail)
    (h_word_no_ovf : (load_effective_address val imm).toNat + 3 < 2 ^ 64)
    :
    projectResult ((jolt_lw imm rs1 rd).run js) =
    (execute_LOAD imm rs1 rd false 4).run js.sail := by
  let ea := load_effective_address val imm
  by_cases h_align : ea &&& 3 = 0
  · exact jolt_lw_eq_sail_aligned imm rs1 rd hrd js hcfg val hrx h_dword_translate h_dword_phys htranslate hphys h_word_no_ovf h_align
  · exact jolt_lw_eq_sail_misaligned imm rs1 rd hrd js hcfg val hrx h_dword_translate h_dword_phys htranslate hphys h_word_no_ovf h_align

end LW_main
