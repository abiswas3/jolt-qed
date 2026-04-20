import JoltBytecode.EmbeddedSailJoltState.Defs
import JoltBytecode.EmbeddedSailJoltState.MemoryUtils
import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadDefUtils
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadFamily.PhaseHelpers
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadFamily.DwordArithmetic
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

namespace LH_main

/-!
# LH: Jolt load-halfword (signed) top-level equivalence

From `tracer/src/instruction/lh.rs::inline_sequence_64`:

    VirtualAssertHalfwordAlignment rs1, imm
    ADDI  v0, rs1, imm
    ANDI  v1, v0, -8
    LD    v1, v1, 0
    XORI  v0, v0, 6
    SLLI  v0, v0, 3
    SLL   v1, v1, v0
    SRAI  rd, v1, 48

LH is a hybrid of LW and LB:
* **Has an alignment check** (`addr & 1 = 0`) like LW — so the program
  uses the same "fuse `VirtualAssert…Alignment` with the initial ADDI"
  trick as `jolt_lw`, opening with an explicit
  `let base ← liftSail (rX_bits rs1); if ea & 1 ≠ 0 then … else …`.
* **Writes via SLL+SRAI** like LB — so after the alignment passes, the
  remaining lines use `vreg_ANDI / vreg_LD / vreg_XORI / vreg_SLLI /
  vreg_SLL / vreg_SRAI_to_real`, one Lean line per bytecode line, with
  `XORI v0, v0, 6` and `SRAI rd, v1, 48` in place of LB's `7` / `56`.

## Current status

* Closed using existing infra: `jolt_lh` (def), `jolt_lh_concrete_misaligned`,
  `execute_LH_reduces`.
* Sorried (need helpers not yet landed):
  * `jolt_lh_bridge` — needs `sll_srai_extracts_halfword` + `loaded_halfword_in_dword`
    to be added to `DwordArithmetic.lean`.
  * `jolt_lh_run_eq_decomposed`, `jolt_lh_concrete` — need `LH_decomposed.lean`.
  * `execute_LH_misaligned`, `jolt_lh_eq_sail_aligned`,
    `jolt_lh_eq_sail_misaligned` — need `access_misaligned_2_{aligned_false,
    unaligned_true}` / `split_misaligned_aligned_2` to be added to
    `MemoryUtils.lean`.
  * `jolt_lh_eq_sail` — dispatches on alignment; composes the two sorried
    aligned/misaligned arms.
-/

/-- The original Jolt LH program. Same fused `VirtualAssertHalfwordAlignment
    + ADDI v0, rs1, imm` trick as `jolt_lw` (one real-register read,
    followed by an early-return `if` for the alignment guard). After the
    guard, each Lean line mirrors one line of the tracer bytecode using
    the boundary-crossing combinators. -/
def jolt_lh (imm : BitVec 12) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  -- VirtualAssertHalfwordAlignment rs1, imm + ADDI v0, rs1, imm (fused)
  let base ← liftSail (rX_bits rs1)
  let ea := base + sign_extend (m := 64) imm
  if ea &&& 1 ≠ 0 then
    pure (ExecutionResult.Memory_Exception
      (Virtaddr ea, ExceptionType.E_Load_Addr_Align ()))
  else do
    writeVReg 0 ea                                        -- (ADDI v0, rs1, imm writes ea)
    let _ ← vreg_ANDI 1 0 (-8 : BitVec 12)                -- ANDI v1, v0, -8
    match ← vreg_LD 1 1 0 with                             -- LD   v1, v1, 0
    | .Retire_Success () =>
        let _ ← vreg_XORI 0 0 6                            -- XORI v0, v0, 6
        let _ ← vreg_SLLI 0 0 3                            -- SLLI v0, v0, 3
        let _ ← vreg_SLL 1 1 0                             -- SLL  v1, v1, v0
        vreg_SRAI_to_real rd 1 (48 : BitVec 6)             -- SRAI rd, v1, 48
    | other => pure other

/-- **Bridge lemma for LH.** The Jolt logic-phase computation (XOR with 6,
    SLL by 3, SLL the dword, arith-shift-right by 48) equals the Sail-
    side direct halfword load sign-extended to 64 bits. Requires halfword
    alignment `halign : addr & 1 = 0`. Pure bit-vector algebra — combines
    `sll_srai_extracts_halfword` with `loaded_halfword_in_dword`,
    mirroring `jolt_lw_bridge`'s shape. -/
theorem jolt_lh_bridge (s : SailState) (addr : BitVec 64)
    (halign : addr &&& 1 = 0) :
    (let dword     := loaded_dword_at s (addr &&& (-8 : BitVec 64))
     let xor_addr  := addr ^^^ (6 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6   := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted   := shift_bits_left dword shift_6
     shift_bits_right_arith shifted (48 : BitVec 6))
    = sign_extend (m := 64) (loaded_halfword_at s addr) := by
  simp only [sll_srai_extracts_halfword _ _ halign, ← loaded_halfword_in_dword _ _ halign]

-- ============================================================================
-- Top-level LH ↔ Sail equivalence theorems
-- ============================================================================

/-- `jolt_lh` and `jolt_lh_decomposed` produce the same final state on a
    halfword-aligned input. Both have the same load / logic / write
    shape once the alignment guard passes and LB's reused phase + LH's
    write phase are unfolded. -/
theorem jolt_lh_run_eq_decomposed (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState) (val : BitVec 64)
    (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (halign : (val + sign_extend (m := 64) imm) &&& 1 = 0)
    :
    (jolt_lh imm rs1 rd).run js = (jolt_lh_decomposed imm rs1 rd).run js := by
  have h8 : sign_extend (m := 64) (-8 : BitVec 12) = (-8 : BitVec 64) := by decide
  unfold jolt_lh jolt_lh_decomposed LB_main.jolt_lb_load_phase vreg_ANDI
  simp only [liftSail, bind, EStateM.bind, pure, EStateM.pure, EStateM.run, h8]
  rw [hrx]
  simp only []
  rw [if_neg (by simpa using halign)]
  rfl

/-- Aligned case: `jolt_lh` succeeds and leaves `rd` holding
    `sign_extend (loaded_halfword_at js.sail ea)`. Composes
    `jolt_lh_decomposed_writes_logic_value` with `jolt_lh_bridge` via
    `congrArg`, same pattern as `jolt_lw_concrete` and `jolt_lb_concrete`. -/
theorem jolt_lh_concrete (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (halign : load_effective_address val imm &&& 1 = 0)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail) :
    ∃ js' : SailJoltState,
      (jolt_lh imm rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (loaded_halfword_at js.sail (load_effective_address val imm))) := by
  have hrun_eq :
      (jolt_lh imm rs1 rd).run js = (jolt_lh_decomposed imm rs1 rd).run js := by
    simpa using jolt_lh_run_eq_decomposed imm rs1 rd js val hrx
      (by simpa [load_effective_address] using halign)
  rcases jolt_lh_decomposed_writes_logic_value imm rs1 rd js val
      hrd hcfg hrx h_dword_translate h_dword_phys with
    ⟨js', logic_val, hdecomp_run, hlogic_val, hwrite_sail⟩
  refine ⟨js', ?_, ?_⟩
  · rw [hrun_eq]
    exact hdecomp_run
  · rw [hwrite_sail, hlogic_val]
    exact congrArg (stateAfterWrite js.sail rd)
      (jolt_lh_bridge js.sail (load_effective_address val imm) halign)

/-- Misaligned case: `jolt_lh` immediately returns
    `Memory_Exception (ea, E_Load_Addr_Align)`. Pure unfolding + `if_pos`,
    analogous to `jolt_lw_concrete_misaligned`. -/
theorem jolt_lh_concrete_misaligned (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_align : load_effective_address val imm &&& 1 ≠ 0)
    :
    (jolt_lh imm rs1 rd).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (load_effective_address val imm), ExceptionType.E_Load_Addr_Align ())) js := by
  unfold jolt_lh
  simp only [liftSail, bind, EStateM.bind, pure, EStateM.run]
  rw [hrx]
  simp only []
  rw [if_pos h_align]
  rfl

/-- Sail-side `execute_LOAD imm rs1 rd false 2` reduces to
    `stateAfterWrite rd (sign_extend (loaded_halfword_at ea))` under the
    aligned + translate + phys + no-overflow assumptions. Width-2
    analogue of `execute_LW_reduces`. -/
theorem execute_LH_reduces (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (hload : LoadReadAssumptions (load_effective_address val imm) 2 js.sail)
    (h_no_ovf : (load_effective_address val imm).toNat + 1 < 2 ^ 64) :
    (execute_LOAD imm rs1 rd false 2).run js.sail =
    .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (loaded_halfword_at js.sail (load_effective_address val imm)))) := by
  unfold execute_LOAD
  simp only [bind, pure]
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  simp (config := { decide := true }) only []
  simp (config := { decide := true }) only [PreSail.assert, EStateM.bind, pure, EStateM.pure,
       EStateM.run, if_true]
  rw [vmem_read_halfword_reduces imm rs1 js.sail val hrx hload.aligned hload.translate
      (mem_read_2_eq_loaded_halfword _ js.sail hcfg h_no_ovf hload.phys)]
  simp only [extend_value, Bool.false_eq_true, if_false, EStateM.bind, EStateM.pure]
  obtain ⟨s', hw⟩ := wX_shape rd
    (sign_extend (m := 64) (loaded_halfword_at js.sail (load_effective_address val imm)))
    js.sail
  rw [hw]
  simp only [RETIRE_SUCCESS]
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

/-- Aligned equivalence: on an aligned input, `jolt_lh` and `execute_LOAD`
    produce the same state. Combines `jolt_lh_concrete` and
    `execute_LH_reduces`, building `LoadReadAssumptions … 2` from the
    width-2 alignment helpers in `MemoryUtils`. -/
theorem jolt_lh_eq_sail_aligned (imm : BitVec 12)
    (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail)
    (htranslate : BareTranslation (load_effective_address val imm) js.sail)
    (hphys : FlatPhysMem (load_effective_address val imm) 2 js.sail)
    (h_half_no_ovf : (load_effective_address val imm).toNat + 1 < 2 ^ 64)
    (h_align : load_effective_address val imm &&& 1 = 0)
    :
    projectResult ((jolt_lh imm rs1 rd).run js) =
    (execute_LOAD imm rs1 rd false 2).run js.sail := by
  let ea := load_effective_address val imm
  have hload : LoadReadAssumptions (load_effective_address val imm) 2 js.sail := by
    refine
      { aligned := ?_
        translate := htranslate
        phys := hphys }
    refine
      { misalign := ?_
        split := ?_ }
    · simpa [ea] using access_misaligned_2_aligned_false ea h_align
    · simpa [ea] using split_misaligned_aligned_2 ea h_align
  have hjolt_aligned := jolt_lh_concrete imm rs1 rd hrd js hcfg val hrx h_align h_dword_translate h_dword_phys
  have hsail_aligned := execute_LH_reduces imm rs1 rd js hcfg val hrx hload h_half_no_ovf
  rcases hjolt_aligned with ⟨js', hjolt, hjolt_sail⟩
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail, hsail_aligned]

/-- Sail-side `execute_LOAD` on a misaligned input returns the same
    memory-alignment exception as Jolt. Width-2 variant of
    `execute_LW_misaligned`, using `access_misaligned_2_unaligned_true`. -/
theorem execute_LH_misaligned (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (htranslate : BareTranslation (load_effective_address val imm) js.sail)
    (hphys : FlatPhysMem (load_effective_address val imm) 2 js.sail)
    (h_no_ovf : (load_effective_address val imm).toNat + 1 < 2 ^ 64)
    (h_align : load_effective_address val imm &&& 1 ≠ 0)
    :
    (execute_LOAD imm rs1 rd false 2).run js.sail =
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
      access_causes_misaligned_exception (Virtaddr ea) 2 false = true := by
    simpa [ea] using access_misaligned_2_unaligned_true ea h_align
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
        ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
        ExceptT.pure, ExceptT.lift,
        MonadLift.monadLift, liftM, monadLift, Functor.map,
        ext_data_get_addr, hrx,
        vmem_read_addr, hmis, ea]
  rfl

/-- Misaligned equivalence: composes `jolt_lh_concrete_misaligned` with
    `execute_LH_misaligned`. The latter is sorried, so this inherits that
    sorry. -/
theorem jolt_lh_eq_sail_misaligned (imm : BitVec 12)
    (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail)
    (htranslate : BareTranslation (load_effective_address val imm) js.sail)
    (hphys : FlatPhysMem (load_effective_address val imm) 2 js.sail)
    (h_half_no_ovf : (load_effective_address val imm).toNat + 1 < 2 ^ 64)
    (h_align : load_effective_address val imm &&& 1 ≠ 0)
    :
    projectResult ((jolt_lh imm rs1 rd).run js) =
    (execute_LOAD imm rs1 rd false 2).run js.sail := by
  let ea := load_effective_address val imm
  have hjolt_misaligned :
      (jolt_lh imm rs1 rd).run js =
        .ok (ExecutionResult.Memory_Exception (Virtaddr ea, ExceptionType.E_Load_Addr_Align ())) js := by
    simpa [ea] using
      (jolt_lh_concrete_misaligned imm rs1 rd hrd js hcfg val hrx h_align)
  have hsail_misaligned :
      (execute_LOAD imm rs1 rd false 2).run js.sail =
        .ok (ExecutionResult.Memory_Exception (Virtaddr ea, ExceptionType.E_Load_Addr_Align ())) js.sail := by
    simpa [ea] using
      (execute_LH_misaligned imm rs1 rd js hcfg val hrx htranslate hphys h_half_no_ovf h_align)
  rw [hjolt_misaligned]
  simp only [projectResult, project]
  symm
  exact hsail_misaligned

/-- **Main theorem.** `jolt_lh = execute_LOAD … false 2` on every input:
    dispatch on alignment. Top-level proof script is complete; the
    underlying aligned/misaligned arms inherit the sorries above. -/
theorem jolt_lh_eq_sail (imm : BitVec 12)
    (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail)
    (htranslate : BareTranslation (load_effective_address val imm) js.sail)
    (hphys : FlatPhysMem (load_effective_address val imm) 2 js.sail)
    (h_half_no_ovf : (load_effective_address val imm).toNat + 1 < 2 ^ 64)
    :
    projectResult ((jolt_lh imm rs1 rd).run js) =
    (execute_LOAD imm rs1 rd false 2).run js.sail := by
  let ea := load_effective_address val imm
  by_cases h_align : ea &&& 1 = 0
  · exact jolt_lh_eq_sail_aligned imm rs1 rd hrd js hcfg val hrx h_dword_translate h_dword_phys htranslate hphys h_half_no_ovf h_align
  · exact jolt_lh_eq_sail_misaligned imm rs1 rd hrd js hcfg val hrx h_dword_translate h_dword_phys htranslate hphys h_half_no_ovf h_align

end LH_main
