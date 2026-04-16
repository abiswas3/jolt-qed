import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Sw
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.StoreDefUtils
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.JoltStoreDefUtils
import Mathlib.Tactic.IntervalCases

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

/-!
# SW: monadic plumbing

This file contains the monadic part of the SW proof.
The pure layers remain in `Sw.lean` and `MemoryWriteReasoning.lean`.

What remains here is the final SW composition layer.
-/

private theorem sw_match_ok_triple_ignore
    (m : EStateM.Result (Error exception) SailJoltState (BitVec 64 × BitVec 64 × BitVec 64)) :
    (match m with
    | EStateM.Result.ok _ s =>
        match vreg_SD 1 2 0 s with
        | EStateM.Result.ok _ s => EStateM.Result.ok RETIRE_SUCCESS s
        | EStateM.Result.error e s => EStateM.Result.error e s
    | EStateM.Result.error e s => EStateM.Result.error e s) =
    (match m with
    | EStateM.Result.ok (_, _, _) js' =>
        match vreg_SD 1 2 0 js' with
        | EStateM.Result.ok _ s => EStateM.Result.ok RETIRE_SUCCESS s
        | EStateM.Result.error e s => EStateM.Result.error e s
    | EStateM.Result.error e s => EStateM.Result.error e s) := by
  cases m <;> rfl

private theorem jolt_sw_run_eq_prefix_then_sd
    (imm : BitVec 12) (rs2 rs1 : regidx) (js : SailJoltState) :
    (jolt_sw imm rs2 rs1).run js =
      match (jolt_sw_compute_splice imm rs2 rs1).run js with
      | .ok (_, _, _) js' =>
          match vreg_SD 1 2 0 js' with
          | .ok _ js'' => .ok RETIRE_SUCCESS js''
          | .error e js'' => .error e js''
      | .error e js' => .error e js' := by
  unfold jolt_sw
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
  cases hres : jolt_sw_compute_splice imm rs2 rs1 js with
  | ok a s =>
      cases a with
      | mk fst snd =>
          cases snd with
          | mk base dword_new =>
              simp
              cases hsd : vreg_SD 1 2 0 s <;> rfl
  | error e s =>
      rfl

-- Under the standard setup assumptions, the projected Jolt execution reduces
-- to storing the spliced dword at the aligned base address.
theorem projectResult_jolt_sw_eq_state_after_dword_store
    (imm : BitVec 12) (rs2 rs1 : regidx) (js : SailJoltState)
    (rs2_val ea base : BitVec 64)
    (hrs1 : ∃ rs1_val : BitVec 64,
      rX_bits rs1 js.sail = .ok rs1_val js.sail ∧
      ea = rs1_val + sign_extend (m := 64) imm)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (hsetup : DwordStoreSetup ea base)
    (hdw : DwordLoadAssumptions base js.sail)
    (hsdwrite :
      vmem_write_addr (Virtaddr base) 8
        (xor_and_xor_splice (loaded_dword_at js.sail base)
          (Sail.BitVec.extractLsb rs2_val 31 0) (((ea - base).toNat) * 8))
        (Store Data) false false false js.sail =
      .ok (Ok true)
        (state_after_dword_store js.sail base
          (xor_and_xor_splice (loaded_dword_at js.sail base)
            (Sail.BitVec.extractLsb rs2_val 31 0) (((ea - base).toNat) * 8))))    
    (hcfg : JoltConfig js.sail) :
    ∃ dword_orig : BitVec 64,
      (∀ k : Nat, k < 8 →
        dword_byte dword_orig k = loaded_byte_at js.sail (base + BitVec.ofNat 64 k)) ∧
      projectResult ((jolt_sw imm rs2 rs1).run js) =
        .ok RETIRE_SUCCESS
          (state_after_dword_store js.sail base
            (xor_and_xor_splice dword_orig (Sail.BitVec.extractLsb rs2_val 31 0)
              ((ea - base).toNat * 8))) := by
  obtain ⟨js', hprefix, hjs'_sail, hvs1, hvs2⟩ :=
    jolt_sw_compute_splice_of_setup imm rs2 rs1 js rs2_val ea base
      hrs1 hrs2 hsetup hdw hcfg
  let dword_orig := loaded_dword_at js.sail base
  refine ⟨dword_orig, ?_, ?_⟩
  · intro k hk
    interval_cases k <;> simp [dword_orig, dword_byte, loaded_dword_at, loaded_byte_at] <;> bv_decide
  · have hsd :
        vreg_SD 1 2 0 js' =
          .ok RETIRE_SUCCESS
            { sail := state_after_dword_store js.sail base
                (xor_and_xor_splice dword_orig (Sail.BitVec.extractLsb rs2_val 31 0)
                  (((ea - base).toNat) * 8)),
              vregs := js'.vregs } := by
      have hsdwrite' :
          vmem_write_addr (Virtaddr (js'.vregs 1 + sign_extend (m := 64) (0 : BitVec 12))) 8
            (js'.vregs 2) (Store Data) false false false js'.sail =
          .ok (Ok true)
            (state_after_dword_store js.sail base
              (xor_and_xor_splice dword_orig (Sail.BitVec.extractLsb rs2_val 31 0)
                (((ea - base).toNat) * 8))) := by
        rw [hjs'_sail, hvs1, hvs2]
        have hzero : sign_extend (m := 64) (0 : BitVec 12) = (0 : BitVec 64) := by decide
        have hzero_addr : base + sign_extend (m := 64) (0 : BitVec 12) = base := by
          rw [hzero]
          bv_decide
        change vmem_write_addr (Virtaddr (base + sign_extend (m := 64) (0 : BitVec 12))) 8
            (xor_and_xor_splice dword_orig (Sail.BitVec.extractLsb rs2_val 31 0)
              (((ea - base).toNat) * 8))
            (Store Data) false false false js.sail =
          .ok (Ok true)
            (state_after_dword_store js.sail base
              (xor_and_xor_splice dword_orig (Sail.BitVec.extractLsb rs2_val 31 0)
                (((ea - base).toNat) * 8)))
        rw [hzero_addr]
        simpa [dword_orig] using hsdwrite
      simpa [hjs'_sail, hvs1, hvs2] using
        (vreg_SD_run_of_write_to_state 1 2 (0 : BitVec 12) js'
          (state_after_dword_store js.sail base
            (xor_and_xor_splice dword_orig (Sail.BitVec.extractLsb rs2_val 31 0)
              (((ea - base).toNat) * 8))) hsdwrite')
    have hrun :
        (jolt_sw imm rs2 rs1).run js =
          .ok RETIRE_SUCCESS
            { sail := state_after_dword_store js.sail base
                (xor_and_xor_splice dword_orig (Sail.BitVec.extractLsb rs2_val 31 0)
                  (((ea - base).toNat) * 8)),
              vregs := js'.vregs } := by
      rw [jolt_sw_run_eq_prefix_then_sd]
      rw [hprefix]
      simp only
      rw [hsd]
    unfold projectResult
    rw [hrun]
    rfl

-- With the aligned dword setup made explicit, the remaining SW proof is a
-- clean composition of the pure splice lemmas with the two monadic reductions.
theorem jolt_sw_eq_sail_of_setup
    (imm : BitVec 12) (rs2 rs1 : regidx) (js : SailJoltState)
    (rs2_val ea base : BitVec 64)
    (hrs1 : ∃ rs1_val : BitVec 64,
      rX_bits rs1 js.sail = .ok rs1_val js.sail ∧
      ea = rs1_val + sign_extend (m := 64) imm)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (hsetup : DwordStoreSetup ea base)
    (hdw : DwordLoadAssumptions base js.sail)
    (hcfg : JoltConfig js.sail) :
    (hwrite :
      vmem_write rs1 (sign_extend (m := 64) imm) 4 (Sail.BitVec.extractLsb rs2_val 31 0)
        (Store Data) false false false js.sail =
      .ok (Ok true)
        (state_after_word_store js.sail ea (Sail.BitVec.extractLsb rs2_val 31 0))) →
    (hsdwrite :
      vmem_write_addr (Virtaddr base) 8
        (xor_and_xor_splice (loaded_dword_at js.sail base)
          (Sail.BitVec.extractLsb rs2_val 31 0) (((ea - base).toNat) * 8))
        (Store Data) false false false js.sail =
      .ok (Ok true)
        (state_after_dword_store js.sail base
          (xor_and_xor_splice (loaded_dword_at js.sail base)
            (Sail.BitVec.extractLsb rs2_val 31 0) (((ea - base).toNat) * 8)))) →
    projectResult ((jolt_sw imm rs2 rs1).run js) =
    (execute_STORE imm rs2 rs1 4).run js.sail := by
  intro hwrite hsdwrite
  obtain ⟨dword_orig, hload, hjolt⟩ :=
    projectResult_jolt_sw_eq_state_after_dword_store
      imm rs2 rs1 js rs2_val ea base hrs1 hrs2 hsetup hdw hsdwrite hcfg
  have hsail :=
    execute_STORE_word_eq_state_after_word_store
      imm rs2 rs1 js rs2_val ea base hrs1 hrs2 hsetup hcfg hwrite
  let off := (ea - base).toNat
  let word_val := Sail.BitVec.extractLsb rs2_val 31 0
  let spliced := xor_and_xor_splice dword_orig word_val (8 * off)
  have hoff : off = 0 ∨ off = 4 := by
    simpa using sw_splice_offset_cases ea base hsetup
  have hspec :
      IsWordSplice dword_orig spliced word_val off := by
    simpa [off, word_val, spliced] using
      sw_splice_spec dword_orig word_val off hoff
  have hpop : ∀ k : Nat, k < 8 → js.sail.mem.get? (base.toNat + k) ≠ none := by
    intro k hk
    exact hcfg.mem_populated (base.toNat + k)
  have hmem :
      (state_after_dword_store js.sail base spliced).mem =
      (state_after_word_store js.sail ea word_val).mem := by
    dsimp [IsWordSplice] at hspec
    exact dword_store_splice_eq_word_store_populated
      js.sail ea base word_val dword_orig spliced
      hsetup hpop hload hspec.1 hspec.2
  have hstate :
      state_after_dword_store js.sail base spliced =
      state_after_word_store js.sail ea word_val := by
    simpa [state_after_dword_store, state_after_word_store] using hmem
  have hstate' :
      state_after_dword_store js.sail base
        (xor_and_xor_splice dword_orig (Sail.BitVec.extractLsb rs2_val 31 0) ((ea - base).toNat * 8)) =
      state_after_word_store js.sail ea (Sail.BitVec.extractLsb rs2_val 31 0) := by
    simpa [off, word_val, spliced, Nat.mul_comm] using hstate
  rw [hjolt, hsail, hstate']

-- Under the explicit SW setup assumptions, the Jolt decomposition agrees with
-- Sail's native word store.
theorem jolt_sw_eq_sail (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState)
    (rs2_val ea base : BitVec 64)
    (hrs1 : ∃ rs1_val : BitVec 64,
      rX_bits rs1 js.sail = .ok rs1_val js.sail ∧
      ea = rs1_val + sign_extend (m := 64) imm)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (hsetup : DwordStoreSetup ea base)
    (hdw : DwordLoadAssumptions base js.sail)
    (hcfg : JoltConfig js.sail)
    (hwrite :
      vmem_write rs1 (sign_extend (m := 64) imm) 4 (Sail.BitVec.extractLsb rs2_val 31 0)
        (Store Data) false false false js.sail =
      .ok (Ok true)
        (state_after_word_store js.sail ea (Sail.BitVec.extractLsb rs2_val 31 0)))
    (hsdwrite :
      vmem_write_addr (Virtaddr base) 8
        (xor_and_xor_splice (loaded_dword_at js.sail base)
          (Sail.BitVec.extractLsb rs2_val 31 0) (((ea - base).toNat) * 8))
        (Store Data) false false false js.sail =
      .ok (Ok true)
        (state_after_dword_store js.sail base
          (xor_and_xor_splice (loaded_dword_at js.sail base)
            (Sail.BitVec.extractLsb rs2_val 31 0) (((ea - base).toNat) * 8)))) :
    projectResult ((jolt_sw imm rs2 rs1).run js) =
    (execute_STORE imm rs2 rs1 4).run js.sail := by
  exact jolt_sw_eq_sail_of_setup
    imm rs2 rs1 js rs2_val ea base hrs1 hrs2 hsetup hdw hcfg hwrite hsdwrite

end
