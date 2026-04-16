import JoltBytecode.EmbeddedSailJoltState.Defs
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Sw
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadDefUtils
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.MonadReduction

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

private theorem shift_bits_left_eq_shiftLeft_nat (x : BitVec 64) (sh : BitVec 6) :
    shift_bits_left x sh = x <<< sh.toNat := by
  rfl

/-!
# Shared Jolt store-definition helpers

These helpers isolate the Jolt-side execution plumbing for store instructions.
The goal is to reduce the inline sequence to explicit register and memory
objects, so the instruction proof can return quickly to the pure splice and
hashmap layers.
-/

private theorem setWidth6_eq_extractLsb_5_0 (v : BitVec 64) :
    v.setWidth 6 = Sail.BitVec.extractLsb v 5 0 := by
  unfold Sail.BitVec.extractLsb
  ext i
  simp

-- The shift computed by the SW prefix is exactly the byte offset within the
-- dword, multiplied by 8.
theorem sw_prefix_shift_eq (ea base : BitVec 64) (hsetup : DwordStoreSetup ea base) :
    Sail.BitVec.extractLsb (shift_bits_left ea (3 : BitVec 6)) 5 0 =
      BitVec.ofNat 6 (((ea - base).toNat) * 8) := by
  rw [← setWidth6_eq_extractLsb_5_0 (shift_bits_left ea (3 : BitVec 6))]
  rcases sw_splice_offset_cases ea base hsetup with hoff | hoff
  · have hsub0 : ea - base = (0 : BitVec 64) := by
      apply BitVec.eq_of_toNat_eq
      simpa using hoff
    have hea0 : ea = base := by
      have := hsub0
      bv_decide
    rw [hoff, hea0, hsetup.base_is_aligned]
    unfold shift_bits_left
    bv_decide
  · have hsub4 : ea - base = (4 : BitVec 64) := by
      apply BitVec.eq_of_toNat_eq
      simpa using hoff
    have hea4 : ea = base + (4 : BitVec 64) := by
      have := hsub4
      bv_decide
    rw [hoff, hea4, hsetup.base_is_aligned]
    unfold shift_bits_left
    bv_decide

private theorem xor_and_xor_splice_eq_sequence
    (dword_orig rs2_val : BitVec 64) (off : Nat) (hoff : off = 0 ∨ off = 4) :
    dword_orig ^^^
        ((dword_orig ^^^ shift_bits_left rs2_val (BitVec.ofNat 6 (off * 8))) &&&
          shift_bits_left (0x00000000FFFFFFFF : BitVec 64) (BitVec.ofNat 6 (off * 8))) =
      xor_and_xor_splice dword_orig (Sail.BitVec.extractLsb rs2_val 31 0) (off * 8) := by
  rcases hoff with rfl | rfl
  · simp [xor_and_xor_splice, shift_bits_left_eq_shiftLeft_nat, Sail.BitVec.extractLsb]
    bv_decide
  · simp [xor_and_xor_splice, shift_bits_left_eq_shiftLeft_nat, Sail.BitVec.extractLsb]
    bv_decide

private theorem SailJoltState.ext'
    {s₁ s₂ : SailJoltState}
    (hsail : s₁.sail = s₂.sail)
    (hvregs : s₁.vregs = s₂.vregs) :
    s₁ = s₂ := by
  cases s₁
  cases s₂
  cases hsail
  cases hvregs
  rfl

-- Under the explicit SW setup assumptions, the Jolt prefix computes the
-- spliced dword and leaves it in virtual register 2.
theorem jolt_sw_compute_splice_of_setup
    (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState)
    (rs2_val ea base : BitVec 64)
    (hrs1 : ∃ rs1_val : BitVec 64,
      rX_bits rs1 js.sail = .ok rs1_val js.sail ∧
      ea = rs1_val + sign_extend (m := 64) imm)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (hsetup : DwordStoreSetup ea base)
    (hdw : DwordLoadAssumptions base js.sail)
    (hcfg : JoltConfig js.sail) :
    ∃ js' : SailJoltState,
      (jolt_sw_compute_splice imm rs2 rs1).run js =
        .ok (ea, base,
          xor_and_xor_splice (loaded_dword_at js.sail base)
            (Sail.BitVec.extractLsb rs2_val 31 0)
            (((ea - base).toNat) * 8)) js' ∧
      js'.sail = js.sail ∧
      js'.vregs 1 = base ∧
      js'.vregs 2 =
        xor_and_xor_splice (loaded_dword_at js.sail base)
          (Sail.BitVec.extractLsb rs2_val 31 0)
          (((ea - base).toNat) * 8) := by
  obtain ⟨rs1_val, hrs1_read, hea⟩ := hrs1
  let shift64 := shift_bits_left ea (3 : BitVec 6)
  let shift6 := Sail.BitVec.extractLsb shift64 5 0
  let dword_orig := loaded_dword_at js.sail base
  let word_val := Sail.BitVec.extractLsb rs2_val 31 0
  let mask := shift_bits_left (0x00000000FFFFFFFF : BitVec 64) shift6
  let shifted_word := shift_bits_left rs2_val shift6
  let masked_xor := (dword_orig ^^^ shifted_word) &&& mask
  let spliced := xor_and_xor_splice dword_orig word_val (((ea - base).toNat) * 8)
  let js0 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = 0 then ea else js.vregs r }
  let js1 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = 1 then base else js0.vregs r }
  let js2 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = 2 then dword_orig else js1.vregs r }
  let js3 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = 0 then shift64 else js2.vregs r }
  let js4 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = 3 then 0 else js3.vregs r }
  let js5 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = 3 then (-1 : BitVec 64) else js4.vregs r }
  let js6 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = 3 then (0x00000000FFFFFFFF : BitVec 64) else js5.vregs r }
  let js7 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = 3 then mask else js6.vregs r }
  let js8 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = 0 then shifted_word else js7.vregs r }
  let js9 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = 0 then dword_orig ^^^ shifted_word else js8.vregs r }
  let js10 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = 0 then masked_xor else js9.vregs r }
  let js11 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = 2 then spliced else js10.vregs r }
  have hw0 : writeVReg 0 ea js = .ok () js0 := by
    unfold writeVReg js0
    simp [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  have hneg8 : sign_extend (m := 64) (-8 : BitVec 12) = (-8 : BitVec 64) := by decide
  have hneg1 : sign_extend (m := 64) (-1 : BitVec 12) = (-1 : BitVec 64) := by decide
  have hbase : js0.vregs 0 &&& sign_extend (m := 64) (-8 : BitVec 12) = base := by
    rw [hneg8]
    simp [js0, hsetup.base_is_aligned]
  have handi : vreg_ANDI 1 0 (-8 : BitVec 12) js0 = .ok RETIRE_SUCCESS js1 := by
    rw [vreg_ANDI_run 1 0 (-8 : BitVec 12) js0]
    congr 1
    exact SailJoltState.ext' rfl <| by
      funext r
      by_cases hr : r = 1
      · subst hr
        simpa [js1] using hbase
      · change (if r = 1 then js0.vregs 0 &&& sign_extend (m := 64) (-8 : BitVec 12) else js0.vregs r) =
            (if r = 1 then base else js0.vregs r)
        split_ifs with h <;> try contradiction
        rfl
  have hvs1 : js1.vregs 1 = base := by
    simp [js1, hbase]
  have hld : vreg_LD 2 1 0 js1 = .ok RETIRE_SUCCESS js2 := by
    simpa [js2, dword_orig] using
      (vreg_LD_run_of_dword_assumptions 2 1 js1 base hvs1 hcfg hdw)
  have hslli : vreg_SLLI 0 0 3 js2 = .ok RETIRE_SUCCESS js3 := by
    change vreg_SLLI 0 0 3 js2 = .ok RETIRE_SUCCESS
      { sail := js2.sail
        vregs := fun r => if r = 0 then shift_bits_left (js2.vregs 0) (3 : BitVec 6) else js2.vregs r }
    simpa [js2, js3, shift64] using (vreg_SLLI_run 0 0 3 js2)
  have hw3 : writeVReg 3 0 js3 = .ok () js4 := by
    unfold writeVReg js4
    simp [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, js3]
  have hori : vreg_ORI 3 3 (-1 : BitVec 12) js4 = .ok RETIRE_SUCCESS js5 := by
    rw [vreg_ORI_run 3 3 (-1 : BitVec 12) js4]
    congr 1
    exact SailJoltState.ext' rfl <| by
      funext r
      by_cases hr : r = 3
      · subst hr
        rw [hneg1]
        simp [js4, js5]
      · change (if r = 3 then js4.vregs 3 ||| sign_extend (m := 64) (-1 : BitVec 12) else js4.vregs r) =
            (if r = 3 then (-1 : BitVec 64) else js4.vregs r)
        split_ifs with h <;> try contradiction
        rfl
  have hsrli : vreg_SRLI 3 3 32 js5 = .ok RETIRE_SUCCESS js6 := by
    rw [vreg_SRLI_run 3 3 32 js5]
    congr 1
    exact SailJoltState.ext' rfl <| by
      funext r
      by_cases hr : r = 3
      · subst hr
        simp [js5, js6]
        unfold shift_bits_right
        bv_decide
      · change (if r = 3 then shift_bits_right (js5.vregs 3) (32 : BitVec 6) else js5.vregs r) =
            (if r = 3 then (0x00000000FFFFFFFF : BitVec 64) else js5.vregs r)
        split_ifs with h <;> try contradiction
        rfl
  have hsll_mask : vreg_SLL 3 3 0 js6 = .ok RETIRE_SUCCESS js7 := by
    change vreg_SLL 3 3 0 js6 = .ok RETIRE_SUCCESS
      { sail := js6.sail
        vregs := fun r =>
          if r = 3 then shift_bits_left (js6.vregs 3) (Sail.BitVec.extractLsb (js6.vregs 0) 5 0)
          else js6.vregs r }
    simpa [js6, js7, mask, shift6, shift64] using (vreg_SLL_run 3 3 0 js6)
  have hread_v0 : readVReg 0 js7 = .ok shift64 js7 := by
    simpa [js7, js6, js5, js4, js3, shift64] using (readVReg_run 0 js7)
  have hw_shifted : writeVReg 0 (shift_bits_left rs2_val shift6) js7 = .ok () js8 := by
    unfold writeVReg js8
    simp [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, shifted_word, js7]
  have hxor1 : vreg_XOR 0 2 0 js8 = .ok RETIRE_SUCCESS js9 := by
    change vreg_XOR 0 2 0 js8 = .ok RETIRE_SUCCESS
      { sail := js8.sail
        vregs := fun r => if r = 0 then js8.vregs 2 ^^^ js8.vregs 0 else js8.vregs r }
    simpa [js8, js9, dword_orig, shifted_word] using (vreg_XOR_run 0 2 0 js8)
  have hand1 : vreg_AND 0 0 3 js9 = .ok RETIRE_SUCCESS js10 := by
    change vreg_AND 0 0 3 js9 = .ok RETIRE_SUCCESS
      { sail := js9.sail
        vregs := fun r => if r = 0 then js9.vregs 0 &&& js9.vregs 3 else js9.vregs r }
    simpa [js9, js10, masked_xor, dword_orig, shifted_word, mask] using (vreg_AND_run 0 0 3 js9)
  have hxor2 : vreg_XOR 2 2 0 js10 = .ok RETIRE_SUCCESS js11 := by
    have hshift6 : shift6 = BitVec.ofNat 6 (((ea - base).toNat) * 8) := by
      simpa [shift6, shift64] using sw_prefix_shift_eq ea base hsetup
    have hoff : ((ea - base).toNat) = 0 ∨ ((ea - base).toNat) = 4 := by
      simpa using sw_splice_offset_cases ea base hsetup
    have hspliced : dword_orig ^^^ masked_xor = spliced := by
      dsimp [masked_xor, shifted_word, mask, spliced]
      rw [hshift6]
      simpa using xor_and_xor_splice_eq_sequence dword_orig rs2_val ((ea - base).toNat) hoff
    rw [vreg_XOR_run 2 2 0 js10]
    congr 1
    exact SailJoltState.ext' rfl <| by
      funext r
      by_cases hr : r = 2
      · subst hr
        simpa [js10, js11] using hspliced
      · change (if r = 2 then js10.vregs 2 ^^^ js10.vregs 0 else js10.vregs r) =
            (if r = 2 then spliced else js10.vregs r)
        split_ifs with h <;> try contradiction
        rfl
  have hread_base : readVReg 1 js11 = .ok base js11 := by
    simpa [js11, js10, js9, js8, js7, js6, js5, js4, js3, js2, js1] using (readVReg_run 1 js11)
  have hread_dword : readVReg 2 js11 = .ok spliced js11 := by
    simpa [js11, spliced] using (readVReg_run 2 js11)
  have hword' : ¬ (rs1_val + sign_extend (m := 64) imm &&& 3 ≠ 0) := by
    simpa [hea] using hsetup.word_aligned
  have hw0' : writeVReg 0 (rs1_val + sign_extend (m := 64) imm) js = .ok () js0 := by
    simpa [hea] using hw0
  have hrs2' : liftSail (rX_bits rs2) js7 = .ok rs2_val js7 := by
    unfold liftSail
    rw [hrs2]
  refine ⟨js11, ?_, rfl, ?_, ?_⟩
  · simp only [jolt_sw_compute_splice, liftSail, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
    rw [hrs1_read]
    simp only [EStateM.bind, EStateM.pure]
    rw [if_neg hword']
    simp only [EStateM.bind]
    rw [hw0']
    simp only [EStateM.bind, EStateM.pure]
    rw [handi]
    simp only [EStateM.bind, EStateM.pure]
    rw [hld]
    simp only [RETIRE_SUCCESS]
    simp only [EStateM.bind, hslli, EStateM.pure]
    simp only [EStateM.bind, hw3, EStateM.pure]
    simp only [EStateM.bind, hori, EStateM.pure]
    simp only [EStateM.bind, hsrli, EStateM.pure]
    simp only [EStateM.bind, hsll_mask, EStateM.pure]
    rw [hrs2']
    simp only [EStateM.bind, EStateM.pure]
    rw [hread_v0]
    simp only [EStateM.bind, EStateM.pure]
    rw [hw_shifted]
    simp only [EStateM.bind, EStateM.pure]
    rw [hxor1]
    simp only [EStateM.bind, EStateM.pure]
    rw [hand1]
    simp only [EStateM.bind, EStateM.pure]
    rw [hxor2]
    simp only [RETIRE_SUCCESS]
    rw [hread_base]
    simp only [EStateM.bind, EStateM.pure]
    rw [hread_dword]
    simp [hea, spliced, dword_orig, word_val]
  · simp [js11, js10, js9, js8, js7, js6, js5, js4, js3, js2, js1]
  · simp [js11, spliced, dword_orig, word_val]

end
