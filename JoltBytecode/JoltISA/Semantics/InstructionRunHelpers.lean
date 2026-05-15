import JoltBytecode.JoltISA.Semantics.RegisterOps
import JoltBytecode.JoltISA.Semantics.StateLemmas
import JoltBytecode.JoltISA.Semantics.Instructions

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Instruction run helpers

These helpers are generic facts about `JoltISA.execInstr` runs. They are not
owned by any instruction-equivalence family.

The `_run_ex` lemmas package the concrete post-state with the usual
virtual-register lookup and preservation facts. They are useful for long
straight-line expansions, including advice-backed DIV/REM programs.
-/

/-- `VirtualAdvice` writes advice to a virtual register. -/
theorem vreg_advice_run (vd : BitVec 7) (advice : BitVec 64) (js : SailJoltState) :
    (JoltISA.execInstr (.VirtualAdvice vd advice)).run js = .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r => if r = vd then advice else js.vregs r } :=
  JoltISA.virtual_advice_run vd advice js

/-- `MULH` on virtual registers writes the signed high half. -/
theorem vreg_MULH_run (vd vs1 vs2 : BitVec 7) (js : SailJoltState) :
    (JoltISA.execInstr (.MULH (.vreg vd) (.vreg vs1) (.vreg vs2))).run js =
      .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r => if r = vd then mulhs (js.vregs vs1) (js.vregs vs2)
                          else js.vregs r } :=
  JoltISA.mulh_run_vreg_vreg_vreg vd vs1 vs2 js

/-- `MUL` on virtual registers writes the low 64 bits. -/
theorem vreg_MUL_run (vd vs1 vs2 : BitVec 7) (js : SailJoltState) :
    (JoltISA.execInstr (.MUL (.vreg vd) (.vreg vs1) (.vreg vs2))).run js =
      .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r => if r = vd then js.vregs vs1 * js.vregs vs2
                          else js.vregs r } :=
  JoltISA.mul_run_vreg_vreg_vreg vd vs1 vs2 js

/-- `SRAI` on virtual registers writes an arithmetic right shift. -/
theorem vreg_SRAI_run (vd vs1 : BitVec 7) (shamt : BitVec 6) (js : SailJoltState) :
    (JoltISA.execInstr (.SRAI (.vreg vd) (.vreg vs1) shamt)).run js =
      .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r => if r = vd then shift_bits_right_arith (js.vregs vs1) shamt
                          else js.vregs r } :=
  JoltISA.srai_run_vreg_vreg vd vs1 shamt js

/-- `ADD` on virtual registers. -/
theorem vreg_ADD_run (vd vs1 vs2 : BitVec 7) (js : SailJoltState) :
    (JoltISA.execInstr (.ADD (.vreg vd) (.vreg vs1) (.vreg vs2))).run js =
      .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r => if r = vd then js.vregs vs1 + js.vregs vs2
                          else js.vregs r } :=
  JoltISA.add_run_vreg_vreg_vreg vd vs1 vs2 js

/-- `SUB` on virtual registers. -/
theorem vreg_SUB_run (vd vs1 vs2 : BitVec 7) (js : SailJoltState) :
    (JoltISA.execInstr (.SUB (.vreg vd) (.vreg vs1) (.vreg vs2))).run js =
      .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r => if r = vd then js.vregs vs1 - js.vregs vs2
                          else js.vregs r } :=
  JoltISA.sub_run_vreg_vreg_vreg vd vs1 vs2 js

/-- `VirtualChangeDivisor` reads two real registers and writes the adjusted divisor. -/
theorem vreg_change_divisor_run (vd : BitVec 7) (rs1 rs2 : regidx)
    (js : SailJoltState) (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    (JoltISA.execInstr (.VirtualChangeDivisor vd rs1 rs2)).run js = .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r =>
          if r = vd then change_divisor_value dividend divisor
          else js.vregs r } :=
  JoltISA.virtual_change_divisor_run vd rs1 rs2 js dividend divisor hrs1 hrs2

/-- `SRAI` from a real register to a virtual register. -/
theorem vreg_SRAI_from_real_run (vd : BitVec 7) (rs1 : regidx) (shamt : BitVec 6)
    (js : SailJoltState) (rs1_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail) :
    (JoltISA.execInstr (.SRAI (.vreg vd) (.xreg rs1) shamt)).run js =
      .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r =>
          if r = vd then shift_bits_right_arith rs1_val shamt
          else js.vregs r } :=
  JoltISA.srai_run_vreg_xreg vd rs1 shamt js rs1_val hrs1

/-- `ADDI` from a virtual register to a real register. -/
theorem vreg_ADDI_to_real_run (rd : regidx) (vs1 : BitVec 7) (imm : BitVec 12)
    (js : SailJoltState) (s' : SailState)
    (hwrite :
      wX_bits rd (js.vregs vs1 + sign_extend (m := 64) imm) js.sail
        = .ok () s') :
    (JoltISA.execInstr (.ADDI (.xreg rd) (.vreg vs1) imm)).run js =
      .ok RETIRE_SUCCESS
      { sail := s', vregs := js.vregs } :=
  JoltISA.addi_run_xreg_vreg rd vs1 imm js s' hwrite

/-- `VirtualAssertValidDiv0` success branch. -/
theorem vreg_assert_valid_div0_run_ok (rs2 : regidx) (vq : BitVec 7)
    (js : SailJoltState) (divisor : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hguard : ¬ (divisor = 0#64 ∧ js.vregs vq ≠ (-1 : BitVec 64))) :
    (JoltISA.execInstr (.VirtualAssertValidDiv0 rs2 vq)).run js =
      .ok RETIRE_SUCCESS js :=
  JoltISA.virtual_assert_valid_div0_run_ok rs2 vq js divisor hrs2 hguard

/-- `VirtualAssertValidDiv0` failure branch. -/
theorem vreg_assert_valid_div0_run_err (rs2 : regidx) (vq : BitVec 7)
    (js : SailJoltState) (divisor : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hguard : divisor = 0#64 ∧ js.vregs vq ≠ (-1 : BitVec 64)) :
    (JoltISA.execInstr (.VirtualAssertValidDiv0 rs2 vq)).run js =
      .error
        (Error.Assertion "VirtualAssertValidDiv0: divisor = 0 but quotient ≠ -1")
        js :=
  JoltISA.virtual_assert_valid_div0_run_err rs2 vq js divisor hrs2 hguard

/-- `VirtualAssertEQ` success branch. -/
theorem vreg_assert_eq_run_ok (va vb : BitVec 7) (js : SailJoltState)
    (hguard : js.vregs va = js.vregs vb) :
    (JoltISA.execInstr (.VirtualAssertEQ va vb)).run js =
      .ok RETIRE_SUCCESS js :=
  JoltISA.virtual_assert_eq_run_ok va vb js hguard

/-- `VirtualAssertEQ` failure branch. -/
theorem vreg_assert_eq_run_err (va vb : BitVec 7) (js : SailJoltState)
    (hguard : js.vregs va ≠ js.vregs vb) :
    (JoltISA.execInstr (.VirtualAssertEQ va vb)).run js =
      .error (Error.Assertion "VirtualAssertEQ") js :=
  JoltISA.virtual_assert_eq_run_err va vb js hguard

/-- `VirtualAssertEQReal` success branch. -/
theorem vreg_assert_eq_real_run_ok (va : BitVec 7) (rb : regidx)
    (js : SailJoltState) (rb_val : BitVec 64)
    (hrb : rX_bits rb js.sail = .ok rb_val js.sail)
    (hguard : js.vregs va = rb_val) :
    (JoltISA.execInstr (.VirtualAssertEQReal va rb)).run js =
      .ok RETIRE_SUCCESS js :=
  JoltISA.virtual_assert_eq_real_run_ok va rb js rb_val hrb hguard

/-- `VirtualAssertEQReal` failure branch. -/
theorem vreg_assert_eq_real_run_err (va : BitVec 7) (rb : regidx)
    (js : SailJoltState) (rb_val : BitVec 64)
    (hrb : rX_bits rb js.sail = .ok rb_val js.sail)
    (hguard : js.vregs va ≠ rb_val) :
    (JoltISA.execInstr (.VirtualAssertEQReal va rb)).run js =
      .error (Error.Assertion "VirtualAssertEQ (vreg vs real)") js :=
  JoltISA.virtual_assert_eq_real_run_err va rb js rb_val hrb hguard

/-- `VirtualAssertValidUnsignedRemainder` success branch. -/
theorem vreg_assert_valid_unsigned_remainder_run_ok
    (vr vd : BitVec 7) (js : SailJoltState)
    (hguard : js.vregs vd = 0#64 ∨ (js.vregs vr).toNat < (js.vregs vd).toNat) :
    (JoltISA.execInstr (.VirtualAssertValidUnsignedRemainder vr vd)).run js =
      .ok RETIRE_SUCCESS js :=
  JoltISA.virtual_assert_valid_unsigned_remainder_run_ok vr vd js hguard

/-- `VirtualAssertValidUnsignedRemainder` failure branch. -/
theorem vreg_assert_valid_unsigned_remainder_run_err
    (vr vd : BitVec 7) (js : SailJoltState)
    (hguard : ¬ (js.vregs vd = 0#64 ∨ (js.vregs vr).toNat < (js.vregs vd).toNat)) :
    (JoltISA.execInstr (.VirtualAssertValidUnsignedRemainder vr vd)).run js =
      .error
        (Error.Assertion "VirtualAssertValidUnsignedRemainder: r ≥ d ∧ d ≠ 0")
        js :=
  JoltISA.virtual_assert_valid_unsigned_remainder_run_err vr vd js hguard

/-- Existential variant of `vreg_advice_run`. -/
theorem vreg_advice_run_ex (vd : BitVec 7) (advice : BitVec 64) (js : SailJoltState) :
    ∃ js',
      (JoltISA.execInstr (.VirtualAdvice vd advice)).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = advice ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail := by
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then advice else js.vregs r }
  refine ⟨js', ?_, ?_, ?_, rfl⟩
  · simpa only [js'] using vreg_advice_run vd advice js
  · show (if vd = vd then advice else js.vregs vd) = advice
    rw [if_pos rfl]
  · intro k h
    show (if k = vd then advice else js.vregs k) = js.vregs k
    rw [if_neg h]

/-- Existential variant of `vreg_MULH_run`. -/
theorem vreg_MULH_run_ex (vd vs1 vs2 : BitVec 7) (js : SailJoltState) :
    ∃ js',
      (JoltISA.execInstr (.MULH (.vreg vd) (.vreg vs1) (.vreg vs2))).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = mulhs (js.vregs vs1) (js.vregs vs2) ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail := by
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then mulhs (js.vregs vs1) (js.vregs vs2)
        else js.vregs r }
  refine ⟨js', ?_, ?_, ?_, rfl⟩
  · simpa only [js'] using vreg_MULH_run vd vs1 vs2 js
  · show (if vd = vd then _ else js.vregs vd) = _
    rw [if_pos rfl]
  · intro k h
    show (if k = vd then _ else js.vregs k) = js.vregs k
    rw [if_neg h]

/-- Existential variant of `vreg_MUL_run`. -/
theorem vreg_MUL_run_ex (vd vs1 vs2 : BitVec 7) (js : SailJoltState) :
    ∃ js',
      (JoltISA.execInstr (.MUL (.vreg vd) (.vreg vs1) (.vreg vs2))).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = js.vregs vs1 * js.vregs vs2 ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail := by
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then js.vregs vs1 * js.vregs vs2
        else js.vregs r }
  refine ⟨js', ?_, ?_, ?_, rfl⟩
  · simpa only [js'] using vreg_MUL_run vd vs1 vs2 js
  · show (if vd = vd then _ else js.vregs vd) = _
    rw [if_pos rfl]
  · intro k h
    show (if k = vd then _ else js.vregs k) = js.vregs k
    rw [if_neg h]

/-- Existential variant of `vreg_SRAI_run`. -/
theorem vreg_SRAI_run_ex (vd vs1 : BitVec 7) (shamt : BitVec 6) (js : SailJoltState) :
    ∃ js',
      (JoltISA.execInstr (.SRAI (.vreg vd) (.vreg vs1) shamt)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = shift_bits_right_arith (js.vregs vs1) shamt ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail := by
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then shift_bits_right_arith (js.vregs vs1) shamt
        else js.vregs r }
  refine ⟨js', ?_, ?_, ?_, rfl⟩
  · simpa only [js'] using vreg_SRAI_run vd vs1 shamt js
  · show (if vd = vd then _ else js.vregs vd) = _
    rw [if_pos rfl]
  · intro k h
    show (if k = vd then _ else js.vregs k) = js.vregs k
    rw [if_neg h]

/-- Existential variant of `vreg_change_divisor_run`. -/
theorem vreg_change_divisor_run_ex (vd : BitVec 7) (rs1 rs2 : regidx)
    (js : SailJoltState) (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    ∃ js',
      (JoltISA.execInstr (.VirtualChangeDivisor vd rs1 rs2)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = change_divisor_value dividend divisor ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail := by
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = vd then change_divisor_value dividend divisor else js.vregs r }
  refine ⟨js', ?_, ?_, ?_, rfl⟩
  · simpa only [js'] using vreg_change_divisor_run vd rs1 rs2 js dividend divisor hrs1 hrs2
  · show (if vd = vd then _ else js.vregs vd) = _
    rw [if_pos rfl]
  · intro k h
    show (if k = vd then _ else js.vregs k) = js.vregs k
    rw [if_neg h]

/-- Existential variant of `vreg_SRAI_from_real_run`. -/
theorem vreg_SRAI_from_real_run_ex (vd : BitVec 7) (rs1 : regidx) (shamt : BitVec 6)
    (js : SailJoltState) (rs1_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail) :
    ∃ js',
      (JoltISA.execInstr (.SRAI (.vreg vd) (.xreg rs1) shamt)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = shift_bits_right_arith rs1_val shamt ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail := by
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = vd then shift_bits_right_arith rs1_val shamt else js.vregs r }
  refine ⟨js', ?_, ?_, ?_, rfl⟩
  · simpa only [js'] using vreg_SRAI_from_real_run vd rs1 shamt js rs1_val hrs1
  · show (if vd = vd then _ else js.vregs vd) = _
    rw [if_pos rfl]
  · intro k h
    show (if k = vd then _ else js.vregs k) = js.vregs k
    rw [if_neg h]

/-- Existential variant for `XOR`. -/
theorem vreg_XOR_run_ex (vd vs1 vs2 : BitVec 7) (js : SailJoltState) :
    ∃ js',
      (JoltISA.execInstr (.XOR (.vreg vd) (.vreg vs1) (.vreg vs2))).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = js.vregs vs1 ^^^ js.vregs vs2 ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail := by
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then js.vregs vs1 ^^^ js.vregs vs2 else js.vregs r }
  refine ⟨js', ?_, ?_, ?_, rfl⟩
  · simpa only [js'] using JoltISA.xor_run_vreg_vreg_vreg vd vs1 vs2 js
  · show (if vd = vd then _ else js.vregs vd) = _
    rw [if_pos rfl]
  · intro k h
    show (if k = vd then _ else js.vregs k) = js.vregs k
    rw [if_neg h]

/-- Existential variant of `vreg_SUB_run`. -/
theorem vreg_SUB_run_ex (vd vs1 vs2 : BitVec 7) (js : SailJoltState) :
    ∃ js',
      (JoltISA.execInstr (.SUB (.vreg vd) (.vreg vs1) (.vreg vs2))).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = js.vregs vs1 - js.vregs vs2 ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail := by
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then js.vregs vs1 - js.vregs vs2 else js.vregs r }
  refine ⟨js', ?_, ?_, ?_, rfl⟩
  · simpa only [js'] using vreg_SUB_run vd vs1 vs2 js
  · show (if vd = vd then _ else js.vregs vd) = _
    rw [if_pos rfl]
  · intro k h
    show (if k = vd then _ else js.vregs k) = js.vregs k
    rw [if_neg h]

/-- Existential variant of `vreg_ADD_run`. -/
theorem vreg_ADD_run_ex (vd vs1 vs2 : BitVec 7) (js : SailJoltState) :
    ∃ js',
      (JoltISA.execInstr (.ADD (.vreg vd) (.vreg vs1) (.vreg vs2))).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = js.vregs vs1 + js.vregs vs2 ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail := by
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then js.vregs vs1 + js.vregs vs2 else js.vregs r }
  refine ⟨js', ?_, ?_, ?_, rfl⟩
  · simpa only [js'] using vreg_ADD_run vd vs1 vs2 js
  · show (if vd = vd then _ else js.vregs vd) = _
    rw [if_pos rfl]
  · intro k h
    show (if k = vd then _ else js.vregs k) = js.vregs k
    rw [if_neg h]

end
