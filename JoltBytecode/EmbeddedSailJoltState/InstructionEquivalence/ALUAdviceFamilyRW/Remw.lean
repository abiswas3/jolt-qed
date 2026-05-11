import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Compatibility
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamilyRW.RemwReference

/-!
# REMW rewrite program

This file is the new-style `JoltISA.Program` transcription of the local
`RemwReference.lean` monadic `jolt_remw` sequence.
-/

set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

namespace JoltISA

private theorem execProgram_instr_run_of_onlyRetire
    (instr : Instr) (rest : Program) (js : SailJoltState)
    (hret : ∀ js r js',
      (execInstr instr).run js = .ok r js' → r = RETIRE_SUCCESS) :
    (execProgram (.instr instr rest)).run js =
      (do
        let _ ← execInstr instr
        execProgram rest).run js := by
  unfold execProgram
  simp only [bind, EStateM.bind, EStateM.run]
  cases h : execInstr instr js with
  | ok r js' =>
      have hr := hret js r js' (by simpa [EStateM.run] using h)
      cases hr
      cases rest <;> rfl
  | error e js' =>
      rfl

private theorem execProgram_instr_of_onlyRetire
    (instr : Instr) (rest : Program)
    (hret : ∀ js r js',
      (execInstr instr).run js = .ok r js' → r = RETIRE_SUCCESS) :
    execProgram (.instr instr rest) =
      (do
        let _ ← execInstr instr
        execProgram rest) := by
  funext js
  exact execProgram_instr_run_of_onlyRetire instr rest js hret

private theorem bind_pure_retire_of_onlyRetire
    (m : JoltMonad ExecutionResult) (js : SailJoltState)
    (hret : ∀ js r js', m.run js = .ok r js' → r = RETIRE_SUCCESS) :
    (do
      let _ ← m
      pure RETIRE_SUCCESS).run js = m.run js := by
  simp only [bind, EStateM.bind, EStateM.run]
  cases h : m js with
  | ok r js' =>
      have hr := hret js r js' (by simpa [EStateM.run] using h)
      cases hr
      rfl
  | error e js' =>
      rfl

private theorem bind_pure_retire_of_onlyRetire_eq
    (m : JoltMonad ExecutionResult)
    (hret : ∀ js r js', m.run js = .ok r js' → r = RETIRE_SUCCESS) :
    (do
      let _ ← m
      pure RETIRE_SUCCESS) = m := by
  funext js
  exact bind_pure_retire_of_onlyRetire m js hret

private theorem onlyRetire_vreg_advice (vd : BitVec 7) (value : BitVec 64) :
  ∀ js r js', (execInstr (.Advice vd value)).run js = .ok r js' → r = RETIRE_SUCCESS := by
  intro js r js' h
  simp [execInstr, writeVReg, RETIRE_SUCCESS, bind, EStateM.bind, EStateM.run,
    pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet] at h
  exact h.1.symm

private theorem onlyRetire_SExtW_vreg_xreg (vd : BitVec 7) (rs : regidx) :
    ∀ js r js', (execInstr (.SExtW (.vreg vd) (.xreg rs))).run js = .ok r js' →
      r = RETIRE_SUCCESS := by
  intro js r js' h
  unfold execInstr readSrc writeDst liftSail writeVReg at h
  simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    RETIRE_SUCCESS, modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet] at h
  cases hr : rX_bits rs js.sail with
  | ok v s =>
      simp [hr] at h
      exact h.1.symm
  | error e s =>
      simp [hr] at h

private theorem onlyRetire_SExtW_vreg_vreg (vd vs : BitVec 7) :
    ∀ js r js', (execInstr (.SExtW (.vreg vd) (.vreg vs))).run js = .ok r js' →
      r = RETIRE_SUCCESS := by
  intro js r js' h
  simp [execInstr, readSrc, writeDst, readVReg, writeVReg, RETIRE_SUCCESS,
    EStateM.run,
    bind, EStateM.bind, pure, EStateM.pure, get, modify, modifyGet,
    getThe, MonadStateOf.get, MonadStateOf.modifyGet, EStateM.get,
    EStateM.modifyGet] at h
  exact h.1.symm

private theorem onlyRetire_SExtW_xreg_vreg (rd : regidx) (vs : BitVec 7) :
    ∀ js r js', (execInstr (.SExtW (.xreg rd) (.vreg vs))).run js = .ok r js' →
      r = RETIRE_SUCCESS := by
  intro js r js' h
  unfold execInstr readSrc writeDst liftSail readVReg at h
  simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get, RETIRE_SUCCESS] at h
  cases hw : wX_bits rd (sign_extend (m := 64) (Sail.BitVec.extractLsb (js.vregs vs) 31 0))
      js.sail with
  | ok u s =>
      simp [hw] at h
      exact h.1.symm
  | error e s =>
      simp [hw] at h

private theorem onlyRetire_AssertValidDiv0V (divisor quotient : VReg) :
    ∀ js r js', (execInstr (.AssertValidDiv0V divisor quotient)).run js = .ok r js' →
      r = RETIRE_SUCCESS := by
  intro js r js' h
  simp [execInstr, readVReg, RETIRE_SUCCESS, bind, EStateM.bind, EStateM.run, pure,
    EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw,
    get, getThe, MonadStateOf.get, EStateM.get] at h
  by_cases hd : js.vregs divisor = 0#64
  · by_cases hq : js.vregs quotient = (-1 : BitVec 64)
    · simp [hd, hq, pure, EStateM.pure] at h
      exact h.1.symm
    · have hq' : js.vregs quotient ≠ 18446744073709551615#64 := by
        simpa using hq
      simp [hd, hq', throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
  · simp [hd, pure, EStateM.pure] at h
    exact h.1.symm

private theorem onlyRetire_ChangeDivisorW (dst dividend divisor : VReg) :
    ∀ js r js', (execInstr (.ChangeDivisorW dst dividend divisor)).run js = .ok r js' →
      r = RETIRE_SUCCESS := by
  intro js r js' h
  simp [execInstr, readVReg, writeVReg, RETIRE_SUCCESS, bind, EStateM.bind,
    EStateM.run,
    pure, EStateM.pure, get, modify, modifyGet, getThe, MonadStateOf.get,
    MonadStateOf.modifyGet, EStateM.get, EStateM.modifyGet] at h
  exact h.1.symm

private theorem onlyRetire_AssertEq (lhs rhs : VReg) :
    ∀ js r js', (execInstr (.AssertEq lhs rhs)).run js = .ok r js' →
      r = RETIRE_SUCCESS := by
  intro js r js' h
  simp [execInstr, readVReg, RETIRE_SUCCESS, bind, EStateM.bind, EStateM.run, pure,
    EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw,
    get, getThe, MonadStateOf.get, EStateM.get] at h
  by_cases hc : js.vregs lhs = js.vregs rhs
  · simp [hc, pure, EStateM.pure] at h
    exact h.1.symm
  · simp [hc, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h

private theorem onlyRetire_SRAI_vreg_vreg (vd vs : VReg) (shamt : BitVec 6) :
    ∀ js r js', (execInstr (.SRAI (.vreg vd) (.vreg vs) shamt)).run js = .ok r js' →
      r = RETIRE_SUCCESS := by
  intro js r js' h
  simp [execInstr, readSrc, writeDst, readVReg, writeVReg, RETIRE_SUCCESS,
    EStateM.run,
    bind, EStateM.bind, pure, EStateM.pure, get, modify, modifyGet,
    getThe, MonadStateOf.get, MonadStateOf.modifyGet, EStateM.get,
    EStateM.modifyGet] at h
  exact h.1.symm

private theorem onlyRetire_AssertEqReal (lhs : VReg) (rhs : regidx) :
    ∀ js r js', (execInstr (.AssertEqReal lhs rhs)).run js = .ok r js' →
      r = RETIRE_SUCCESS := by
  intro js r js' h
  unfold execInstr liftSail readVReg at h
  simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get, RETIRE_SUCCESS,
    throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
  cases hr : rX_bits rhs js.sail with
  | ok v s =>
      simp [hr] at h
      by_cases hc : js.vregs lhs = v
      · simp [hc, pure, EStateM.pure] at h
        exact h.1.symm
      · simp [hc, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
  | error e s =>
      simp [hr] at h

private theorem onlyRetire_XOR_vreg_vreg_vreg (vd lhs rhs : VReg) :
    ∀ js r js', (execInstr (.XOR (.vreg vd) (.vreg lhs) (.vreg rhs))).run js = .ok r js' →
      r = RETIRE_SUCCESS := by
  intro js r js' h
  simp [execInstr, readSrc, writeDst, readVReg, writeVReg, RETIRE_SUCCESS,
    EStateM.run,
    bind, EStateM.bind, pure, EStateM.pure, get, modify, modifyGet,
    getThe, MonadStateOf.get, MonadStateOf.modifyGet, EStateM.get,
    EStateM.modifyGet] at h
  exact h.1.symm

private theorem onlyRetire_SUB_vreg_vreg_vreg (vd lhs rhs : VReg) :
    ∀ js r js', (execInstr (.SUB (.vreg vd) (.vreg lhs) (.vreg rhs))).run js = .ok r js' →
      r = RETIRE_SUCCESS := by
  intro js r js' h
  simp [execInstr, readSrc, writeDst, readVReg, writeVReg, RETIRE_SUCCESS,
    EStateM.run,
    bind, EStateM.bind, pure, EStateM.pure, get, modify, modifyGet,
    getThe, MonadStateOf.get, MonadStateOf.modifyGet, EStateM.get,
    EStateM.modifyGet] at h
  exact h.1.symm

private theorem onlyRetire_MUL_vreg_vreg_vreg (vd lhs rhs : VReg) :
    ∀ js r js', (execInstr (.MUL (.vreg vd) (.vreg lhs) (.vreg rhs))).run js = .ok r js' →
      r = RETIRE_SUCCESS := by
  intro js r js' h
  simp [execInstr, readSrc, writeDst, readVReg, writeVReg, RETIRE_SUCCESS,
    EStateM.run,
    bind, EStateM.bind, pure, EStateM.pure, get, modify, modifyGet,
    getThe, MonadStateOf.get, MonadStateOf.modifyGet, EStateM.get,
    EStateM.modifyGet] at h
  exact h.1.symm

private theorem onlyRetire_ADD_vreg_vreg_vreg (vd lhs rhs : VReg) :
    ∀ js r js', (execInstr (.ADD (.vreg vd) (.vreg lhs) (.vreg rhs))).run js = .ok r js' →
      r = RETIRE_SUCCESS := by
  intro js r js' h
  simp [execInstr, readSrc, writeDst, readVReg, writeVReg, RETIRE_SUCCESS,
    EStateM.run,
    bind, EStateM.bind, pure, EStateM.pure, get, modify, modifyGet,
    getThe, MonadStateOf.get, MonadStateOf.modifyGet, EStateM.get,
    EStateM.modifyGet] at h
  exact h.1.symm

private theorem onlyRetire_AssertValidUnsignedRemainder (remainder divisor : VReg) :
    ∀ js r js', (execInstr (.AssertValidUnsignedRemainder remainder divisor)).run js =
      .ok r js' → r = RETIRE_SUCCESS := by
  intro js r js' h
  simp [execInstr, readVReg, RETIRE_SUCCESS, bind, EStateM.bind, EStateM.run, pure,
    EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw,
    get, getThe, MonadStateOf.get, EStateM.get] at h
  by_cases hc : js.vregs divisor = 0#64 ∨
      (js.vregs remainder).toNat < (js.vregs divisor).toNat
  · simp [hc, pure, EStateM.pure] at h
    exact h.1.symm
  · simp [hc, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h

/-- New-style Jolt ISA program for RV64 `REMW`.

The advice values are explicit parameters, matching the old `jolt_remw`
signature:
* `quotient` is loaded into `v0`.
* `remAbs` is loaded into `v1`.

Virtual register allocation follows the existing proof:
`v0 = quotient`, `v1 = |remainder|`, `v2 = adjusted divisor`,
`v3 = temporary`, `v4 = temporary`, `v5 = signed remainder / divisor`,
`v6 = sign-extended dividend`.
-/
def remwProgram (rs2 rs1 rd : regidx)
    (quotient remAbs : BitVec 64) : Program :=
  .instr (.Advice 0 quotient) <|
  .instr (.Advice 1 remAbs) <|
  .instr (.SExtW (.vreg 6) (.xreg rs1)) <|
  .instr (.SExtW (.vreg 5) (.xreg rs2)) <|
  .instr (.AssertValidDiv0V 5 0) <|
  .instr (.ChangeDivisorW 2 6 5) <|
  .instr (.SExtW (.vreg 3) (.vreg 0)) <|
  .instr (.AssertEq 3 0) <|
  .instr (.SRAI (.vreg 4) (.vreg 1) (32 : BitVec 6)) <|
  .instr (.AssertEqReal 4 (regidx.Regidx 0)) <|
  .instr (.SRAI (.vreg 4) (.vreg 6) (31 : BitVec 6)) <|
  .instr (.XOR (.vreg 5) (.vreg 1) (.vreg 4)) <|
  .instr (.SUB (.vreg 5) (.vreg 5) (.vreg 4)) <|
  .instr (.MUL (.vreg 3) (.vreg 0) (.vreg 2)) <|
  .instr (.ADD (.vreg 3) (.vreg 3) (.vreg 5)) <|
  .instr (.AssertEq 3 6) <|
  .instr (.SRAI (.vreg 4) (.vreg 2) (31 : BitVec 6)) <|
  .instr (.XOR (.vreg 3) (.vreg 2) (.vreg 4)) <|
  .instr (.SUB (.vreg 3) (.vreg 3) (.vreg 4)) <|
  .instr (.AssertValidUnsignedRemainder 1 3) <|
  .instr (.SExtW (.xreg rd) (.vreg 5)) <|
  .done RETIRE_SUCCESS

theorem remwProgram_run_eq_jolt_remw (rs2 rs1 rd : regidx)
    (quotient remAbs : BitVec 64) (js : SailJoltState) :
    (execProgram (remwProgram rs2 rs1 rd quotient remAbs)).run js =
      (jolt_remw rs2 rs1 rd quotient remAbs).run js := by
  unfold remwProgram jolt_remw
  rw [execProgram_instr_of_onlyRetire (.Advice 0 quotient) _
    (onlyRetire_vreg_advice 0 quotient)]
  rw [execProgram_instr_of_onlyRetire (.Advice 1 remAbs) _
    (onlyRetire_vreg_advice 1 remAbs)]
  rw [execProgram_instr_of_onlyRetire (.SExtW (.vreg 6) (.xreg rs1)) _
    (onlyRetire_SExtW_vreg_xreg 6 rs1)]
  rw [execProgram_instr_of_onlyRetire (.SExtW (.vreg 5) (.xreg rs2)) _
    (onlyRetire_SExtW_vreg_xreg 5 rs2)]
  rw [execProgram_instr_of_onlyRetire (.AssertValidDiv0V 5 0) _
    (onlyRetire_AssertValidDiv0V 5 0)]
  rw [execProgram_instr_of_onlyRetire (.ChangeDivisorW 2 6 5) _
    (onlyRetire_ChangeDivisorW 2 6 5)]
  rw [execProgram_instr_of_onlyRetire (.SExtW (.vreg 3) (.vreg 0)) _
    (onlyRetire_SExtW_vreg_vreg 3 0)]
  rw [execProgram_instr_of_onlyRetire (.AssertEq 3 0) _
    (onlyRetire_AssertEq 3 0)]
  rw [execProgram_instr_of_onlyRetire (.SRAI (.vreg 4) (.vreg 1) (32 : BitVec 6)) _
    (onlyRetire_SRAI_vreg_vreg 4 1 32)]
  rw [execProgram_instr_of_onlyRetire (.AssertEqReal 4 (regidx.Regidx 0)) _
    (onlyRetire_AssertEqReal 4 (regidx.Regidx 0))]
  rw [execProgram_instr_of_onlyRetire (.SRAI (.vreg 4) (.vreg 6) (31 : BitVec 6)) _
    (onlyRetire_SRAI_vreg_vreg 4 6 31)]
  rw [execProgram_instr_of_onlyRetire (.XOR (.vreg 5) (.vreg 1) (.vreg 4)) _
    (onlyRetire_XOR_vreg_vreg_vreg 5 1 4)]
  rw [execProgram_instr_of_onlyRetire (.SUB (.vreg 5) (.vreg 5) (.vreg 4)) _
    (onlyRetire_SUB_vreg_vreg_vreg 5 5 4)]
  rw [execProgram_instr_of_onlyRetire (.MUL (.vreg 3) (.vreg 0) (.vreg 2)) _
    (onlyRetire_MUL_vreg_vreg_vreg 3 0 2)]
  rw [execProgram_instr_of_onlyRetire (.ADD (.vreg 3) (.vreg 3) (.vreg 5)) _
    (onlyRetire_ADD_vreg_vreg_vreg 3 3 5)]
  rw [execProgram_instr_of_onlyRetire (.AssertEq 3 6) _
    (onlyRetire_AssertEq 3 6)]
  rw [execProgram_instr_of_onlyRetire (.SRAI (.vreg 4) (.vreg 2) (31 : BitVec 6)) _
    (onlyRetire_SRAI_vreg_vreg 4 2 31)]
  rw [execProgram_instr_of_onlyRetire (.XOR (.vreg 3) (.vreg 2) (.vreg 4)) _
    (onlyRetire_XOR_vreg_vreg_vreg 3 2 4)]
  rw [execProgram_instr_of_onlyRetire (.SUB (.vreg 3) (.vreg 3) (.vreg 4)) _
    (onlyRetire_SUB_vreg_vreg_vreg 3 3 4)]
  rw [execProgram_instr_of_onlyRetire (.AssertValidUnsignedRemainder 1 3) _
    (onlyRetire_AssertValidUnsignedRemainder 1 3)]
  rw [execProgram_instr_of_onlyRetire (.SExtW (.xreg rd) (.vreg 5)) _
    (onlyRetire_SExtW_xreg_vreg rd 5)]
  simp [execProgram, execInstr, vreg_advice, vreg_sign_extend_word_from_real,
    vreg_assert_valid_div0_v, vreg_change_divisor_w, vreg_sign_extend_word,
    vreg_assert_eq, vreg_SRAI, vreg_assert_eq_real, vreg_XOR, vreg_SUB,
    vreg_MUL, vreg_ADD, vreg_assert_valid_unsigned_remainder,
    vreg_sign_extend_word_to_real, change_divisor_w_value]

/-- Completeness for the new-style REMW bytecode program.

With honest quotient and absolute-remainder advice, interpreting
`remwProgram` produces the same projected Sail result as Sail's `execute_REMW`.
-/
theorem remwProgram_complete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    projectResult ((execProgram (remwProgram rs2 rs1 rd
                      (sail_divw_value dividend divisor false)
                      (bv_abs (sail_remw_value dividend divisor false)))).run js) =
    (execute_REMW rs2 rs1 rd false).run js.sail := by
  rw [remwProgram_run_eq_jolt_remw]
  exact jolt_remw_complete rs2 rs1 rd hrd js hwf dividend divisor hrs1 hrs2

/-- Soundness for the new-style REMW bytecode program.

If `remwProgram` succeeds on arbitrary advice, the architectural writeback
state matches Sail REMW for the source operands.
-/
theorem remwProgram_sound (rs2 rs1 rd : regidx)
    (q rem : BitVec 64)
    (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (js' : SailJoltState)
    (hok : (execProgram (remwProgram rs2 rs1 rd q rem)).run js =
      .ok RETIRE_SUCCESS js') :
    js'.sail =
      stateAfterWrite js.sail rd (sail_remw_value dividend divisor false) := by
  apply jolt_remw_sound rs2 rs1 rd q rem js dividend divisor hrs1 hrs2 js'
  rw [← remwProgram_run_eq_jolt_remw]
  exact hok

end JoltISA
