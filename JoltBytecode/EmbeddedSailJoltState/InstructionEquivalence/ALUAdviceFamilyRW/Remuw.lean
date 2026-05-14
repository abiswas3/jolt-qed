import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Compatibility
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamilyRW.RemuwReference

/-!
# REMUW rewrite program

This file is the new-style `JoltISA.Program` transcription of the local
`RemuwReference.lean` monadic `jolt_remuw` sequence.
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

private theorem onlyRetire_VirtualZeroExtendWord_vreg_xreg (vd : BitVec 7) (rs : regidx) :
    ∀ js r js', (execInstr (.VirtualZeroExtendWord (.vreg vd) (.xreg rs))).run js = .ok r js' →
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

private theorem onlyRetire_vreg_advice (vd : BitVec 7) (value : BitVec 64) :
    ∀ js r js', (execInstr (.VirtualAdvice vd value)).run js = .ok r js' →
      r = RETIRE_SUCCESS := by
  intro js r js' h
  simp [execInstr, writeVReg, RETIRE_SUCCESS, bind, EStateM.bind,
    EStateM.run, pure, EStateM.pure, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet] at h
  exact h.1.symm

private theorem onlyRetire_VirtualAssertMulUNoOverflowV (lhs rhs : VReg) :
    ∀ js r js', (execInstr (.VirtualAssertMulUNoOverflowV lhs rhs)).run js = .ok r js' →
      r = RETIRE_SUCCESS := by
  intro js r js' h
  by_cases hc : (js.vregs lhs).toNat * (js.vregs rhs).toNat <
      18446744073709551616
  · simp [execInstr, readVReg, RETIRE_SUCCESS, bind, EStateM.bind,
      EStateM.run, pure, EStateM.pure, get, getThe, MonadStateOf.get,
      EStateM.get, hc] at h
    exact h.1.symm
  · simp [execInstr, readVReg, RETIRE_SUCCESS, bind, EStateM.bind,
      EStateM.run, pure, EStateM.pure, throw, throwThe,
      MonadExceptOf.throw, EStateM.throw, get, getThe, MonadStateOf.get,
      EStateM.get, hc] at h

private theorem onlyRetire_MUL_vreg_vreg_vreg (vd lhs rhs : VReg) :
    ∀ js r js', (execInstr (.MUL (.vreg vd) (.vreg lhs) (.vreg rhs))).run js = .ok r js' →
      r = RETIRE_SUCCESS := by
  intro js r js' h
  simp [execInstr, readSrc, writeDst, readVReg, writeVReg, RETIRE_SUCCESS,
    EStateM.run, bind, EStateM.bind, pure, EStateM.pure, get, modify,
    modifyGet, getThe, MonadStateOf.get, MonadStateOf.modifyGet,
    EStateM.get, EStateM.modifyGet] at h
  exact h.1.symm

private theorem onlyRetire_VirtualAssertLTE (lhs rhs : VReg) :
    ∀ js r js', (execInstr (.VirtualAssertLTE lhs rhs)).run js = .ok r js' →
      r = RETIRE_SUCCESS := by
  intro js r js' h
  by_cases hc : (js.vregs lhs).toNat ≤ (js.vregs rhs).toNat
  · simp [execInstr, readVReg, RETIRE_SUCCESS, bind, EStateM.bind,
      EStateM.run, pure, EStateM.pure, get, getThe, MonadStateOf.get,
      EStateM.get, hc] at h
    exact h.1.symm
  · simp [execInstr, readVReg, RETIRE_SUCCESS, bind, EStateM.bind,
      EStateM.run, pure, EStateM.pure, throw, throwThe,
      MonadExceptOf.throw, EStateM.throw, get, getThe, MonadStateOf.get,
      EStateM.get, hc] at h

private theorem onlyRetire_SUB_vreg_vreg_vreg (vd lhs rhs : VReg) :
    ∀ js r js', (execInstr (.SUB (.vreg vd) (.vreg lhs) (.vreg rhs))).run js = .ok r js' →
      r = RETIRE_SUCCESS := by
  intro js r js' h
  simp [execInstr, readSrc, writeDst, readVReg, writeVReg, RETIRE_SUCCESS,
    EStateM.run, bind, EStateM.bind, pure, EStateM.pure, get, modify,
    modifyGet, getThe, MonadStateOf.get, MonadStateOf.modifyGet,
    EStateM.get, EStateM.modifyGet] at h
  exact h.1.symm

private theorem onlyRetire_VirtualAssertValidUnsignedRemainder (remainder divisor : VReg) :
    ∀ js r js', (execInstr (.VirtualAssertValidUnsignedRemainder remainder divisor)).run js =
      .ok r js' → r = RETIRE_SUCCESS := by
  intro js r js' h
  simp [execInstr, readVReg, RETIRE_SUCCESS, bind, EStateM.bind, EStateM.run,
    pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw,
    EStateM.throw, get, getThe, MonadStateOf.get, EStateM.get] at h
  by_cases hc : js.vregs divisor = 0#64 ∨
      (js.vregs remainder).toNat < (js.vregs divisor).toNat
  · simp [hc, pure, EStateM.pure] at h
    exact h.1.symm
  · simp [hc, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h

private theorem onlyRetire_VirtualSignExtendWord_vreg_vreg (vd vs : BitVec 7) :
    ∀ js r js', (execInstr (.VirtualSignExtendWord (.vreg vd) (.vreg vs))).run js = .ok r js' →
      r = RETIRE_SUCCESS := by
  intro js r js' h
  simp [execInstr, readSrc, writeDst, readVReg, writeVReg, RETIRE_SUCCESS,
    EStateM.run, bind, EStateM.bind, pure, EStateM.pure, get, modify,
    modifyGet, getThe, MonadStateOf.get, MonadStateOf.modifyGet,
    EStateM.get, EStateM.modifyGet] at h
  exact h.1.symm

private theorem onlyRetire_VirtualSignExtendWord_xreg_vreg (rd : regidx) (vs : BitVec 7) :
    ∀ js r js', (execInstr (.VirtualSignExtendWord (.xreg rd) (.vreg vs))).run js = .ok r js' →
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

private theorem onlyRetire_VirtualAssertValidDiv0V (divisor quotient : VReg) :
    ∀ js r js', (execInstr (.VirtualAssertValidDiv0V divisor quotient)).run js = .ok r js' →
      r = RETIRE_SUCCESS := by
  intro js r js' h
  simp [execInstr, readVReg, RETIRE_SUCCESS, bind, EStateM.bind, EStateM.run,
    pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw,
    EStateM.throw, get, getThe, MonadStateOf.get, EStateM.get] at h
  by_cases hd : js.vregs divisor = 0#64
  · by_cases hq : js.vregs quotient = (-1 : BitVec 64)
    · simp [hd, hq, pure, EStateM.pure] at h
      exact h.1.symm
    · have hq' : js.vregs quotient ≠ 18446744073709551615#64 := by
        simpa using hq
      simp [hd, hq', throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
  · simp [hd, pure, EStateM.pure] at h
    exact h.1.symm

private theorem onlyRetire_ADDI_xreg_vreg (rd : regidx) (vs : BitVec 7)
    (imm : BitVec 12) :
    ∀ js r js', (execInstr (.ADDI (.xreg rd) (.vreg vs) imm)).run js = .ok r js' →
      r = RETIRE_SUCCESS := by
  intro js r js' h
  unfold execInstr readSrc writeDst liftSail readVReg at h
  simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get, RETIRE_SUCCESS] at h
  cases hw : wX_bits rd (js.vregs vs + sign_extend (m := 64) imm) js.sail with
  | ok u s =>
      simp [hw] at h
      exact h.1.symm
  | error e s =>
      simp [hw] at h

/-- New-style Jolt ISA program for RV64 `REMUW`. -/
def remuwProgram (rs2 rs1 rd : regidx) (quotient : BitVec 64) : Program :=
  .instr (.VirtualZeroExtendWord (.vreg 0) (.xreg rs1)) <|
  .instr (.VirtualZeroExtendWord (.vreg 1) (.xreg rs2)) <|
  .instr (.VirtualAdvice 2 quotient) <|
  .instr (.VirtualAssertMulUNoOverflowV 2 1) <|
  .instr (.MUL (.vreg 3) (.vreg 2) (.vreg 1)) <|
  .instr (.VirtualAssertLTE 3 0) <|
  .instr (.SUB (.vreg 3) (.vreg 0) (.vreg 3)) <|
  .instr (.VirtualAssertValidUnsignedRemainder 3 1) <|
  .instr (.VirtualSignExtendWord (.xreg rd) (.vreg 3)) <|
  .done RETIRE_SUCCESS

theorem remuwProgram_run_eq_jolt_remuw (rs2 rs1 rd : regidx)
    (quotient : BitVec 64) (js : SailJoltState) :
    (execProgram (remuwProgram rs2 rs1 rd quotient)).run js =
      (jolt_remuw rs2 rs1 rd quotient).run js := by
  unfold remuwProgram jolt_remuw
  rw [execProgram_instr_of_onlyRetire (.VirtualZeroExtendWord (.vreg 0) (.xreg rs1)) _
    (onlyRetire_VirtualZeroExtendWord_vreg_xreg 0 rs1)]
  rw [execProgram_instr_of_onlyRetire (.VirtualZeroExtendWord (.vreg 1) (.xreg rs2)) _
    (onlyRetire_VirtualZeroExtendWord_vreg_xreg 1 rs2)]
  rw [execProgram_instr_of_onlyRetire (.VirtualAdvice 2 quotient) _
    (onlyRetire_vreg_advice 2 quotient)]
  rw [execProgram_instr_of_onlyRetire (.VirtualAssertMulUNoOverflowV 2 1) _
    (onlyRetire_VirtualAssertMulUNoOverflowV 2 1)]
  rw [execProgram_instr_of_onlyRetire (.MUL (.vreg 3) (.vreg 2) (.vreg 1)) _
    (onlyRetire_MUL_vreg_vreg_vreg 3 2 1)]
  rw [execProgram_instr_of_onlyRetire (.VirtualAssertLTE 3 0) _
    (onlyRetire_VirtualAssertLTE 3 0)]
  rw [execProgram_instr_of_onlyRetire (.SUB (.vreg 3) (.vreg 0) (.vreg 3)) _
    (onlyRetire_SUB_vreg_vreg_vreg 3 0 3)]
  rw [execProgram_instr_of_onlyRetire (.VirtualAssertValidUnsignedRemainder 3 1) _
    (onlyRetire_VirtualAssertValidUnsignedRemainder 3 1)]
  rw [execProgram_instr_of_onlyRetire (.VirtualSignExtendWord (.xreg rd) (.vreg 3)) _
    (onlyRetire_VirtualSignExtendWord_xreg_vreg rd 3)]
  simp [execProgram, execInstr, vreg_zero_extend_word_from_real, vreg_advice,
    vreg_assert_mulu_no_overflow_v, vreg_MUL, vreg_assert_lte, vreg_SUB,
    vreg_assert_valid_unsigned_remainder, vreg_sign_extend_word_to_real]

/-- Completeness for the new-style REMUW bytecode program. -/
theorem remuwProgram_complete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    projectResult ((execProgram (remuwProgram rs2 rs1 rd
                      (sail_divuw_advice dividend divisor))).run js) =
    (execute_REMW rs2 rs1 rd true).run js.sail := by
  rw [remuwProgram_run_eq_jolt_remuw]
  exact jolt_remuw_complete rs2 rs1 rd hrd js hwf dividend divisor hrs1 hrs2

/-- Soundness for the new-style REMUW bytecode program. -/
theorem remuwProgram_sound (rs2 rs1 rd : regidx)
    (q : BitVec 64)
    (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (js' : SailJoltState)
    (hok : (execProgram (remuwProgram rs2 rs1 rd q)).run js =
      .ok RETIRE_SUCCESS js') :
    js'.sail =
      stateAfterWrite js.sail rd (sail_remw_value dividend divisor true) := by
  apply jolt_remuw_sound rs2 rs1 rd q js dividend divisor hrs1 hrs2 js'
  rw [← remuwProgram_run_eq_jolt_remuw]
  exact hok

end JoltISA
