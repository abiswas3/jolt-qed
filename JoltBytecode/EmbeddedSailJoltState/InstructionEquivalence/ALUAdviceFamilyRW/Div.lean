import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Compatibility
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamilyRW.DivReference

/-!
# DIV rewrite program

This file is the new-style `JoltISA.Program` transcription of the local
`DivReference.lean` monadic `jolt_div` sequence.
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

private theorem onlyRetire_vreg_advice (vd : BitVec 7) (value : BitVec 64) :
    ∀ js r js', (execInstr (.VirtualAdvice vd value)).run js = .ok r js' →
      r = RETIRE_SUCCESS := by
  intro js r js' h
  simp [execInstr, writeVReg, RETIRE_SUCCESS, bind, EStateM.bind,
    EStateM.run, pure, EStateM.pure, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet] at h
  exact h.1.symm

private theorem onlyRetire_VirtualAssertValidDiv0 (divisor : regidx) (quotient : VReg) :
    ∀ js r js', (execInstr (.VirtualAssertValidDiv0 divisor quotient)).run js =
      .ok r js' → r = RETIRE_SUCCESS := by
  intro js r js' h
  unfold execInstr liftSail readVReg at h
  simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get, RETIRE_SUCCESS,
    throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
  cases hr : rX_bits divisor js.sail with
  | ok d s =>
      simp [hr] at h
      by_cases hd : d = 0#64
      · by_cases hq : js.vregs quotient = (-1 : BitVec 64)
        · simp [hd, hq, pure, EStateM.pure] at h
          exact h.1.symm
        · have hq' : js.vregs quotient ≠ 18446744073709551615#64 := by
            simpa using hq
          simp [hd, hq', throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
      · simp [hd, pure, EStateM.pure] at h
        exact h.1.symm
  | error e s =>
      simp [hr] at h

private theorem onlyRetire_VirtualChangeDivisor
    (dst : VReg) (dividend divisor : regidx) :
    ∀ js r js', (execInstr (.VirtualChangeDivisor dst dividend divisor)).run js =
      .ok r js' → r = RETIRE_SUCCESS := by
  intro js r js' h
  unfold execInstr liftSail writeVReg at h
  simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    RETIRE_SUCCESS, modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet] at h
  cases hdividend : rX_bits dividend js.sail with
  | ok a s1 =>
      simp [hdividend] at h
      cases hdivisor : rX_bits divisor s1 with
      | ok b s2 =>
          simp [hdivisor] at h
          exact h.1.symm
      | error e s2 =>
          simp [hdivisor] at h
  | error e s1 =>
      simp [hdividend] at h

private theorem onlyRetire_MULH_vreg_vreg_vreg (vd lhs rhs : VReg) :
    ∀ js r js', (execInstr (.MULH (.vreg vd) (.vreg lhs) (.vreg rhs))).run js =
      .ok r js' → r = RETIRE_SUCCESS := by
  intro js r js' h
  simp [execInstr, readSrc, writeDst, readVReg, writeVReg, RETIRE_SUCCESS,
    EStateM.run, bind, EStateM.bind, pure, EStateM.pure, get, modify,
    modifyGet, getThe, MonadStateOf.get, MonadStateOf.modifyGet,
    EStateM.get, EStateM.modifyGet] at h
  exact h.1.symm

private theorem onlyRetire_MUL_vreg_vreg_vreg (vd lhs rhs : VReg) :
    ∀ js r js', (execInstr (.MUL (.vreg vd) (.vreg lhs) (.vreg rhs))).run js =
      .ok r js' → r = RETIRE_SUCCESS := by
  intro js r js' h
  simp [execInstr, readSrc, writeDst, readVReg, writeVReg, RETIRE_SUCCESS,
    EStateM.run, bind, EStateM.bind, pure, EStateM.pure, get, modify,
    modifyGet, getThe, MonadStateOf.get, MonadStateOf.modifyGet,
    EStateM.get, EStateM.modifyGet] at h
  exact h.1.symm

private theorem onlyRetire_SRAI_vreg_vreg (vd vs : VReg) (shamt : BitVec 6) :
    ∀ js r js', (execInstr (.SRAI (.vreg vd) (.vreg vs) shamt)).run js =
      .ok r js' → r = RETIRE_SUCCESS := by
  intro js r js' h
  simp [execInstr, readSrc, writeDst, readVReg, writeVReg, RETIRE_SUCCESS,
    EStateM.run, bind, EStateM.bind, pure, EStateM.pure, get, modify,
    modifyGet, getThe, MonadStateOf.get, MonadStateOf.modifyGet,
    EStateM.get, EStateM.modifyGet] at h
  exact h.1.symm

private theorem onlyRetire_SRAI_vreg_xreg
    (vd : VReg) (rs : regidx) (shamt : BitVec 6) :
    ∀ js r js', (execInstr (.SRAI (.vreg vd) (.xreg rs) shamt)).run js =
      .ok r js' → r = RETIRE_SUCCESS := by
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

private theorem onlyRetire_VirtualAssertEQ (lhs rhs : VReg) :
    ∀ js r js', (execInstr (.VirtualAssertEQ lhs rhs)).run js = .ok r js' →
      r = RETIRE_SUCCESS := by
  intro js r js' h
  simp [execInstr, readVReg, RETIRE_SUCCESS, bind, EStateM.bind, EStateM.run,
    pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw,
    EStateM.throw, get, getThe, MonadStateOf.get, EStateM.get] at h
  by_cases hc : js.vregs lhs = js.vregs rhs
  · simp [hc, pure, EStateM.pure] at h
    exact h.1.symm
  · simp [hc, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h

private theorem onlyRetire_XOR_vreg_vreg_vreg (vd lhs rhs : VReg) :
    ∀ js r js', (execInstr (.XOR (.vreg vd) (.vreg lhs) (.vreg rhs))).run js =
      .ok r js' → r = RETIRE_SUCCESS := by
  intro js r js' h
  simp [execInstr, readSrc, writeDst, readVReg, writeVReg, RETIRE_SUCCESS,
    EStateM.run, bind, EStateM.bind, pure, EStateM.pure, get, modify,
    modifyGet, getThe, MonadStateOf.get, MonadStateOf.modifyGet,
    EStateM.get, EStateM.modifyGet] at h
  exact h.1.symm

private theorem onlyRetire_SUB_vreg_vreg_vreg (vd lhs rhs : VReg) :
    ∀ js r js', (execInstr (.SUB (.vreg vd) (.vreg lhs) (.vreg rhs))).run js =
      .ok r js' → r = RETIRE_SUCCESS := by
  intro js r js' h
  simp [execInstr, readSrc, writeDst, readVReg, writeVReg, RETIRE_SUCCESS,
    EStateM.run, bind, EStateM.bind, pure, EStateM.pure, get, modify,
    modifyGet, getThe, MonadStateOf.get, MonadStateOf.modifyGet,
    EStateM.get, EStateM.modifyGet] at h
  exact h.1.symm

private theorem onlyRetire_ADD_vreg_vreg_vreg (vd lhs rhs : VReg) :
    ∀ js r js', (execInstr (.ADD (.vreg vd) (.vreg lhs) (.vreg rhs))).run js =
      .ok r js' → r = RETIRE_SUCCESS := by
  intro js r js' h
  simp [execInstr, readSrc, writeDst, readVReg, writeVReg, RETIRE_SUCCESS,
    EStateM.run, bind, EStateM.bind, pure, EStateM.pure, get, modify,
    modifyGet, getThe, MonadStateOf.get, MonadStateOf.modifyGet,
    EStateM.get, EStateM.modifyGet] at h
  exact h.1.symm

private theorem onlyRetire_VirtualAssertEQReal (lhs : VReg) (rhs : regidx) :
    ∀ js r js', (execInstr (.VirtualAssertEQReal lhs rhs)).run js = .ok r js' →
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

private theorem onlyRetire_VirtualAssertValidUnsignedRemainder
    (remainder divisor : VReg) :
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

private theorem onlyRetire_ADDI_xreg_vreg (rd : regidx) (vs : BitVec 7)
    (imm : BitVec 12) :
    ∀ js r js', (execInstr (.ADDI (.xreg rd) (.vreg vs) imm)).run js =
      .ok r js' → r = RETIRE_SUCCESS := by
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

/-- New-style Jolt ISA program for RV64 `DIV`. -/
def divProgram (rs2 rs1 rd : regidx)
    (quotient remAbs : BitVec 64) : Program :=
  .instr (.VirtualAdvice 0 quotient) <|
  .instr (.VirtualAdvice 1 remAbs) <|
  .instr (.VirtualAssertValidDiv0 rs2 0) <|
  .instr (.VirtualChangeDivisor 2 rs1 rs2) <|
  .instr (.MULH (.vreg 3) (.vreg 0) (.vreg 2)) <|
  .instr (.MUL (.vreg 4) (.vreg 0) (.vreg 2)) <|
  .instr (.SRAI (.vreg 5) (.vreg 4) (63 : BitVec 6)) <|
  .instr (.VirtualAssertEQ 3 5) <|
  .instr (.SRAI (.vreg 3) (.xreg rs1) (63 : BitVec 6)) <|
  .instr (.XOR (.vreg 5) (.vreg 1) (.vreg 3)) <|
  .instr (.SUB (.vreg 5) (.vreg 5) (.vreg 3)) <|
  .instr (.ADD (.vreg 4) (.vreg 4) (.vreg 5)) <|
  .instr (.VirtualAssertEQReal 4 rs1) <|
  .instr (.SRAI (.vreg 3) (.vreg 2) (63 : BitVec 6)) <|
  .instr (.XOR (.vreg 5) (.vreg 2) (.vreg 3)) <|
  .instr (.SUB (.vreg 5) (.vreg 5) (.vreg 3)) <|
  .instr (.VirtualAssertValidUnsignedRemainder 1 5) <|
  .instr (.ADDI (.xreg rd) (.vreg 0) (0 : BitVec 12)) <|
  .done RETIRE_SUCCESS

theorem divProgram_run_eq_jolt_div (rs2 rs1 rd : regidx)
    (quotient remAbs : BitVec 64) (js : SailJoltState) :
    (execProgram (divProgram rs2 rs1 rd quotient remAbs)).run js =
      (jolt_div rs2 rs1 rd quotient remAbs).run js := by
  unfold divProgram jolt_div
  rw [execProgram_instr_of_onlyRetire (.VirtualAdvice 0 quotient) _
    (onlyRetire_vreg_advice 0 quotient)]
  rw [execProgram_instr_of_onlyRetire (.VirtualAdvice 1 remAbs) _
    (onlyRetire_vreg_advice 1 remAbs)]
  rw [execProgram_instr_of_onlyRetire (.VirtualAssertValidDiv0 rs2 0) _
    (onlyRetire_VirtualAssertValidDiv0 rs2 0)]
  rw [execProgram_instr_of_onlyRetire (.VirtualChangeDivisor 2 rs1 rs2) _
    (onlyRetire_VirtualChangeDivisor 2 rs1 rs2)]
  rw [execProgram_instr_of_onlyRetire (.MULH (.vreg 3) (.vreg 0) (.vreg 2)) _
    (onlyRetire_MULH_vreg_vreg_vreg 3 0 2)]
  rw [execProgram_instr_of_onlyRetire (.MUL (.vreg 4) (.vreg 0) (.vreg 2)) _
    (onlyRetire_MUL_vreg_vreg_vreg 4 0 2)]
  rw [execProgram_instr_of_onlyRetire (.SRAI (.vreg 5) (.vreg 4) (63 : BitVec 6)) _
    (onlyRetire_SRAI_vreg_vreg 5 4 63)]
  rw [execProgram_instr_of_onlyRetire (.VirtualAssertEQ 3 5) _
    (onlyRetire_VirtualAssertEQ 3 5)]
  rw [execProgram_instr_of_onlyRetire (.SRAI (.vreg 3) (.xreg rs1) (63 : BitVec 6)) _
    (onlyRetire_SRAI_vreg_xreg 3 rs1 63)]
  rw [execProgram_instr_of_onlyRetire (.XOR (.vreg 5) (.vreg 1) (.vreg 3)) _
    (onlyRetire_XOR_vreg_vreg_vreg 5 1 3)]
  rw [execProgram_instr_of_onlyRetire (.SUB (.vreg 5) (.vreg 5) (.vreg 3)) _
    (onlyRetire_SUB_vreg_vreg_vreg 5 5 3)]
  rw [execProgram_instr_of_onlyRetire (.ADD (.vreg 4) (.vreg 4) (.vreg 5)) _
    (onlyRetire_ADD_vreg_vreg_vreg 4 4 5)]
  rw [execProgram_instr_of_onlyRetire (.VirtualAssertEQReal 4 rs1) _
    (onlyRetire_VirtualAssertEQReal 4 rs1)]
  rw [execProgram_instr_of_onlyRetire (.SRAI (.vreg 3) (.vreg 2) (63 : BitVec 6)) _
    (onlyRetire_SRAI_vreg_vreg 3 2 63)]
  rw [execProgram_instr_of_onlyRetire (.XOR (.vreg 5) (.vreg 2) (.vreg 3)) _
    (onlyRetire_XOR_vreg_vreg_vreg 5 2 3)]
  rw [execProgram_instr_of_onlyRetire (.SUB (.vreg 5) (.vreg 5) (.vreg 3)) _
    (onlyRetire_SUB_vreg_vreg_vreg 5 5 3)]
  rw [execProgram_instr_of_onlyRetire (.VirtualAssertValidUnsignedRemainder 1 5) _
    (onlyRetire_VirtualAssertValidUnsignedRemainder 1 5)]
  rw [execProgram_instr_of_onlyRetire (.ADDI (.xreg rd) (.vreg 0) (0 : BitVec 12)) _
    (onlyRetire_ADDI_xreg_vreg rd 0 0)]
  simp [execProgram, execInstr, vreg_advice, vreg_assert_valid_div0,
    vreg_change_divisor, vreg_MULH, vreg_MUL, vreg_SRAI, vreg_assert_eq,
    vreg_SRAI_from_real, vreg_XOR, vreg_SUB, vreg_ADD,
    vreg_assert_eq_real, vreg_assert_valid_unsigned_remainder,
    vreg_ADDI_to_real, change_divisor_value]

/-- Completeness for the new-style DIV bytecode program. -/
theorem divProgram_complete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    projectResult ((execProgram (divProgram rs2 rs1 rd
                      (sail_div_value dividend divisor false)
                      (bv_abs (sail_rem_value dividend divisor false)))).run js) =
    (execute_DIV rs2 rs1 rd false).run js.sail := by
  rw [divProgram_run_eq_jolt_div]
  exact jolt_div_complete rs2 rs1 rd hrd js hwf dividend divisor hrs1 hrs2

/-- Soundness for the new-style DIV bytecode program. -/
theorem divProgram_sound (rs2 rs1 rd : regidx)
    (q rem : BitVec 64)
    (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (js' : SailJoltState)
    (hok : (execProgram (divProgram rs2 rs1 rd q rem)).run js =
      .ok RETIRE_SUCCESS js') :
    q = sail_div_value dividend divisor false ∧
    rem = bv_abs (sail_rem_value dividend divisor false) := by
  apply jolt_div_sound rs2 rs1 rd q rem js dividend divisor hrs1 hrs2 js'
  rw [← divProgram_run_eq_jolt_div]
  exact hok

end JoltISA
