import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Compatibility
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamilyRW.RemuReference

/-!
# REMU rewrite program

This file is the new-style `JoltISA.Program` transcription of the local
`RemuReference.lean` monadic `jolt_remu` sequence.
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

private theorem onlyRetire_VirtualAssertMulUNoOverflow (lhs : VReg) (rhs : regidx) :
    ∀ js r js', (execInstr (.VirtualAssertMulUNoOverflow lhs rhs)).run js =
      .ok r js' → r = RETIRE_SUCCESS := by
  intro js r js' h
  unfold execInstr liftSail readVReg at h
  simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get, RETIRE_SUCCESS,
    throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
  cases hr : rX_bits rhs js.sail with
  | ok y s =>
      simp [hr] at h
      by_cases hc : (js.vregs lhs).toNat * y.toNat < 18446744073709551616
      · simp [hc, pure, EStateM.pure] at h
        exact h.1.symm
      · simp [hc, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
  | error e s =>
      simp [hr] at h

private theorem onlyRetire_MUL_vreg_vreg_xreg
    (vd lhs : VReg) (rhs : regidx) :
    ∀ js r js', (execInstr (.MUL (.vreg vd) (.vreg lhs) (.xreg rhs))).run js =
      .ok r js' → r = RETIRE_SUCCESS := by
  intro js r js' h
  unfold execInstr readSrc writeDst liftSail readVReg writeVReg at h
  simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get, RETIRE_SUCCESS,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet] at h
  cases hr : rX_bits rhs js.sail with
  | ok y s =>
      simp [hr] at h
      exact h.1.symm
  | error e s =>
      simp [hr] at h

private theorem onlyRetire_VirtualAssertLTEReal (lhs : VReg) (rhs : regidx) :
    ∀ js r js', (execInstr (.VirtualAssertLTEReal lhs rhs)).run js =
      .ok r js' → r = RETIRE_SUCCESS := by
  intro js r js' h
  unfold execInstr liftSail readVReg at h
  simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get, RETIRE_SUCCESS,
    throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
  cases hr : rX_bits rhs js.sail with
  | ok y s =>
      simp [hr] at h
      by_cases hc : (js.vregs lhs).toNat ≤ y.toNat
      · simp [hc, pure, EStateM.pure] at h
        exact h.1.symm
      · simp [hc, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
  | error e s =>
      simp [hr] at h

private theorem onlyRetire_SUB_vreg_xreg_vreg
    (vd : VReg) (lhs : regidx) (rhs : VReg) :
    ∀ js r js', (execInstr (.SUB (.vreg vd) (.xreg lhs) (.vreg rhs))).run js =
      .ok r js' → r = RETIRE_SUCCESS := by
  intro js r js' h
  unfold execInstr readSrc writeDst liftSail readVReg writeVReg at h
  simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get, RETIRE_SUCCESS,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet] at h
  cases hr : rX_bits lhs js.sail with
  | ok x s =>
      simp [hr] at h
      exact h.1.symm
  | error e s =>
      simp [hr] at h

private theorem onlyRetire_VirtualAssertValidUnsignedRemainderReal
    (remainder : VReg) (divisor : regidx) :
    ∀ js r js',
      (execInstr (.VirtualAssertValidUnsignedRemainderReal remainder divisor)).run js =
        .ok r js' → r = RETIRE_SUCCESS := by
  intro js r js' h
  unfold execInstr liftSail readVReg at h
  simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get, RETIRE_SUCCESS,
    throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
  cases hr : rX_bits divisor js.sail with
  | ok d s =>
      simp [hr] at h
      by_cases hc : d = 0#64 ∨ (js.vregs remainder).toNat < d.toNat
      · simp [hc, pure, EStateM.pure] at h
        exact h.1.symm
      · simp [hc, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
  | error e s =>
      simp [hr] at h

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

/-- New-style Jolt ISA program for RV64 `REMU`. -/
def remuProgram (rs2 rs1 rd : regidx) (quotient : BitVec 64) : Program :=
  .instr (.VirtualAdvice 0 quotient) <|
  .instr (.VirtualAssertMulUNoOverflow 0 rs2) <|
  .instr (.MUL (.vreg 0) (.vreg 0) (.xreg rs2)) <|
  .instr (.VirtualAssertLTEReal 0 rs1) <|
  .instr (.SUB (.vreg 0) (.xreg rs1) (.vreg 0)) <|
  .instr (.VirtualAssertValidUnsignedRemainderReal 0 rs2) <|
  .instr (.ADDI (.xreg rd) (.vreg 0) (0 : BitVec 12)) <|
  .done RETIRE_SUCCESS

theorem remuProgram_run_eq_jolt_remu (rs2 rs1 rd : regidx)
    (quotient : BitVec 64) (js : SailJoltState) :
    (execProgram (remuProgram rs2 rs1 rd quotient)).run js =
      (jolt_remu rs2 rs1 rd quotient).run js := by
  unfold remuProgram jolt_remu
  rw [execProgram_instr_of_onlyRetire (.VirtualAdvice 0 quotient) _
    (onlyRetire_vreg_advice 0 quotient)]
  rw [execProgram_instr_of_onlyRetire (.VirtualAssertMulUNoOverflow 0 rs2) _
    (onlyRetire_VirtualAssertMulUNoOverflow 0 rs2)]
  rw [execProgram_instr_of_onlyRetire (.MUL (.vreg 0) (.vreg 0) (.xreg rs2)) _
    (onlyRetire_MUL_vreg_vreg_xreg 0 0 rs2)]
  rw [execProgram_instr_of_onlyRetire (.VirtualAssertLTEReal 0 rs1) _
    (onlyRetire_VirtualAssertLTEReal 0 rs1)]
  rw [execProgram_instr_of_onlyRetire (.SUB (.vreg 0) (.xreg rs1) (.vreg 0)) _
    (onlyRetire_SUB_vreg_xreg_vreg 0 rs1 0)]
  rw [execProgram_instr_of_onlyRetire (.VirtualAssertValidUnsignedRemainderReal 0 rs2) _
    (onlyRetire_VirtualAssertValidUnsignedRemainderReal 0 rs2)]
  rw [execProgram_instr_of_onlyRetire (.ADDI (.xreg rd) (.vreg 0) (0 : BitVec 12)) _
    (onlyRetire_ADDI_xreg_vreg rd 0 0)]
  simp [execProgram, execInstr, vreg_advice, vreg_assert_mulu_no_overflow,
    vreg_MUL_from_real_vs2, vreg_assert_lte_real, vreg_SUB_from_real_vs1,
    vreg_assert_valid_unsigned_remainder_real, vreg_ADDI_to_real]

/-- Completeness for the new-style REMU bytecode program. -/
theorem remuProgram_complete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    projectResult ((execProgram (remuProgram rs2 rs1 rd
                      (sail_div_value dividend divisor true))).run js) =
    (execute_REM rs2 rs1 rd true).run js.sail := by
  rw [remuProgram_run_eq_jolt_remu]
  exact jolt_remu_complete rs2 rs1 rd hrd js hwf dividend divisor hrs1 hrs2

/-- Soundness for the new-style REMU bytecode program. -/
theorem remuProgram_sound (rs2 rs1 rd : regidx)
    (q : BitVec 64)
    (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (js' : SailJoltState)
    (hok : (execProgram (remuProgram rs2 rs1 rd q)).run js =
      .ok RETIRE_SUCCESS js') :
    js'.sail =
      stateAfterWrite js.sail rd (sail_rem_value dividend divisor true) := by
  apply jolt_remu_sound rs2 rs1 rd q js dividend divisor hrs1 hrs2 js'
  rw [← remuProgram_run_eq_jolt_remu]
  exact hok

end JoltISA
