import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Itype.W.Family

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# ADDIW: Jolt ADDI + VirtualSignExtendWord = Sail ADDIW

Jolt's ADDIW is `execute_ITYPE iop.ADDI + VSEW`. No bridge lemma is
needed: both Jolt and Sail compute the same value
`sign_extend(extractLsb(v + sign_extend(imm)))` for the final value in
`rd`.
-/

theorem execute_ITYPE_ADDI_factored (imm : BitVec 12) (rs1 rd : regidx) :
    execute_ITYPE imm rs1 rd iop.ADDI = (do
      let v ← rX_bits rs1
      wX_bits rd (v + sign_extend (m := 64) imm)
      pure RETIRE_SUCCESS) := by
  simp [execute_ITYPE, bind_pure_comp, pure_bind]

theorem execute_ADDIW_factored (imm : BitVec 12) (rs1 rd : regidx) :
    execute_ADDIW imm rs1 rd = (do
      let v ← rX_bits rs1
      wX_bits rd (sign_extend (m := 64)
        (Sail.BitVec.extractLsb (v + sign_extend (m := 64) imm) 31 0))
      pure RETIRE_SUCCESS) := by
  simp [execute_ADDIW, bind_pure_comp, pure_bind]

def jolt_addiw (imm : BitVec 12) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let _ ← liftSail (execute_ITYPE imm rs1 rd iop.ADDI)
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

theorem jolt_addiw_concrete (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v : BitVec 64),
      rX_bits rs1 js.sail = .ok v js.sail ∧
      (jolt_addiw imm rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (Sail.BitVec.extractLsb (v + sign_extend (m := 64) imm) 31 0)) := by
  unfold jolt_addiw liftSail
  rw [execute_ITYPE_ADDI_factored]
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
  obtain ⟨v, hok⟩ := hwf rs1
  simp only [hok]
  obtain ⟨s3, hw1⟩ := wX_shape rd (v + sign_extend (m := 64) imm) js.sail
  simp only [hw1]
  have hrx := wX_rX_roundtrip rd _ js.sail s3 hrd hw1
  obtain ⟨js4, hvsew, hsail⟩ :=
    jolt_virtual_sign_extend_word_concrete rd
      { sail := s3, vregs := js.vregs } (v + sign_extend (m := 64) imm) hrd hrx
  simp only [EStateM.run] at hvsew
  simp only [hvsew]
  refine ⟨js4, v, rfl, rfl, ?_⟩
  rw [hsail, show ({ sail := s3, vregs := js.vregs } : SailJoltState).sail = s3 from rfl,
      wX_bits_eq_stateAfterWrite rd _ js.sail s3 hw1,
      stateAfterWrite_stateAfterWrite]

theorem jolt_addiw_eq_sail (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_addiw imm rs1 rd).run js) =
    (execute_ADDIW imm rs1 rd).run js.sail :=
  itype_eq_sail_uniform
    (f := fun v => sign_extend (m := 64)
      (Sail.BitVec.extractLsb (v + sign_extend (m := 64) imm) 31 0))
    (execute_ADDIW_factored imm rs1 rd)
    (jolt_addiw_concrete imm rs1 rd hrd js hwf)

end
