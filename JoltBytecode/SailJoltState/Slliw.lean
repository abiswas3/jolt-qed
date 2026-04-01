-- TODO: This file depends on sorry'd lemmas in Common.lean (wX_rX_roundtrip, wX_wX_collapse)
-- TODO: Main theorem needs shift-truncation commutativity BitVec lemma
import JoltBytecode.SailJoltState.Common

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SLLIW: Jolt SLLI + VirtualSignExtendWord = Sail SLLIW
-/

theorem execute_SHIFTIWOP_SLLIW_eq_factored (shamt : BitVec 5) (rs1 rd : regidx) :
    execute_SHIFTIWOP shamt rs1 rd sopw.SLLIW = (do
      let v1 ← rX_bits rs1
      let rs1_32 := Sail.BitVec.extractLsb v1 31 0
      wX_bits rd (sign_extend (m := 64) (shift_bits_left rs1_32 shamt))
      pure RETIRE_SUCCESS) := by
  simp [execute_SHIFTIWOP]

def jolt_slliw (shamt : BitVec 5) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let _ ← liftSail (execute_SHIFTIOP (shamt.setWidth 6) rs1 rd sop.SLLI)
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

theorem jolt_slliw_eq_sail (shamt : BitVec 5) (rs1 rd : regidx) (js : SailJoltState) :
    projectResult ((jolt_slliw shamt rs1 rd).run js) =
    (execute_SHIFTIWOP shamt rs1 rd sopw.SLLIW).run (project js) := by
  rw [execute_SHIFTIWOP_SLLIW_eq_factored]
  simp only [jolt_slliw, jolt_virtual_sign_extend_word,
        liftSail, projectResult, project,
        bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
  simp only [execute_SHIFTIOP, bind, EStateM.bind, pure, EStateM.pure]
  cases rX_bits rs1 ⟨js.regs, js.choiceState, js.mem, js.tags, js.cycleCount, js.sailOutput⟩ with
  | error e s => simp
  | ok v1 s1 =>
    simp
    sorry

end
