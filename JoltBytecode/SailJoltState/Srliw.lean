-- TODO: This file depends on sorry'd lemmas in Common.lean (wX_rX_roundtrip, wX_wX_collapse)
-- TODO: Main theorem needs shift-truncation commutativity BitVec lemma
import JoltBytecode.SailJoltState.Common

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SRLIW: Jolt SRLI + VirtualSignExtendWord = Sail SRLIW
-/

-- Factored Sail SRLIW
theorem execute_SHIFTIWOP_SRLIW_eq_factored (shamt : BitVec 5) (rs1 rd : regidx) :
    execute_SHIFTIWOP shamt rs1 rd sopw.SRLIW = (do
      let v1 ← rX_bits rs1
      let rs1_32 := Sail.BitVec.extractLsb v1 31 0
      wX_bits rd (sign_extend (m := 64) (shift_bits_right rs1_32 shamt))
      pure RETIRE_SUCCESS) := by
  simp [execute_SHIFTIWOP]

-- Jolt's SRLIW: SRLI (64-bit logical right shift) then VirtualSignExtendWord.
def jolt_srliw (shamt : BitVec 5) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let _ ← liftSail (execute_SHIFTIOP (shamt.setWidth 6) rs1 rd sop.SRLI)
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

-- Main theorem
theorem jolt_srliw_eq_sail (shamt : BitVec 5) (rs1 rd : regidx) (js : JoltState) :
    projectResult ((jolt_srliw shamt rs1 rd).run js) =
    (execute_SHIFTIWOP shamt rs1 rd sopw.SRLIW).run (project js) := by
  rw [execute_SHIFTIWOP_SRLIW_eq_factored]
  simp only [jolt_srliw, jolt_virtual_sign_extend_word,
        liftSail, projectResult, project,
        bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
  simp only [execute_SHIFTIOP, bind, EStateM.bind, pure, EStateM.pure]
  cases rX_bits rs1 ⟨js.regs, js.choiceState, js.mem, js.tags, js.cycleCount, js.sailOutput⟩ with
  | error e s => simp
  | ok v1 s1 =>
    simp
    -- Same pattern as SLLIW: need shift-then-truncate = truncate-then-shift lemma.
    sorry

end
