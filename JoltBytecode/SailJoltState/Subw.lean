-- TODO: This file depends on sorry'd lemmas in Common.lean (wX_rX_roundtrip, wX_wX_collapse)
import JoltBytecode.SailJoltState.Common

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SUBW: Jolt SUB + VirtualSignExtendWord = Sail SUBW
-/

-- Factored Sail SUBW: read, read, compute, write.
theorem execute_RTYPEW_SUBW_eq_factored (rs2 rs1 rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.SUBW = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sign_extend (m := 64)
        (Sail.BitVec.extractLsb v1 31 0 - Sail.BitVec.extractLsb v2 31 0))
      pure RETIRE_SUCCESS) := by
  simp [execute_RTYPEW]

-- Jolt's SUBW: SUB then VirtualSignExtendWord.
def jolt_subw (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let _ ← liftSail (execute_RTYPE rs2 rs1 rd rop.SUB)
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

-- Main theorem: Jolt SUBW projected = Sail SUBW.
theorem jolt_subw_eq_sail (rs2 rs1 rd : regidx) (js : JoltState) :
    projectResult ((jolt_subw rs2 rs1 rd).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.SUBW).run (project js) := by
  rw [execute_RTYPEW_SUBW_eq_factored]
  simp only [jolt_subw, jolt_virtual_sign_extend_word,
        liftSail, projectResult, project,
        bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
  simp only [execute_RTYPE, bind, EStateM.bind, pure, EStateM.pure]
  cases rX_bits rs1 ⟨js.regs, js.choiceState, js.mem, js.tags, js.cycleCount, js.sailOutput⟩ with
  | error e s => simp
  | ok v1 s1 =>
    simp
    cases rX_bits rs2 s1 with
    | error e s => simp
    | ok v2 s2 =>
      simp
      obtain ⟨s3, hwx⟩ := wX_shape rd (v1 - v2) s2
      simp [hwx]
      have hrx := wX_rX_roundtrip rd (v1 - v2) s2 s3 hwx
      simp [hrx]
      rw [extractLsb_sub v1 v2]
      obtain ⟨s4, hwx2⟩ := wX_shape rd
          (sign_extend (Sail.BitVec.extractLsb v1 31 0 - Sail.BitVec.extractLsb v2 31 0)) s3
      have hcollapse := wX_wX_collapse rd (v1 - v2)
          (sign_extend (Sail.BitVec.extractLsb v1 31 0 - Sail.BitVec.extractLsb v2 31 0))
          s2 s3 s4 hwx hwx2
      simp [hwx2, hcollapse]

end
