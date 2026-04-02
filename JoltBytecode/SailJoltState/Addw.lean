-- TODO: This file depends on sorry'd lemmas in Common.lean (wX_rX_roundtrip, wX_wX_collapse)
import JoltBytecode.SailJoltState.Common

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# ADDW: Jolt ADD + VirtualSignExtendWord = Sail ADDW
-/

-- In plain English: The Sail execute RTYPEW for ADDW decomposes 
-- to the following imperative code block.
theorem execute_RTYPEW_ADDW_eq_factored (rs2 rs1 rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.ADDW = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sign_extend (m := 64)
        (Sail.BitVec.extractLsb v1 31 0 + Sail.BitVec.extractLsb v2 31 0))
      pure RETIRE_SUCCESS) := by
  simp [execute_RTYPEW]


-- In plain English: Jolt has no native ADDW instruction. Instead it
-- executes a full-width ADD on the two source registers, then applies
-- VirtualSignExtendWord to the destination register to narrow and
-- sign-extend the 32-bit result back to 64 bits.
def jolt_addw (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let _ ← liftSail (execute_RTYPE rs2 rs1 rd rop.ADD)
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

/-! ## Main theorem -/
-- The cases nightmare was solved with `sail_cases` (defined in Common.lean).
-- `sail_cases` uses `generalize` + `cases` + `simp` to case-split on shared
-- EStateM.Result discriminants (like `rX_bits rs1 s`) on both sides of the
-- equation simultaneously. `mvcgen` was investigated but doesn't apply here
-- because the theorem is a cross-monad simulation (JoltMonad vs SailM), not
-- a single-monad functional correctness proof.
--
-- In plain English: Running Jolt's two-step ADDW (ADD then
-- VirtualSignExtendWord) and projecting the result onto Sail state
-- produces exactly the same outcome as running Sail's native ADDW
-- instruction directly. This is the correctness proof that Jolt's
-- decomposition is faithful to the RISC-V specification.
theorem jolt_addw_eq_sail (rs2 rs1 rd : regidx) (js : SailJoltState) :
    projectResult ((jolt_addw rs2 rs1 rd).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.ADDW).run (project js) := by
  rw [execute_RTYPEW_ADDW_eq_factored]
  simp only [jolt_addw, jolt_virtual_sign_extend_word,
        liftSail, projectResult, project,
        bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
  simp only [execute_RTYPE, bind, EStateM.bind, pure, EStateM.pure]
  sail_cases rX_bits rs1 ⟨js.regs, js.choiceState, js.mem, js.tags, js.cycleCount, js.sailOutput⟩
  rename_i v1 s1
  sail_cases rX_bits rs2 s1
  rename_i v2 s2
  obtain ⟨s3, hwx⟩ := wX_shape rd (v1 + v2) s2
  simp [hwx]
  have hrx := wX_rX_roundtrip rd (v1 + v2) s2 s3 hwx
  simp [hrx]
  rw [extractLsb_add v1 v2]
  obtain ⟨s4, hwx2⟩ := wX_shape rd
      (sign_extend (Sail.BitVec.extractLsb v1 31 0 + Sail.BitVec.extractLsb v2 31 0)) s3
  have hcollapse := wX_wX_collapse rd (v1 + v2)
      (sign_extend (Sail.BitVec.extractLsb v1 31 0 + Sail.BitVec.extractLsb v2 31 0))
      s2 s3 s4 hwx hwx2
  simp [hwx2, hcollapse]
end
