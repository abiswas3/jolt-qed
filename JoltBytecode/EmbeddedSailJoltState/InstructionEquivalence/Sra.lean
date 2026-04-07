import JoltBytecode.EmbeddedSailJoltState.RtypeW
import JoltBytecode.BytecodeExpansions.Instructions.Sra

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do

set_option autoImplicit true

noncomputable section

/-! ## SRA: Jolt VirtualSRA via bitmask = Sail SRA

Jolt decomposes SRA as (from BytecodeExpansions/Sra.lean):
1. VirtualShiftRightBitmask rs2 → bitmask
2. VirtualSRA rd, rs1, bitmask  — arithmetic right shift by ctz(bitmask)

ctz(bitmask) = rs2[5:0], so this equals Sail's SRA.
Same pattern as SRAI but reading shift amount from rs2 instead of immediate.
-/

-- Bridge: Jolt's arithmetic shift via ctz(bitmask) = Sail's shift_bits_right_arith.
private lemma sra_bitmask_eq_shift (v1 v2 : BitVec 64) :
    v1.sshiftRight (ctz (sra_bitmask v2)) =
    shift_bits_right_arith v1 (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0) := by
  sorry

-- Factoring: execute_RTYPE SRA reads rs1, rs2, arith-right-shifts v1 by v2[5:0].
private theorem execute_RTYPE_SRA_factored (rs2 rs1 rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SRA = (do
      let v1 ← rX_bits rs1; let v2 ← rX_bits rs2
      wX_bits rd (shift_bits_right_arith v1 (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0))
      pure RETIRE_SUCCESS) := by
  sorry

-- Jolt's SRA: read rs1, arithmetic right shift by ctz(bitmask of rs2), write to rd.
def jolt_sra (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let v1 ← liftSail (rX_bits rs1)
  let v2 ← liftSail (rX_bits rs2)
  liftSail (wX_bits rd (v1.sshiftRight (ctz (sra_bitmask v2))))
  pure RETIRE_SUCCESS

-- Running Jolt's SRA and projecting equals running Sail's SRA.
theorem jolt_sra_eq_sail (rs2 rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_sra rs2 rs1 rd).run js) =
    (execute_RTYPE rs2 rs1 rd rop.SRA).run js.sail := by
  rw [execute_RTYPE_SRA_factored]
  unfold jolt_sra liftSail projectResult
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
  obtain ⟨v1, hok1⟩ := hwf rs1
  obtain ⟨v2, hok2⟩ := hwf rs2
  simp only [hok1, hok2]
  rw [sra_bitmask_eq_shift v1 v2]
  cases wX_bits rd _ js.sail with
  | error e s => simp [projectResult, project]
  | ok a s => simp [projectResult, project]

end
