import JoltBytecode.EmbeddedSailJoltState.RtypeW

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-! ## ADDW: instantiation of the generic R-type W framework -/

-- Factoring: execute_RTYPE ADD reads rs1, rs2, writes v1 + v2.
theorem execute_RTYPE_ADD_factored (rs2 rs1 rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.ADD = (do
      let v1 ← rX_bits rs1; let v2 ← rX_bits rs2
      wX_bits rd (v1 + v2); pure RETIRE_SUCCESS) := by
  simp [execute_RTYPE, bind_pure_comp]

-- Jolt's ADDW decomposition: 64-bit ADD then sign-extend lower 32 bits.
def jolt_addw (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let _ ← liftSail (execute_RTYPE rs2 rs1 rd rop.ADD)
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

-- Jolt ADDW = Sail ADDW.
theorem jolt_addw_eq_sail (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_addw rs2 rs1 rd).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.ADDW).run js.sail := by
  exact jolt_rtype_w_eq_sail rop.ADD ropw.ADDW (· + ·) execute_RTYPE_ADD_factored
    (by intro a b; exact extractLsb_add a b) rs2 rs1 rd hrd js hwf

end
