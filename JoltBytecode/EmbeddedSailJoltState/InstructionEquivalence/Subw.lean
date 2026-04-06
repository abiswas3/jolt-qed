import JoltBytecode.EmbeddedSailJoltState.RtypeW

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-! ## SUBW: instantiation of the generic R-type W framework -/

-- Factoring: execute_RTYPE SUB reads rs1, rs2, writes v1 - v2.
theorem execute_RTYPE_SUB_factored (rs2 rs1 rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SUB = (do
      let v1 ← rX_bits rs1; let v2 ← rX_bits rs2
      wX_bits rd (v1 - v2); pure RETIRE_SUCCESS) := by
  simp [execute_RTYPE, bind_pure_comp, pure_bind]

-- Mathematical core: truncation distributes over subtraction.
theorem extractLsb_sub (a b : BitVec 64) :
    Sail.BitVec.extractLsb (a - b) 31 0 =
    Sail.BitVec.extractLsb a 31 0 - Sail.BitVec.extractLsb b 31 0 := by
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_sub]
  omega

-- Jolt's SUBW decomposition: 64-bit SUB then sign-extend lower 32 bits.
def jolt_subw (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let _ ← liftSail (execute_RTYPE rs2 rs1 rd rop.SUB)
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

-- Jolt SUBW = Sail SUBW.
theorem jolt_subw_eq_sail (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_subw rs2 rs1 rd).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.SUBW).run js.sail := by
  exact jolt_rtype_w_eq_sail rop.SUB ropw.SUBW (· - ·) execute_RTYPE_SUB_factored
    (by intro a b; exact extractLsb_sub a b) rs2 rs1 rd hrd js hwf

end
