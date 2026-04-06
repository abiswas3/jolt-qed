import JoltBytecode.EmbeddedSailJoltState.RtypeW

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-! ## SRLW: Jolt's 64-bit SRL then sign-extend-word = Sail's SRLW

Jolt decomposes SRLW as:
1. SRL rd, rs1, rs2  — 64-bit logical right shift (shift amount = rs2[5:0])
2. VSEW rd           — sign-extend lower 32 bits of rd

Sail's SRLW extracts lower 32 bits of rs1 and rs2, logically right-shifts
the 32-bit value by rs2[4:0], sign-extends to 64, writes to rd.
-/

-- Factoring: execute_RTYPE SRL reads rs1, rs2, right-shifts v1 by extractLsb(v2, 5, 0).
theorem execute_RTYPE_SRL_factored (rs2 rs1 rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SRL = (do
      let v1 ← rX_bits rs1; let v2 ← rX_bits rs2
      wX_bits rd (shift_bits_right v1 (Sail.BitVec.extractLsb v2 (_root_.log2_xlen -i 1) 0))
      pure RETIRE_SUCCESS) := by
  sorry

-- Math bridge: truncating to 32 bits after a 64-bit logical right shift equals
-- right-shifting the truncated values with a truncated shift amount.
theorem extractLsb_srl (a b : BitVec 64) :
    Sail.BitVec.extractLsb
      (shift_bits_right a (Sail.BitVec.extractLsb b (_root_.log2_xlen -i 1) 0)) 31 0 =
    shift_bits_right (Sail.BitVec.extractLsb a 31 0)
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb b 31 0) 4 0) := by
  sorry

-- Jolt's SRLW: 64-bit SRL then sign-extend lower 32 bits.
def jolt_srlw (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let _ ← liftSail (execute_RTYPE rs2 rs1 rd rop.SRL)
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

-- Running Jolt's SRLW and projecting equals running Sail's SRLW.
theorem jolt_srlw_eq_sail (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_srlw rs2 rs1 rd).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.SRLW).run js.sail := by
  exact jolt_rtype_w_eq_sail rop.SRL ropw.SRLW
    (fun v1 v2 => shift_bits_right v1 (Sail.BitVec.extractLsb v2 (_root_.log2_xlen -i 1) 0))
    execute_RTYPE_SRL_factored
    (by intro a b; exact extractLsb_srl a b) rs2 rs1 rd hrd js hwf

end
