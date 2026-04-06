import JoltBytecode.EmbeddedSailJoltState.RtypeW

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-! ## SLLW: Jolt's 64-bit SLL then sign-extend-word = Sail's SLLW

Jolt decomposes SLLW as:
1. SLL rd, rs1, rs2  — 64-bit left shift (shift amount = rs2[5:0])
2. VSEW rd           — sign-extend lower 32 bits of rd

Sail's SLLW extracts lower 32 bits of rs1 and rs2, left-shifts the
32-bit value by rs2[4:0], sign-extends to 64, writes to rd.

The math bridge: truncating to 32 bits after a 64-bit left shift
equals left-shifting the truncated values with a truncated shift amount.
-/

-- Factoring: execute_RTYPE SLL reads rs1, rs2, left-shifts v1 by extractLsb(v2, 5, 0).
theorem execute_RTYPE_SLL_factored (rs2 rs1 rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SLL = (do
      let v1 ← rX_bits rs1; let v2 ← rX_bits rs2
      wX_bits rd (shift_bits_left v1 (Sail.BitVec.extractLsb v2 (_root_.log2_xlen -i 1) 0))
      pure RETIRE_SUCCESS) := by
  sorry

-- Math bridge: truncating to 32 bits after a 64-bit left shift equals
-- left-shifting the truncated values with a truncated shift amount.
theorem extractLsb_sll (a b : BitVec 64) :
    Sail.BitVec.extractLsb
      (shift_bits_left a (Sail.BitVec.extractLsb b (_root_.log2_xlen -i 1) 0)) 31 0 =
    shift_bits_left (Sail.BitVec.extractLsb a 31 0)
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb b 31 0) 4 0) := by
  sorry

-- Jolt's SLLW: 64-bit SLL then sign-extend lower 32 bits.
def jolt_sllw (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let _ ← liftSail (execute_RTYPE rs2 rs1 rd rop.SLL)
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

-- Running Jolt's SLLW and projecting equals running Sail's SLLW.
theorem jolt_sllw_eq_sail (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_sllw rs2 rs1 rd).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.SLLW).run js.sail := by
  exact jolt_rtype_w_eq_sail rop.SLL ropw.SLLW
    (fun v1 v2 => shift_bits_left v1 (Sail.BitVec.extractLsb v2 (_root_.log2_xlen -i 1) 0))
    execute_RTYPE_SLL_factored
    (by intro a b; exact extractLsb_sll a b) rs2 rs1 rd hrd js hwf

end
