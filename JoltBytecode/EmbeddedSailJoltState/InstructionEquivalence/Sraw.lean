import JoltBytecode.EmbeddedSailJoltState.RtypeW

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-! ## SRAW: Jolt's 64-bit SRA then sign-extend-word = Sail's SRAW

Jolt decomposes SRAW as:
1. SRA rd, rs1, rs2  — 64-bit arithmetic right shift (shift amount = rs2[5:0])
2. VSEW rd           — sign-extend lower 32 bits of rd

Sail's SRAW extracts lower 32 bits of rs1 and rs2, arithmetically right-shifts
the 32-bit value by rs2[4:0], sign-extends to 64, writes to rd.
-/

-- Factoring: execute_RTYPE SRA reads rs1, rs2, arithmetically right-shifts v1.
theorem execute_RTYPE_SRA_factored (rs2 rs1 rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SRA = (do
      let v1 ← rX_bits rs1; let v2 ← rX_bits rs2
      wX_bits rd (shift_bits_right_arith v1 (Sail.BitVec.extractLsb v2 (_root_.log2_xlen -i 1) 0))
      pure RETIRE_SUCCESS) := by
  sorry

-- Math bridge: truncating to 32 bits after a 64-bit arithmetic right shift equals
-- arithmetically right-shifting the truncated values with a truncated shift amount.
theorem extractLsb_sra (a b : BitVec 64) :
    Sail.BitVec.extractLsb
      (shift_bits_right_arith a (Sail.BitVec.extractLsb b (_root_.log2_xlen -i 1) 0)) 31 0 =
    shift_bits_right_arith (Sail.BitVec.extractLsb a 31 0)
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb b 31 0) 4 0) := by
  sorry

-- Jolt's SRAW: 64-bit SRA then sign-extend lower 32 bits.
def jolt_sraw (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let _ ← liftSail (execute_RTYPE rs2 rs1 rd rop.SRA)
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

-- Running Jolt's SRAW and projecting equals running Sail's SRAW.
theorem jolt_sraw_eq_sail (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_sraw rs2 rs1 rd).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.SRAW).run js.sail := by
  exact jolt_rtype_w_eq_sail rop.SRA ropw.SRAW
    (fun v1 v2 => shift_bits_right_arith v1 (Sail.BitVec.extractLsb v2 (_root_.log2_xlen -i 1) 0))
    execute_RTYPE_SRA_factored
    (by intro a b; exact extractLsb_sra a b) rs2 rs1 rd hrd js hwf

end
