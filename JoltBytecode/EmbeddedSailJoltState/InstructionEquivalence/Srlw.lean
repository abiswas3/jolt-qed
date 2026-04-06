import JoltBytecode.EmbeddedSailJoltState.RtypeW
import JoltBytecode.BytecodeExpansions.Instructions.Srlw

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do

set_option autoImplicit true

noncomputable section

/-! ## SRLW: Jolt's SLLI+bitmask+VirtualSRL+VSEW = Sail SRLW

Jolt decomposes SRLW into (from BytecodeExpansions/Srlw.lean):
1. SLLI v_rs1, rs1, 32          — left-shift rs1 by 32 (clears upper 32 bits)
2. ORI v_bitmask, rs2, 32       — set bit 5 of shift amount (shift + 32)
3. VirtualShiftRightBitmask      — compute bitmask from (shift + 32)
4. VirtualSRL rd, v_rs1, v_bitmask — logical right shift via ctz(bitmask)
5. VirtualSignExtendWord rd, rd   — sign-extend lower 32 bits

The SLLI 32 pushes the lower 32 bits of rs1 to the upper half.
ORI 32 makes the shift amount (rs2[4:0] + 32). Right-shifting by
(s+32) after left-shifting by 32 extracts the lower 32 bits shifted
right by s — which is exactly what SRLW does.

Sail's SRLW extracts lower 32 bits of rs1 and rs2, logically right-shifts
the 32-bit value by rs2[4:0], sign-extends to 64, writes to rd.
-/

-- ============================================================================
-- Bridge lemma
-- ============================================================================

-- The Jolt SRLW computation (SLLI 32, ORI 32, bitmask shift, VSEW) produces
-- the same value as Sail's SRLW (extract 32 bits, logical right shift).
-- The SLLI+bitmask Jolt SRLW computation produces the same value as Sail's SRLW.
-- Jolt: left-shift by 32 (clear upper bits), right-shift by (rs2[4:0]+32) via bitmask.
-- Sail: extract lower 32, logical right shift by rs2[4:0].
-- These are equal: shifting up by 32 then down by (s+32) = extracting and shifting by s.
private lemma srlw_shift_eq (v1 v2 : BitVec 64) :
    sign_extend (m := 64)
      (Sail.BitVec.extractLsb
        ((v1 <<< 32) >>> ctz (srlw_bitmask v2)) 31 0) =
    sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb v1 31 0)
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)) := by
  -- Step 1: recover shift amount from bitmask. ctz(srlw_bitmask v2) = s + 32.
  rw [show ctz (srlw_bitmask v2) = (v2.setWidth 5).toNat + 32 from ctz_srlw_bitmask v2]
  -- Step 2: unfold Sail wrappers to plain BitVec.
  simp only [sign_extend, shift_bits_right, Sail.BitVec.signExtend, Sail.BitVec.toNatInt,
             Sail.BitVec.extractLsb, BitVec.extractLsb, Int.ofNat_eq_natCast, Int.toNat_natCast,
             Nat.sub_zero, Nat.reduceAdd]
  -- Step 3: strip signExtend from both sides.
  congr 1
  -- Step 4: bit-by-bit. (v1 <<< 32) >>> (s+32) at bit i = v1[i+s] if i+s < 32.
  -- v1.setWidth 32 >>> s at bit i = v1[i+s] if i+s < 32. Same.
  ext i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight,
             BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
             BitVec.toNat_setWidth, Nat.sub_zero, Nat.reduceAdd]
  sorry

-- ============================================================================
-- Factoring
-- ============================================================================

-- Sail's SRLW reads rs1, rs2, extracts lower 32 bits, logically right-shifts
-- by rs2[4:0], sign-extends, writes to rd.
theorem execute_RTYPEW_SRLW_eq_factored (rs2 rs1 rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.SRLW = (do
      let v1 ← rX_bits rs1; let v2 ← rX_bits rs2
      wX_bits rd (sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb v1 31 0)
        (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)))
      pure RETIRE_SUCCESS) := by
  simp [execute_RTYPEW, bind_pure_comp, pure_bind]

-- ============================================================================
-- Jolt SRLW definition (faithful to BytecodeExpansions/Srlw.lean)
-- ============================================================================

-- Jolt's SRLW decomposition: SLLI 32 + bitmask + VirtualSRL + VSEW.
-- Step 1: Left-shift rs1 by 32 (pushes lower 32 bits to upper half).
-- Step 2: Compute bitmask from ORI(rs2, 32) (shift amount + 32).
-- Step 3: Logical right shift by ctz(bitmask), write to rd.
-- Step 4: Sign-extend lower 32 bits (VSEW).
def jolt_srlw (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  -- Step 1: SLLI rs1, 32 → virtual register 0
  let v1 ← liftSail (rX_bits rs1)
  writeVReg 0 (v1 <<< 32)
  -- Step 2: compute bitmask from rs2 (ORI 32 + VirtualShiftRightBitmask)
  let v2 ← liftSail (rX_bits rs2)
  let v_bitmask := srlw_bitmask v2
  -- Step 3: VirtualSRL — logical right shift via ctz(bitmask), write to rd
  let v_rs1 ← readVReg 0
  liftSail (wX_bits rd (v_rs1 >>> ctz v_bitmask))
  -- Step 4: VirtualSignExtendWord rd
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

-- ============================================================================
-- Main theorem: Jolt SRLW = Sail SRLW
-- ============================================================================

-- Running Jolt's SRLW decomposition and projecting onto Sail state
-- equals running Sail's native SRLW instruction.
theorem jolt_srlw_eq_sail (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_srlw rs2 rs1 rd).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.SRLW).run js.sail := by
  rw [execute_RTYPEW_SRLW_eq_factored]
  unfold jolt_srlw jolt_virtual_sign_extend_word liftSail projectResult
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
             writeVReg, readVReg, modify, modifyGet, MonadStateOf.modifyGet,
             EStateM.modifyGet, get]
  -- Under WellFormed, both register reads succeed.
  obtain ⟨v1, hok1⟩ := hwf rs1
  obtain ⟨v2, hok2⟩ := hwf rs2
  simp only [hok1, hok2]
  -- Reduce vreg operations
  dsimp only [getThe, MonadStateOf.get, EStateM.get]
  simp (config := { decide := true }) only [ite_true, project]
  -- Both sides write to rd then VSEW.
  obtain ⟨s3, hw1⟩ := wX_shape rd (v1 <<< 32 >>> ctz (srlw_bitmask v2)) js.sail
  simp only [hw1]
  have hrx := wX_rX_roundtrip rd _ js.sail s3 hrd hw1
  simp only [hrx]
  -- Apply the bridge: SLLI+bitmask+shift = SRLW
  rw [srlw_shift_eq v1 v2]
  -- Collapse double write
  obtain ⟨s4, hw2⟩ := wX_shape rd
    (sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb v1 31 0)
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0))) s3
  have hc := wX_wX_collapse rd _ _ js.sail s3 s4 hw1 hw2
  simp [hw2, hc]

end
