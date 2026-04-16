import JoltBytecode.EmbeddedSailJoltState.RtypeW
import JoltBytecode.EmbeddedSailJoltState.ShiftDefs

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do

set_option autoImplicit true

noncomputable section

-- From BytecodeExpansions/Instructions/Srlw.lean
def srlw_bitmask (rs2_val : BitVec 64) : Nat :=
  let v_bitmask_in := Riscv.ori rs2_val 32#64
  let shift := (v_bitmask_in.setWidth 6).toNat
  let ones := (1 <<< (64 - shift)) - 1
  ones <<< shift

lemma ctz_srlw_bitmask (rs2_val : BitVec 64) :
    ctz (srlw_bitmask rs2_val) = (rs2_val.setWidth 5).toNat + 32 := by
  sorry

/-! ## SRLW: Jolt's SLLI+bitmask+VirtualSRL+VSEW = Sail SRLW

Jolt decomposes SRLW into (from BytecodeExpansions/Srlw.lean):
1. SLLI v_rs1, rs1, 32          — left-shift rs1 by 32 (clears upper 32 bits)
2. ORI v_bitmask, rs2, 32       — set bit 5 of shift amount (shift + 32)
3. VirtualShiftRightBitmask      — compute bitmask from (shift + 32)
4. VirtualSRL rd, v_rs1, v_bitmask — logical right shift via ctz(bitmask)
5. VirtualSignExtendWord rd, rd   — sign-extend lower 32 bits

Sail's SRLW extracts lower 32 bits of rs1 and rs2, logically right-shifts
the 32-bit value by rs2[4:0], sign-extends to 64, writes to rd.
-/

-- ============================================================================
-- Bridge lemma
-- ============================================================================

-- Helper 1: (v <<< 32).toNat = v.toNat * 2^32 % 2^64.
-- Converts BitVec shiftLeft to Nat multiply without deep recursion.
-- (v <<< 32).toNat = v.toNat * 2^32 % 2^64.
-- Sorry'd — proving it triggers deep recursion in the kernel.
-- The fact is trivially true: shiftLeft by 32 = multiply by 2^32, mod 2^64 for BitVec 64.
-- (v <<< 32).toNat = v.toNat * 2^32 % 2^64.
-- Kernel deep recursion prevents proving this — the kernel tries to
-- reduce BitVec.shiftLeft on a 64-bit value by literal 32, which
-- creates 32 nested operations and blows the stack.
-- Needs a kernel-level workaround (e.g. native_decide, or a proof
-- that avoids touching the BitVec term).
lemma toNat_shl_32 (v : BitVec 64) :
    (v <<< 32).toNat = v.toNat * 2^32 % 2^64 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

-- Helper 2: (a * 2^32 % 2^64) / 2^(s+32) = a % 2^32 / 2^s, for s < 32.
-- Pure Nat identity about the shift-left-then-right cancellation.
lemma mul_mod_div_cancel (a s : Nat) (hs : s < 32) :
    a * 2^32 % 2^64 / 2^(s + 32) = a % 2^32 / 2^s := by
  have h1 : a * 2^32 % 2^64 = a % 2^32 * 2^32 := by omega
  have h2 : (2:Nat)^(s + 32) = 2^s * 2^32 := by
    have : (2:Nat)^32 = 2^32 := rfl
    rw [Nat.pow_add]
  rw [h1, h2, Nat.mul_div_mul_right _ _ (by positivity : (0:Nat) < 2^32)]

-- Helper 2: >>> 0 is identity on Nat.
lemma nat_shr_zero (n : Nat) : n >>> 0 = n := by simp

-- The core BitVec identity, proved using the helpers above.
lemma shl_shr_setWidth (v1 v2 : BitVec 64)
    (hs : (v2.setWidth 5).toNat < 32) :
    BitVec.extractLsb' 0 32 (v1 <<< 32 >>> ((v2.setWidth 5).toNat + 32)) =
    BitVec.extractLsb' 0 32 v1 >>> BitVec.extractLsb' 0 5 (BitVec.extractLsb' 0 32 v2) := by
  unfold BitVec.extractLsb'
  -- Goal: BitVec.ofNat 32 ((v1 <<< 32 >>> (s+32)).toNat >>> 0) =
  --       BitVec.ofNat 32 (v1.toNat >>> 0) >>> BitVec.ofNat 5 ((BitVec.ofNat 32 (v2.toNat >>> 0)).toNat >>> 0)
  simp only [nat_shr_zero]
  -- Goal: BitVec.ofNat 32 (v1 <<< 32 >>> (s+32)).toNat =
  --       BitVec.ofNat 32 v1.toNat >>> BitVec.ofNat 5 (BitVec.ofNat 32 v2.toNat).toNat
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
             Nat.reducePow]
  -- LHS: (v1 <<< 32).toNat / 2^(s+32) % 2^32
  -- RHS: (BitVec.ofNat 32 v1.toNat >>> BitVec.ofNat 5 (v2.toNat % 2^32)).toNat
  -- Step 1: convert LHS using helpers
  rw [toNat_shl_32 v1, mul_mod_div_cancel v1.toNat _ hs]
  -- LHS now: v1.toNat % 2^32 / 2^s % 2^32
  -- Step 2: % 2^32 is identity
  -- a % 2^32 / 2^s < 2^32 because a % 2^32 < 2^32 and division only makes smaller.
  simp only [Nat.reducePow]
  have hbound : v1.toNat % 4294967296 / 2 ^ (BitVec.setWidth 5 v2).toNat < 4294967296 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (by positivity))
  rw [Nat.mod_eq_of_lt hbound]
  -- RHS still has BitVec >>> BitVec. Convert to >>> Nat, then to / 2^n.
  change _ = (BitVec.ofNat 32 v1.toNat >>> (BitVec.ofNat 5 (v2.toNat % 4294967296)).toNat).toNat
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reducePow]
  -- Now both sides are Nat: v1.toNat % 4294967296 / 2^s = v1.toNat % 4294967296 / 2^(v2.toNat % 4294967296 % 32)
  have : v2.toNat % 4294967296 % 32 = (BitVec.setWidth 5 v2).toNat := by
    simp [BitVec.toNat_setWidth]
  rw [this]



-- The Jolt SRLW computation produces the same value as Sail's SRLW.
lemma srlw_shift_eq (v1 v2 : BitVec 64) :
    sign_extend (m := 64)
      (Sail.BitVec.extractLsb
        ((v1 <<< 32) >>> ctz (srlw_bitmask v2)) 31 0) =
    sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb v1 31 0)
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)) := by
  rw [show ctz (srlw_bitmask v2) = (v2.setWidth 5).toNat + 32 from ctz_srlw_bitmask v2]
  simp only [sign_extend, shift_bits_right, Sail.BitVec.signExtend,
             Sail.BitVec.extractLsb, BitVec.extractLsb,
             Nat.sub_zero, Nat.reduceAdd]
  congr 1
  have hs : (v2.setWidth 5).toNat < 32 := by
    have := (v2.setWidth 5).isLt; norm_num at this; exact this
  exact shl_shr_setWidth v1 v2 hs

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
def jolt_srlw (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let v1 ← liftSail (rX_bits rs1)
  writeVReg 0 (v1 <<< 32)
  let v2 ← liftSail (rX_bits rs2)
  let v_bitmask := srlw_bitmask v2
  let v_rs1 ← readVReg 0
  liftSail (wX_bits rd (v_rs1 >>> ctz v_bitmask))
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

-- ============================================================================
-- Concrete characterization
-- ============================================================================

-- After running Jolt's SRLW, rd holds the Sail SRLW value.
theorem jolt_srlw_concrete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v1 v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      rX_bits rs2 js.sail = .ok v2 js.sail ∧
      (jolt_srlw rs2 rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb v1 31 0)
          (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0))) := by
  unfold jolt_srlw jolt_virtual_sign_extend_word liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
             writeVReg, readVReg, modify, modifyGet, MonadStateOf.modifyGet,
             EStateM.modifyGet, get]
  obtain ⟨v1, hok1⟩ := hwf rs1
  obtain ⟨v2, hok2⟩ := hwf rs2
  simp only [hok1, hok2]
  dsimp only [getThe, MonadStateOf.get, EStateM.get]
  simp (config := { decide := true }) only [ite_true]
  obtain ⟨s3, hw1⟩ := wX_shape rd ((v1 <<< 32) >>> ctz (srlw_bitmask v2)) js.sail
  simp only [hw1]
  have hrx := wX_rX_roundtrip rd _ js.sail s3 hrd hw1
  simp only [hrx]
  obtain ⟨s4, hw2⟩ := wX_shape rd
    (sign_extend (m := 64) (Sail.BitVec.extractLsb ((v1 <<< 32) >>> ctz (srlw_bitmask v2)) 31 0)) s3
  simp only [hw2]
  have hc := wX_wX_collapse rd _ _ js.sail s3 s4 hw1 hw2
  refine ⟨_, v1, v2, rfl, rfl, rfl, ?_⟩
  rw [← srlw_shift_eq v1 v2]
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s4 hc

-- ============================================================================
-- Main theorem: Jolt SRLW = Sail SRLW
-- ============================================================================

-- Running Jolt's SRLW decomposition and projecting onto Sail state
-- equals running Sail's native SRLW instruction.
theorem jolt_srlw_eq_sail (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_srlw rs2 rs1 rd).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.SRLW).run js.sail := by
  obtain ⟨js', v1, v2, hj_rx1, hj_rx2, hj, hj_sail⟩ :=
    jolt_srlw_concrete rs2 rs1 rd hrd js hwf
  rw [execute_RTYPEW_SRLW_eq_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hj_rx1, hj_rx2]
  show projectResult ((jolt_srlw rs2 rs1 rd).run js) = _
  rw [hj]
  simp only [projectResult, project]
  rw [hj_sail]
  obtain ⟨s', hw⟩ := wX_shape rd _ js.sail
  rw [hw]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd _ js.sail s' hw).symm

end
