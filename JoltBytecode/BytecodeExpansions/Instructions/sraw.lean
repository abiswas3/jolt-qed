import JoltBytecode.BytecodeExpansions.Common.FormatR
import JoltBytecode.BytecodeExpansions.Common.Virtual
import JoltBytecode.BytecodeExpansions.Common.Riscv

/-!
# SRAW: RISC-V ≡ Jolt Decomposition

## Instruction (RV64I, Format R)

`SRAW rd, rs1, rs2` takes the lower 32 bits of rs1, arithmetic right
shifts by rs2[4:0], sign-extends the 32-bit result to 64 bits, and
writes to rd.

## Jolt Decomposition (faithful to Rust implementation)

```
VirtualSignExtendWord    v_rs1, rs1, 0               -- sign-extend rs1[31:0] to 64
ANDI                     v_shamt, rs2, 0x1f          -- mask shift amount to 5 bits
VirtualShiftRightBitmask v_bitmask, v_shamt, 0       -- compute bitmask from shift
VirtualSRA               rd, v_rs1, v_bitmask        -- arith right shift via ctz(bitmask)
VirtualSignExtendWord    rd, rd, 0                   -- sign-extend result to 64
```

## Proof

The bitmask has `shamt` trailing zeros, so `ctz(bitmask) = shamt = rs2[4:0]`.
The core identity is: sign-extending a 32-bit value to 64, then logically
right-shifting by s < 32, then truncating back to 32 and sign-extending,
equals directly performing an arithmetic right shift on the 32-bit value
and sign-extending. This holds because the sign-extended upper bits
propagate correctly through the logical shift for s < 32.
-/

-- ============================================================================
-- Bitmask computation (VirtualShiftRightBitmask, 64-bit mode)
-- ============================================================================

-- Matching Rust:
--   let shift = x & 0x3f;
--   let ones = (1u128 << (64 - shift)) - 1;
--   rd = (ones << shift) as i64;
def sraw_bitmask (shamt_val : BitVec 64) : Nat :=
  let shift := (shamt_val.setWidth 6).toNat
  let ones := (1 <<< (64 - shift)) - 1
  ones <<< shift

-- ============================================================================
-- ctz lemmas
-- ============================================================================

private lemma ctz_of_odd {n : Nat} (h : n % 2 = 1) : ctz n = 0 := by
  have hne : n ≠ 0 := by omega
  unfold ctz; rw [if_neg hne, if_pos h]

private lemma ctz_of_double {n : Nat} (hn : 0 < n) : ctz (2 * n) = 1 + ctz n := by
  have h1 : 2 * n ≠ 0 := by omega
  have h2 : ¬(2 * n % 2 = 1) := by omega
  have h3 : (2 * n) / 2 = n := by omega
  conv_lhs => unfold ctz
  rw [if_neg h1, if_neg h2, h3]

private lemma ctz_mul_pow2 (k : Nat) {m : Nat} (hm : 0 < m) :
    ctz (2 ^ k * m) = k + ctz m := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h_rw : 2 ^ (k + 1) * m = 2 * (2 ^ k * m) := by ring
    rw [h_rw, ctz_of_double (by positivity), ih]
    omega

private lemma pow2_sub_one_odd {k : Nat} (hk : 0 < k) : (2 ^ k - 1) % 2 = 1 := by
  cases k with
  | zero => omega
  | succ n =>
    rw [pow_succ, mul_comm]
    have : 0 < 2 ^ n := by positivity
    omega

-- ctz of VirtualShiftRightBitmask output recovers the shift amount.
lemma ctz_sraw_bitmask (shamt_val : BitVec 64) :
    ctz (sraw_bitmask shamt_val) = (shamt_val.setWidth 6).toNat := by
  unfold sraw_bitmask
  simp only [Nat.shiftLeft_eq, one_mul]
  set shift := (shamt_val.setWidth 6).toNat
  have h_lt : shift < 64 := by
    have := (shamt_val.setWidth 6).isLt
    norm_num at this; exact this
  have h_diff_pos : 0 < 64 - shift := by omega
  have h_m_pos : 0 < 2 ^ (64 - shift) - 1 := by
    have : 2 ≤ 2 ^ (64 - shift) :=
      le_trans (show (2 : Nat) ≤ 2 ^ 1 from by norm_num)
        (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  rw [mul_comm, ctz_mul_pow2 shift h_m_pos,
      ctz_of_odd (pow2_sub_one_odd h_diff_pos)]
  omega

-- The ANDI + bitmask + ctz chain recovers (rs2.setWidth 5).toNat.
private lemma ctz_sraw_chain (rs2_val : BitVec 64) :
    ctz (sraw_bitmask (Riscv.andi rs2_val 0x1f#64)) = (rs2_val.setWidth 5).toNat := by
  rw [ctz_sraw_bitmask]
  unfold Riscv.andi
  -- Goal: ((rs2_val &&& 0x1f#64).setWidth 6).toNat = (rs2_val.setWidth 5).toNat
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  -- Reduce 31 % 2^64 to 31, then rewrite 31 = 2^5 - 1 to use and_pow_two lemma
  have h1 : (31 : Nat) % 2 ^ 64 = 31 := by norm_num
  rw [h1, show (31 : Nat) = 2 ^ 5 - 1 from by norm_num, Nat.and_pow_two_sub_one_eq_mod]
  -- Goal: (rs2_val.toNat % 2^5) % 2^6 = rs2_val.toNat % 2^5
  exact Nat.mod_eq_of_lt (by have := Nat.mod_lt rs2_val.toNat (show 0 < 2 ^ 5 from by positivity); omega)

-- ============================================================================
-- Jolt decomposition
-- ============================================================================

-- Jolt's decomposition: VirtualSignExtendWord → ANDI → VirtualShiftRightBitmask
--   → VirtualSRA → VirtualSignExtendWord.
def srawJolt (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  let v_rs1     := Jolt.virtualSignExtendWord rs1_val
  let v_shamt   := Riscv.andi rs2_val 0x1f#64
  let v_bitmask := sraw_bitmask v_shamt
  let v_result  := v_rs1 >>> ctz v_bitmask
  Jolt.virtualSignExtendWord v_result

-- ============================================================================
-- Core lemma
-- ============================================================================

-- Arithmetic right shift of a 32-bit value equals: sign-extend to 64,
-- logical right shift, truncate back to 32.
private lemma sshiftRight_eq_signExtend_ushr_trunc (x : BitVec 32) (s : Nat) (hs : s < 32) :
    x.sshiftRight s = (x.signExtend 64 >>> s).setWidth 32 := by
  ext i
  simp only [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_setWidth,
             BitVec.getLsbD_ushiftRight, BitVec.getLsbD_signExtend]
  simp [i.isLt, show ¬(32 ≤ (↑i : Nat)) from by omega,
        show s + (↑i : Nat) < 64 from by omega]

-- ============================================================================
-- Main theorems
-- ============================================================================

-- Pure-function equivalence: Riscv.sraw = srawJolt
theorem sraw_eq_srawJolt (rs1_val rs2_val : BitVec 64) :
    Riscv.sraw rs1_val rs2_val = srawJolt rs1_val rs2_val := by
  unfold Riscv.sraw srawJolt Jolt.virtualSignExtendWord
  simp only [ctz_sraw_chain]
  have hs : (rs2_val.setWidth 5).toNat < 32 := by
    have := (rs2_val.setWidth 5).isLt
    norm_num at this; exact this
  congr 1
  rw [sshiftRight_eq_signExtend_ushr_trunc (rs1_val.setWidth 32) _ hs]

-- State-level equivalence via Format R lifting.
theorem sraw_state_eq (rs1 rs2 rd : BitVec 5) (s : State) :
    format_r_exec rs1 rs2 rd Riscv.sraw s = format_r_exec rs1 rs2 rd srawJolt s :=
  format_r_ops_eq_of_fns_eq Riscv.sraw srawJolt rs1 rs2 rd s
    (by funext rs1_val rs2_val; exact sraw_eq_srawJolt rs1_val rs2_val)

/-SANITY CHECKS-/
-- Exhaustive check: verify Riscv.sraw == srawJolt for 256 values × 32 shift amounts
#eval do
  let mut failures := 0
  for i in List.range 256 do
    for s in List.range 32 do
      let rs1_val : BitVec 64 := BitVec.ofNat 64 i
      let rs2_val : BitVec 64 := BitVec.ofNat 64 s
      if Riscv.sraw rs1_val rs2_val != srawJolt rs1_val rs2_val then
        failures := failures + 1
  if failures == 0 then
    IO.println "✓ Exhaustive check passed: sraw == srawJolt for all 8192 test pairs"
  else
    IO.println s!"✗ FAILED: {failures} mismatches found"
