import JoltBytecode.BytecodeExpansions.Common.FormatI
import JoltBytecode.BytecodeExpansions.Common.Virtual
import JoltBytecode.BytecodeExpansions.Common.Riscv

/-!
# SRLIW: RISC-V ≡ Jolt Decomposition

## Instruction (RV64I, Format I)

`SRLIW rd, rs1, shamt` takes the lower 32 bits of rs1, shifts right
logically by shamt[4:0], sign-extends the 32-bit result to 64 bits, and
writes to rd.

## Jolt Decomposition (faithful to Rust implementation)

```
SLLI                  v0, rs1, 32                        -- zero upper bits via shift
shift := (shamt & 0x1f) + 32                             -- 5-bit shift amount + 32
ones  := (1 <<< (64 - shift)) - 1                        -- (64-shift) one-bits
mask  := ones <<< shift                                   -- bitmask for VirtualSRLI
VirtualSRLI           v0, v0, mask                        -- shift right by ctz(mask) = shift
VirtualSignExtendWord rd, v0, 0                           -- sign-extend lower 32 bits
```

## Proof

The bitmask has `shift` trailing zeros, so `ctz(mask) = shift = shamt[4:0] + 32`.
Shifting left by 32 then right by (shamt + 32) extracts exactly the
lower 32 bits shifted right by shamt: the SLLI clears the upper 32
bits by pushing lower 32 to the top, and the combined right shift
recovers them in the correct position. Truncation to 32 bits then
matches the direct 32-bit shift, and sign-extension completes the
equivalence.
-/

-- ============================================================================
-- Bitmask computation (faithful to Jolt Rust implementation)
-- ============================================================================

-- Jolt's SRLIW bitmask, matching the Rust code:
--   let shift = (imm & 0x1f) + 32;
--   let len = 64;
--   let ones = (1u128 << (len - shift)) - 1;
--   let bitmask = (ones << shift) as u64;
def srliw_imm (shamt : BitVec 64) : Nat :=
  let shift := (shamt.setWidth 5).toNat + 32
  let len := 64
  let ones := (1 <<< (len - shift)) - 1
  ones <<< shift

-- ============================================================================
-- ctz lemmas for the bitmask
-- ============================================================================

-- An odd number has zero trailing zeros.
private lemma ctz_of_odd {n : Nat} (h : n % 2 = 1) : ctz n = 0 := by
  have hne : n ≠ 0 := by omega
  unfold ctz
  rw [if_neg hne]
  rw [if_pos h]

-- Doubling a positive number adds one trailing zero.
private lemma ctz_of_double {n : Nat} (hn : 0 < n) : ctz (2 * n) = 1 + ctz n := by
  have h1 : 2 * n ≠ 0 := by omega
  have h2 : ¬(2 * n % 2 = 1) := by omega
  have h3 : (2 * n) / 2 = n := by omega
  conv_lhs => unfold ctz
  rw [if_neg h1, if_neg h2, h3]

-- Multiplying by 2^k adds k trailing zeros.
private lemma ctz_mul_pow2 (k : Nat) {m : Nat} (hm : 0 < m) :
    ctz (2 ^ k * m) = k + ctz m := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h_rw : 2 ^ (k + 1) * m = 2 * (2 ^ k * m) := by ring
    rw [h_rw, ctz_of_double (by positivity), ih]
    omega

-- 2^k - 1 is odd for k > 0.
private lemma pow2_sub_one_odd {k : Nat} (hk : 0 < k) : (2 ^ k - 1) % 2 = 1 := by
  cases k with
  | zero => omega
  | succ n =>
    rw [pow_succ, mul_comm]
    have : 0 < 2 ^ n := by positivity
    omega

-- ctz of Jolt's bitmask recovers the shift amount.
-- The number of trailing zeros in srliw_imm x 
-- is exactly exqual to x[0:4] + 32
lemma ctz_srliw_imm (shamt : BitVec 64) :
    ctz (srliw_imm shamt) = (shamt.setWidth 5).toNat + 32 := by
  unfold srliw_imm
  simp only [Nat.shiftLeft_eq, one_mul]
  have h_lt : (shamt.setWidth 5).toNat < 32 := by
    have := (shamt.setWidth 5).isLt
    norm_num at this
    exact this
  have h_diff_pos : 0 < 64 - ((shamt.setWidth 5).toNat + 32) := by omega
  have h_m_pos : 0 < 2 ^ (64 - ((shamt.setWidth 5).toNat + 32)) - 1 := by
    have : 2 ≤ 2 ^ (64 - ((shamt.setWidth 5).toNat + 32)) :=
      le_trans (show (2 : Nat) ≤ 2 ^ 1 from by norm_num)
        (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  rw [mul_comm,
      ctz_mul_pow2 ((shamt.setWidth 5).toNat + 32) h_m_pos,
      ctz_of_odd (pow2_sub_one_odd h_diff_pos)]

-- ============================================================================
-- Jolt decomposition
-- ============================================================================

-- Jolt's decomposition: SLLI → bitmask → VirtualSRLI → VirtualSignExtendWord.
-- TODO: Move this into name space Jolt
def srliwJolt (rs1_val shamt : BitVec 64) : BitVec 64 :=
  let v0   := Riscv.slli rs1_val 32
  let mask := srliw_imm shamt
  let v0   := Jolt.virtualSRLI v0 mask
  Jolt.virtualSignExtendWord v0

-- ============================================================================
-- Supporting shift lemmas
-- ============================================================================

-- Shift associativity for BitVec.
private lemma ushiftRight_add {w : Nat} (x : BitVec w) (a b : Nat) :
    x >>> (a + b) = (x >>> a) >>> b := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_add]

-- Shift left by 32 then right by 32 = zero-extend lower 32 bits.
private lemma sll32_srl32_eq_zext (x : BitVec 64) :
    (x <<< 32) >>> 32 = (x.setWidth 32).setWidth 64 := by
  bv_omega

-- Zero-extend, shift right, truncate = shift the 32-bit value directly.
private lemma zext_srl_trunc_32 (x : BitVec 64) (n : Nat) :
    ((x.setWidth 32).setWidth 64 >>> n).setWidth 32 = (x.setWidth 32) >>> n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h : x.toNat % 2 ^ 32 % 2 ^ 64 = x.toNat % 2 ^ 32 :=
    Nat.mod_eq_of_lt (by have := Nat.mod_lt x.toNat (show 0 < 2 ^ 32 by omega); omega)
  rw [h]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (by omega)))

-- SLLI 32 then VSRLI (n+32), truncated to 32 = direct 32-bit shift right by n.
private lemma slli_vsrli_trunc_32 (x : BitVec 64) (n : Nat) :
    ((x <<< 32) >>> (n + 32)).setWidth 32 = (x.setWidth 32) >>> n := by
  rw [show n + 32 = 32 + n from by omega]
  rw [ushiftRight_add]
  rw [sll32_srl32_eq_zext]
  exact zext_srl_trunc_32 x n

-- ============================================================================
-- Main theorems
-- ============================================================================

-- Pure-function equivalence: Riscv.srliw = srliwJolt
theorem srliw_eq_srliwJolt (rs1_val shamt : BitVec 64) :
    Riscv.srliw rs1_val shamt = srliwJolt rs1_val shamt := by
  unfold Riscv.srliw srliwJolt Riscv.slli Jolt.virtualSRLI Jolt.virtualSignExtendWord
  congr 
  simp only [ctz_srliw_imm]
  simp only [slli_vsrli_trunc_32]

-- State-level equivalence via Format I lifting.
theorem srliw_state_eq (rs1 rd : BitVec 5) (imm : BitVec 64) (s : State) :
    format_i_exec rs1 rd imm Riscv.srliw s = format_i_exec rs1 rd imm srliwJolt s :=
  format_i_ops_eq_of_fns_eq Riscv.srliw srliwJolt rs1 rd imm s
    (by funext rs1_val shamt; exact srliw_eq_srliwJolt rs1_val shamt)

/-SANITY CHECKS-/
-- Exhaustive check: verify Riscv.srliw == srliwJolt for 256 values × 64 shift amounts
#eval do
  let mut failures := 0
  for i in List.range 256 do
    for s in List.range 64 do
      let rs1_val : BitVec 64 := BitVec.ofNat 64 i
      let shamt : BitVec 64 := BitVec.ofNat 64 s
      if Riscv.srliw rs1_val shamt != srliwJolt rs1_val shamt then
        failures := failures + 1
  if failures == 0 then
    IO.println "✓ Exhaustive check passed: srliw == srliwJolt for all 16384 test pairs"
  else
    IO.println s!"✗ FAILED: {failures} mismatches found"
