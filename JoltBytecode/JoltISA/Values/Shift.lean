import Mathlib.Tactic
import Mathlib.Data.BitVec

/-!
# Shared Pure Definitions for Shift Instruction Proofs

Extracted from the deleted `BytecodeExpansions/` directory. Contains:
- `ctz` (count trailing zeros) and its lemmas
- `Jolt.*` virtual instruction definitions (pure functions)
- `Riscv.*` pure instruction definitions (used in Jolt decompositions)
- Shared shift/bitmask lemmas
-/

-- ============================================================================
-- Count trailing zeros
-- ============================================================================

/-- Count trailing zeros of a natural number. Returns 0 for input 0. -/
def ctz (n : Nat) : Nat :=
  if n = 0 then 0
  else if n % 2 = 1 then 0
  else 1 + ctz (n / 2)
termination_by n

@[simp] lemma ctz_pow2 (n : Nat) : ctz (2 ^ n) = n := by
  induction n with
  | zero => unfold ctz; simp
  | succ k ih =>
    unfold ctz
    rw [if_neg (show 2 ^ (k + 1) ≠ 0 from Nat.pos_iff_ne_zero.mp (by positivity))]
    rw [if_neg (show ¬(2 ^ (k + 1) % 2 = 1) from by rw [pow_succ]; omega)]
    rw [show 2 ^ (k + 1) / 2 = 2 ^ k from by rw [pow_succ]; omega]
    rw [ih]; omega

lemma ctz_of_odd {n : Nat} (h : n % 2 = 1) : ctz n = 0 := by
  have hne : n ≠ 0 := by omega
  unfold ctz; rw [if_neg hne, if_pos h]

lemma ctz_of_double {n : Nat} (hn : 0 < n) : ctz (2 * n) = 1 + ctz n := by
  have h1 : 2 * n ≠ 0 := by omega
  have h2 : ¬(2 * n % 2 = 1) := by omega
  have h3 : (2 * n) / 2 = n := by omega
  conv_lhs => unfold ctz
  rw [if_neg h1, if_neg h2, h3]

lemma ctz_mul_pow2 (k : Nat) {m : Nat} (hm : 0 < m) :
    ctz (2 ^ k * m) = k + ctz m := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h_rw : 2 ^ (k + 1) * m = 2 * (2 ^ k * m) := by ring
    rw [h_rw, ctz_of_double (by positivity), ih]
    omega

lemma pow2_sub_one_odd {k : Nat} (hk : 0 < k) : (2 ^ k - 1) % 2 = 1 := by
  cases k with
  | zero => omega
  | succ n =>
    rw [pow_succ, mul_comm]
    have : 0 < 2 ^ n := by positivity
    omega

-- ============================================================================
-- Riscv pure-function definitions (used in Jolt decompositions)
-- ============================================================================

namespace Riscv

variable {w : Nat}

def mul (x y : BitVec w) : BitVec w := x * y
def slli (x : BitVec w) (shamt : Nat) : BitVec w := x <<< shamt
def ori (x imm : BitVec w) : BitVec w := x ||| imm
def andi (x y : BitVec w) : BitVec w := x &&& y

def sllw (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  ((rs1_val.setWidth 32) <<< (rs2_val.setWidth 5).toNat).signExtend 64

def srlw (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  ((rs1_val.setWidth 32) >>> (rs2_val.setWidth 5).toNat).signExtend 64

def sraw (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  ((rs1_val.setWidth 32).sshiftRight (rs2_val.setWidth 5).toNat).signExtend 64

def sll (x y : BitVec 64) : BitVec 64 := x <<< (y.setWidth 6).toNat
def srl (x y : BitVec 64) : BitVec 64 := x >>> (y.setWidth 6).toNat
def sra (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  rs1_val.sshiftRight (rs2_val.setWidth 6).toNat

def slli64 (rs1_val shamt : BitVec 64) : BitVec 64 := rs1_val <<< (shamt.setWidth 6).toNat
def srli64 (rs1_val shamt : BitVec 64) : BitVec 64 := rs1_val >>> (shamt.setWidth 6).toNat
def srai64 (rs1_val shamt : BitVec 64) : BitVec 64 := rs1_val.sshiftRight (shamt.setWidth 6).toNat

def slliw (rs1_val shamt : BitVec 64) : BitVec 64 :=
  ((rs1_val.setWidth 32) <<< (shamt.setWidth 5).toNat).signExtend 64

def srliw (rs1_val shamt : BitVec 64) : BitVec 64 :=
  ((rs1_val.setWidth 32) >>> (shamt.setWidth 5).toNat).signExtend 64

def sraiw (rs1_val shamt : BitVec 64) : BitVec 64 :=
  ((rs1_val.setWidth 32).sshiftRight (shamt.setWidth 5).toNat).signExtend 64

end Riscv

-- ============================================================================
-- Jolt virtual instruction definitions
-- ============================================================================

namespace Jolt

variable {w : Nat}

def virtualSignExtendWord (z : BitVec 64) : BitVec 64 :=
  (z.setWidth 32).signExtend 64

def virtualPow2 (x : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (2 ^ (x.setWidth 6).toNat)

def virtualPow2W (x : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (2 ^ (x.setWidth 5).toNat)

def virtualSRLI (x : BitVec w) (imm : Nat) : BitVec w :=
  x >>> ctz imm

end Jolt

-- ============================================================================
-- Shared shift lemmas
-- ============================================================================

@[simp]
lemma shiftLeft_eq_mul_pow2 (x : BitVec 64) (s : Nat) :
    x <<< s = x * BitVec.ofNat 64 (2 ^ s) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.shiftLeft_eq]

lemma sshiftRight_eq_signExtend_ushr_trunc (x : BitVec 32) (s : Nat) (hs : s < 32) :
    x.sshiftRight s = (x.signExtend 64 >>> s).setWidth 32 := by
  ext i hi
  simp only [BitVec.getElem_sshiftRight, BitVec.getElem_setWidth,
             BitVec.getLsbD_ushiftRight, BitVec.getLsbD_signExtend]
  simp only [show s + i < 64 from by omega, decide_true, Bool.true_and]
  split
  · rename_i hsi; simp [BitVec.getLsbD_eq_getElem, hsi]
  · rfl
