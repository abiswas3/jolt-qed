import Mathlib.Tactic
import Mathlib.Data.BitVec

/-!
# MULH Equivalence Theorem (Compositional Version)

We formally verify that the RISC-V `MULH` instruction (signed high multiplication)
computes the same result as Jolt's replacement sequence of virtual instructions.

## Background

The RISC-V `MULH rd, rs1, rs2` instruction computes the upper `w` bits of the
signed product of `rs1` and `rs2`, storing the result in `rd`.

In Jolt, this single instruction is replaced by a sequence of virtual instructions:
```
VirtualMovsign  v_sx, rs1, 0      -- s_x = sign(rs1)
VirtualMovsign  v_sy, rs2, 0      -- s_y = sign(rs2)
MULHU           v_0,  rs1, rs2    -- v_0 = floor(x' * y' / 2^w)  (unsigned high mul)
MUL             v_sx, v_sx, rs2   -- v_sx = s_x * y'
MUL             v_sy, v_sy, rs1   -- v_sy = s_y * x'
ADD             v_0,  v_0,  v_sx  -- v_0 = floor(x'*y'/2^w) + s_x*y'
ADD             rd,   v_0,  v_sy  -- rd  = floor(x'*y'/2^w) + s_x*y' + s_y*x'
```

Each instruction is defined as a separate function, and `mulhJolt` is their composition.

## Definitions

- `signExtract x`         : the sign function s(x), returns -1 if x < 0, else 0 (Int-valued)
- `Jolt.virtualMovSign x` : sign extraction as a BitVec (allOnes if negative, 0 otherwise)
- `Jolt.mulhu x y`        : unsigned high multiplication (upper w bits of unsigned product)
- `mulh x y`              : the RISC-V MULH instruction: floor(toInt(x) * toInt(y) / 2^w)
- `mulhJolt x y`          : Jolt's decomposition as a sequence of virtual instructions

MUL and ADD are standard BitVec `*` and `+` (modular arithmetic), so we use the
built-in operations directly.

## Proof Strategy

1. **Bridging lemmas**: Show each virtual instruction's BitVec output corresponds to the
   Int-valued expression used in the mathematical proof.

2. **Signed ↔ Unsigned**: Show `toInt(x) = toNat(x) + signExtract(x) * 2^w`.

3. **Product Expansion**: Substitute the above into `toInt(x) * toInt(y)` and expand.

4. **Division**: Divide by 2^w. Terms that are exact multiples of 2^w collapse.

5. **Mod 2^w**: The extra `s_x*s_y*2^w` term vanishes mod 2^w, giving us the result.

## Key Lean 4 lemmas used

- `BitVec.ofInt_add`           : ofInt distributes over addition
- `BitVec.toInt_eq_msb_cond`   : characterizes toInt via msb case split
- `BitVec.eq_of_toInt_eq`      : two BitVecs are equal iff their toInt values are equal
- `BitVec.toInt_ofInt`          : toInt(ofInt(i)) = i.bmod(2^w)
- `Int.add_mul_ediv_right`      : (a + b*c) / c = a/c + b  (for c ≠ 0)
- `Int.bmod_add_mul_cancel`     : bmod(x + n*k, n) = bmod(x, n)
-/

section MULH

variable {w : Nat}

-- ============================================================================
-- DEFINITIONS
-- ============================================================================

/-- Sign extraction: returns -1 if the bitvector is negative (msb set), 0 otherwise.
    This is the Int-valued version used in mathematical reasoning. -/
def signExtract (x : BitVec w) : Int :=
  if x.msb then -1 else 0

-- Virtual instruction definitions for Jolt's bytecode expansion.
namespace Jolt

/-- VirtualMovSign: extracts the sign bit as a w-bit register value.
    Produces allOnes (two's complement -1) if negative, 0 otherwise.
    This is the BitVec-valued counterpart of `signExtract`. -/
def virtualMovSign (x : BitVec w) : BitVec w :=
  BitVec.ofInt w (signExtract x)

/-- MULHU: unsigned high multiplication.
    Computes the upper w bits of the unsigned product of x and y:
      floor(toNat(x) * toNat(y) / 2^w) -/
def mulhu (x y : BitVec w) : BitVec w :=
  BitVec.ofNat w (x.toNat * y.toNat / 2 ^ w)

end Jolt

/-- The RISC-V MULH instruction: computes the upper w bits of the signed product.
    Given two w-bit signed integers x and y, MULH returns:
      floor(toInt(x) * toInt(y) / 2^w)  mod 2^w -/
def mulh (x y : BitVec w) : BitVec w :=
  BitVec.ofInt w (x.toInt * y.toInt / (2 ^ w : Int))

/-- The Jolt virtual instruction decomposition for MULH.
    Each line corresponds to a virtual instruction in the expansion sequence.
    MUL and ADD are standard BitVec `*` and `+` (modular arithmetic). -/
def mulhJolt (x y : BitVec w) : BitVec w :=
  let v_sx := Jolt.virtualMovSign x       -- VirtualMovsign v_sx, rs1, 0
  let v_sy := Jolt.virtualMovSign y       -- VirtualMovsign v_sy, rs2, 0
  let v_0  := Jolt.mulhu x y              -- MULHU v_0, rs1, rs2
  let v_sx := v_sx * y                    -- MUL v_sx, v_sx, rs2
  let v_sy := v_sy * x                    -- MUL v_sy, v_sy, rs1
  let v_0  := v_0 + v_sx                  -- ADD v_0, v_0, v_sx
  v_0 + v_sy                              -- ADD rd,  v_0, v_sy

-- ============================================================================
-- BRIDGING LEMMAS: Connecting BitVec instructions to Int expressions
-- ============================================================================

/-! ## Bridging Lemmas

These lemmas connect the BitVec-valued virtual instruction outputs to the
Int-valued expressions used in the mathematical proof. The key insight is that
`BitVec.ofInt` distributes over addition (`BitVec.ofInt_add`), so composing
individual instructions is equivalent to a single `BitVec.ofInt` of their sum. -/

/-- VirtualMovSign as a BitVec equals ofInt of signExtract (definitional). -/
lemma virtualMovSign_eq_ofInt (x : BitVec w) :
    Jolt.virtualMovSign x = BitVec.ofInt w (signExtract x) := rfl

/-- The product of virtualMovSign and a bitvector equals the ofInt of the
    corresponding Int product. This bridges the MUL instruction's BitVec
    output to the Int expression `signExtract(x) * toNat(y)`. -/
lemma virtualMovSign_mul_eq (x y : BitVec w) :
    Jolt.virtualMovSign x * y =
      BitVec.ofInt w (signExtract x * (y.toNat : Int)) := by
  rw [virtualMovSign_eq_ofInt]
  have hy : y = BitVec.ofInt w (↑y.toNat : Int) := by
    rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  conv_lhs => rw [hy]
  rw [← BitVec.ofInt_mul]

/-- MULHU as a BitVec equals ofInt of the corresponding Int expression.
    This bridges the MULHU instruction output to `floor(x' * y' / 2^w)`. -/
lemma mulhu_eq_ofInt (x y : BitVec w) :
    (Jolt.mulhu x y : BitVec w) =
      BitVec.ofInt w ((x.toNat : Int) * (y.toNat : Int) / (2 ^ w : Int)) := by
  unfold Jolt.mulhu
  have h : (x.toNat : Int) * (y.toNat : Int) / (2 ^ w : Int) =
      ↑(x.toNat * y.toNat / 2 ^ w) := by norm_cast
  rw [h, BitVec.ofInt_natCast]

/-- The composed mulhJolt equals ofInt of the flat Int expression.
    This is the main bridging result, connecting the instruction-by-instruction
    composition to the mathematical formula used in the equivalence proof. -/
lemma mulhJolt_eq_ofInt (x y : BitVec w) :
    mulhJolt x y =
      BitVec.ofInt w (
        (x.toNat : Int) * (y.toNat : Int) / (2 ^ w : Int)
        + signExtract x * (y.toNat : Int)
        + signExtract y * (x.toNat : Int)) := by
  unfold mulhJolt
  simp only []
  rw [mulhu_eq_ofInt, virtualMovSign_mul_eq x y, virtualMovSign_mul_eq y x]
  rw [← BitVec.ofInt_add, ← BitVec.ofInt_add]

-- ============================================================================
-- LEMMA 1: Two's complement identity
-- ============================================================================

/-! ## Lemma 1: Signed = Unsigned + sign * 2^w

The fundamental two's complement identity:
  toInt(x) = toNat(x) + signExtract(x) * 2^w -/

lemma toInt_eq_toNat_add_signExtract_mul (x : BitVec w) :
    (x.toInt : Int) = (x.toNat : Int) + signExtract x * (2 ^ w : Int) := by
  unfold signExtract
  rw [BitVec.toInt_eq_msb_cond]
  split
  · simp; ring
  · simp

-- ============================================================================
-- LEMMA 2: Signed product expansion
-- ============================================================================

/-! ## Lemma 2: Product expansion

Using Lemma 1 on both factors:
  x * y = x'*y' + s_x*y'*2^w + s_y*x'*2^w + s_x*s_y*2^(2w) -/

lemma signed_product_expansion (x y : BitVec w) :
    (x.toInt * y.toInt : Int) =
      (x.toNat : Int) * (y.toNat : Int)
      + signExtract x * (y.toNat : Int) * (2 ^ w : Int)
      + signExtract y * (x.toNat : Int) * (2 ^ w : Int)
      + signExtract x * signExtract y * (2 ^ w : Int) * (2 ^ w : Int) := by
  rw [toInt_eq_toNat_add_signExtract_mul x, toInt_eq_toNat_add_signExtract_mul y]
  ring

-- ============================================================================
-- LEMMA 3: Division extracts coefficients
-- ============================================================================

/-! ## Lemma 3: Division pulls out exact multiples of 2^w

  floor(x*y / 2^w) = floor(x'*y' / 2^w) + s_x*y' + s_y*x' + s_x*s_y*2^w -/

lemma div_signed_product (x y : BitVec w) :
    x.toInt * y.toInt / (2 ^ w : Int) =
      (x.toNat : Int) * (y.toNat : Int) / (2 ^ w : Int)
      + signExtract x * (y.toNat : Int)
      + signExtract y * (x.toNat : Int)
      + signExtract x * signExtract y * (2 ^ w : Int) := by
  rw [signed_product_expansion]
  have h2w : (2 ^ w : Int) ≠ 0 := by positivity
  have hrearrange :
    (x.toNat : Int) * y.toNat
    + signExtract x * y.toNat * (2 ^ w)
    + signExtract y * x.toNat * (2 ^ w)
    + signExtract x * signExtract y * (2 ^ w) * (2 ^ w)
    = (x.toNat : Int) * y.toNat
    + (signExtract x * y.toNat + signExtract y * x.toNat
       + signExtract x * signExtract y * (2 ^ w)) * (2 ^ w) := by ring
  rw [hrearrange]
  rw [Int.add_mul_ediv_right _ _ h2w]
  ring

-- ============================================================================
-- MAIN THEOREM: MULH ≡ MULH_JOLT
-- ============================================================================

/-! ## Main Theorem: MULH Equivalence

From Lemma 3:
  floor(x*y / 2^w) = floor(x'*y' / 2^w) + s_x*y' + s_y*x' + s_x*s_y*2^w

The difference between mulh and mulhJolt is `s_x * s_y * 2^w`, which
vanishes under mod 2^w via `Int.bmod_add_mul_cancel`. -/

theorem mulh_eq_mulhJolt (x y : BitVec w) : mulh x y = mulhJolt x y := by
  -- Step 0: Rewrite the composed mulhJolt to its flat ofInt form
  rw [mulhJolt_eq_ofInt]
  -- From here, the proof is identical to the monolithic version:
  unfold mulh
  apply BitVec.eq_of_toInt_eq
  simp only [BitVec.toInt_ofInt]
  rw [div_signed_product]
  have key : signExtract x * signExtract y * (2 : Int) ^ w =
    ↑(2 ^ w : Nat) * (signExtract x * signExtract y) := by
    push_cast; ring
  rw [key, Int.bmod_add_mul_cancel]

end MULH

-- ============================================================================
-- EVALUATION / SANITY CHECKS
-- ============================================================================

/-! ## Concrete evaluations

We trace through concrete 8-bit examples to sanity-check the definitions,
using the actual virtual instruction functions. -/

section Evals

/-- Trace the full virtual instruction sequence for an 8-bit example,
    using the actual `Jolt.virtualMovSign` and `Jolt.mulhu` functions. -/
def traceVirtualMulh8 (x y : BitVec 8) : String :=
  -- Execute the virtual instruction sequence
  let v_sx := Jolt.virtualMovSign x         -- VirtualMovsign v_sx, rs1, 0
  let v_sy := Jolt.virtualMovSign y         -- VirtualMovsign v_sy, rs2, 0
  let v_0  := Jolt.mulhu x y               -- MULHU v_0, rs1, rs2
  let v_sx_mul := v_sx * y                  -- MUL v_sx, v_sx, rs2
  let v_sy_mul := v_sy * x                 -- MUL v_sy, v_sy, rs1
  let v_0' := v_0 + v_sx_mul               -- ADD v_0, v_0, v_sx
  let rd := v_0' + v_sy_mul                -- ADD rd, v_0, v_sy
  s!"  x = {x.toInt}, y = {y.toInt} (x' = {x.toNat}, y' = {y.toNat})\n" ++
  s!"  VirtualMovsign: v_sx = {v_sx.toInt}, v_sy = {v_sy.toInt}\n" ++
  s!"  MULHU:  v_0  = {v_0.toInt}\n" ++
  s!"  MUL:    v_sx = {v_sx_mul.toInt}\n" ++
  s!"  MUL:    v_sy = {v_sy_mul.toInt}\n" ++
  s!"  ADD:    v_0  = {v_0'.toInt}\n" ++
  s!"  ADD:    rd   = {rd.toInt}\n" ++
  s!"  Expected (MULH): floor({x.toInt}*{y.toInt}/256) = {x.toInt * y.toInt / 256}\n" ++
  s!"  mulh result:     {(mulh x y).toInt}\n" ++
  s!"  mulhJolt result: {(mulhJolt x y).toInt}\n" ++
  s!"  Match: {mulh x y == mulhJolt x y}"

-- Example 1: Both positive (7 * 3 = 21, high bits = 0)
#eval do
  IO.println "=== Example 1: 7 * 3 (both positive) ==="
  IO.println (traceVirtualMulh8 (BitVec.ofInt 8 7) (BitVec.ofInt 8 3))

-- Example 2: Max positive * max positive (127 * 127 = 16129)
#eval do
  IO.println "=== Example 2: 127 * 127 (large positive) ==="
  IO.println (traceVirtualMulh8 (BitVec.ofInt 8 127) (BitVec.ofInt 8 127))

-- Example 3: Both negative (-1 * -1 = 1)
#eval do
  IO.println "=== Example 3: -1 * -1 (both negative) ==="
  IO.println (traceVirtualMulh8 (BitVec.ofInt 8 (-1)) (BitVec.ofInt 8 (-1)))

-- Example 4: Negative * positive (-128 * 2 = -256)
#eval do
  IO.println "=== Example 4: -128 * 2 (negative * positive) ==="
  IO.println (traceVirtualMulh8 (BitVec.ofInt 8 (-128)) (BitVec.ofInt 8 2))

-- Example 5: Negative * positive (-3 * 7 = -21)
#eval do
  IO.println "=== Example 5: -3 * 7 (negative * positive) ==="
  IO.println (traceVirtualMulh8 (BitVec.ofInt 8 (-3)) (BitVec.ofInt 8 7))

-- Example 6: Both negative (-3 * -7 = 21)
#eval do
  IO.println "=== Example 6: -3 * -7 (both negative) ==="
  IO.println (traceVirtualMulh8 (BitVec.ofInt 8 (-3)) (BitVec.ofInt 8 (-7)))

-- Example 7: Zero cases
#eval do
  IO.println "=== Example 7: 0 * -128 ==="
  IO.println (traceVirtualMulh8 (BitVec.ofInt 8 0) (BitVec.ofInt 8 (-128)))

-- Exhaustive check: verify mulh == mulhJolt for ALL 8-bit pairs
#eval do
  let mut failures := 0
  for i in List.range 256 do
    for j in List.range 256 do
      let x : BitVec 8 := BitVec.ofNat 8 i
      let y : BitVec 8 := BitVec.ofNat 8 j
      if mulh x y != mulhJolt x y then
        failures := failures + 1
  if failures == 0 then
    IO.println "✓ Exhaustive check passed: mulh == mulhJolt for all 65536 8-bit pairs"
  else
    IO.println s!"✗ FAILED: {failures} mismatches found"

end Evals
