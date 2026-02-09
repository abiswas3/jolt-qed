import Mathlib.Tactic
import Mathlib.Data.BitVec

/-!
# MULH Equivalence Theorem

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

We prove that the original MULH and the Jolt decomposition produce identical results.

## Definitions

- `signExtract x` : the sign function s(x), returns -1 if x < 0, else 0
- `mulh x y`      : the RISC-V MULH instruction: floor(toInt(x) * toInt(y) / 2^w)
- `mulhJolt x y`  : Jolt's decomposition: floor(x'*y'/2^w) + s_x*y' + s_y*x'

where x' = toNat(x) is the unsigned interpretation of x, and
s_x = signExtract(x) ∈ {0, -1}.

## Proof Strategy

The proof follows the paper proof in `FormalTyped/mulh.typ`:

1. **Signed ↔ Unsigned**: Show `toInt(x) = toNat(x) + signExtract(x) * 2^w`.
   This is the well-known two's complement identity.

2. **Product Expansion**: Substitute the above into `toInt(x) * toInt(y)` and expand:
   `x*y = x'*y' + s_x*y'*2^w + s_y*x'*2^w + s_x*s_y*2^(2w)`

3. **Division**: Divide by 2^w. Terms that are exact multiples of 2^w collapse:
   `floor(x*y / 2^w) = floor(x'*y' / 2^w) + s_x*y' + s_y*x' + s_x*s_y*2^w`

4. **Mod 2^w**: The extra `s_x*s_y*2^w` term vanishes mod 2^w, giving us the result.

## Key Lean 4 lemmas used

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
    Models s(x) from the paper proof:
      s(x) = 0   if x ≥ 0
      s(x) = -1  if x < 0
    This captures the sign bit of a two's complement number. -/
def signExtract (x : BitVec w) : Int :=
  if x.msb then -1 else 0

/-- The RISC-V MULH instruction: computes the upper w bits of the signed product.
    Given two w-bit signed integers x and y, MULH returns:
      floor(toInt(x) * toInt(y) / 2^w)  mod 2^w
    This is the "high half" of a full 2w-bit signed multiplication. -/
def mulh (x y : BitVec w) : BitVec w :=
  BitVec.ofInt w (x.toInt * y.toInt / (2 ^ w : Int))

/-- The Jolt virtual instruction decomposition for MULH.
    Instead of computing the signed high multiply directly, Jolt computes:
      floor(x' * y' / 2^w) + s_x * y' + s_y * x'
    where x' = toNat(x) (unsigned interpretation), y' = toNat(y),
    and s_x, s_y are the sign extractions.

    This decomposes the signed operation into:
    - An unsigned high multiply (MULHU): floor(x' * y' / 2^w)
    - Two sign correction terms: s_x * y' and s_y * x'

    All arithmetic is mod 2^w (handled by BitVec.ofInt). -/
def mulhJolt (x y : BitVec w) : BitVec w :=
  BitVec.ofInt w (
    (x.toNat : Int) * (y.toNat : Int) / (2 ^ w : Int)
    + signExtract x * (y.toNat : Int)
    + signExtract y * (x.toNat : Int))

-- ============================================================================
-- LEMMA 1: Two's complement identity
-- ============================================================================

/-! ## Lemma 1: Signed = Unsigned + sign * 2^w

The fundamental two's complement identity:
  toInt(x) = toNat(x) + signExtract(x) * 2^w

Case analysis:
- If msb = false (x ≥ 0): toInt(x) = toNat(x), and signExtract(x) = 0,
  so toNat(x) + 0 * 2^w = toNat(x). ✓
- If msb = true  (x < 0): toInt(x) = toNat(x) - 2^w, and signExtract(x) = -1,
  so toNat(x) + (-1) * 2^w = toNat(x) - 2^w. ✓
-/
lemma toInt_eq_toNat_add_signExtract_mul (x : BitVec w) :
    (x.toInt : Int) = (x.toNat : Int) + signExtract x * (2 ^ w : Int) := by
  -- Unfold signExtract to expose the if-then-else on x.msb
  unfold signExtract
  -- Use the Lean 4 lemma that characterizes toInt via msb:
  --   toInt(x) = if x.msb then toNat(x) - 2^w else toNat(x)
  rw [BitVec.toInt_eq_msb_cond]
  -- Case split on x.msb
  split
  -- Case msb = true: need toNat(x) - 2^w = toNat(x) + (-1) * 2^w
  · simp; ring
  -- Case msb = false: need toNat(x) = toNat(x) + 0 * 2^w
  · simp

-- ============================================================================
-- LEMMA 2: Signed product expansion
-- ============================================================================

/-! ## Lemma 2: Product expansion

Using Lemma 1 on both factors:
  x = x' + s_x * 2^w
  y = y' + s_y * 2^w

Multiply out:
  x * y = (x' + s_x * 2^w) * (y' + s_y * 2^w)
        = x'*y'
          + s_x * y' * 2^w       ← cross term 1
          + s_y * x' * 2^w       ← cross term 2
          + s_x * s_y * 2^(2w)   ← high-order term

The `ring` tactic closes this after substituting Lemma 1 for both x and y.
-/
lemma signed_product_expansion (x y : BitVec w) :
    (x.toInt * y.toInt : Int) =
      (x.toNat : Int) * (y.toNat : Int)
      + signExtract x * (y.toNat : Int) * (2 ^ w : Int)
      + signExtract y * (x.toNat : Int) * (2 ^ w : Int)
      + signExtract x * signExtract y * (2 ^ w : Int) * (2 ^ w : Int) := by
  -- Substitute the two's complement identity for both x and y
  rw [toInt_eq_toNat_add_signExtract_mul x, toInt_eq_toNat_add_signExtract_mul y]
  -- The result is a polynomial identity — `ring` closes it
  ring

-- ============================================================================
-- LEMMA 3: Division extracts coefficients
-- ============================================================================

/-! ## Lemma 3: Division pulls out exact multiples of 2^w

Starting from the product expansion (Lemma 2):
  x*y = x'*y' + s_x*y'*2^w + s_y*x'*2^w + s_x*s_y*2^(2w)

We rearrange the RHS into the form `A + B * 2^w` where:
  A = x'*y'
  B = s_x*y' + s_y*x' + s_x*s_y*2^w

Then integer division gives us:
  (A + B * 2^w) / 2^w = A / 2^w + B      [by Int.add_mul_ediv_right]

So:
  floor(x*y / 2^w) = floor(x'*y' / 2^w) + s_x*y' + s_y*x' + s_x*s_y*2^w

The key insight: the cross terms s_x*y' and s_y*x' are exact integers
(not divided by 2^w), because they were multiplied by 2^w in the product
and that factor cancels with the division.
-/
lemma div_signed_product (x y : BitVec w) :
    x.toInt * y.toInt / (2 ^ w : Int) =
      (x.toNat : Int) * (y.toNat : Int) / (2 ^ w : Int)
      + signExtract x * (y.toNat : Int)
      + signExtract y * (x.toNat : Int)
      + signExtract x * signExtract y * (2 ^ w : Int) := by
  -- Step 1: Substitute the product expansion from Lemma 2
  rw [signed_product_expansion]
  -- 2^w ≠ 0, needed for the division lemma
  have h2w : (2 ^ w : Int) ≠ 0 := by positivity
  -- Step 2: Rearrange into the form `A + B * 2^w` so we can apply add_mul_ediv_right.
  -- We factor out 2^w from the last three terms:
  --   x'*y' + s_x*y'*2^w + s_y*x'*2^w + s_x*s_y*2^w*2^w
  --   = x'*y' + (s_x*y' + s_y*x' + s_x*s_y*2^w) * 2^w
  have hrearrange :
    (x.toNat : Int) * y.toNat
    + signExtract x * y.toNat * (2 ^ w)
    + signExtract y * x.toNat * (2 ^ w)
    + signExtract x * signExtract y * (2 ^ w) * (2 ^ w)
    = (x.toNat : Int) * y.toNat
    + (signExtract x * y.toNat + signExtract y * x.toNat
       + signExtract x * signExtract y * (2 ^ w)) * (2 ^ w) := by ring
  rw [hrearrange]
  -- Step 3: Apply (A + B * C) / C = A / C + B
  rw [Int.add_mul_ediv_right _ _ h2w]
  -- Step 4: Rearrange the resulting sum to match the goal
  ring

-- ============================================================================
-- MAIN THEOREM: MULH ≡ MULH_JOLT
-- ============================================================================

/-! ## Main Theorem: MULH Equivalence

We now prove that `mulh x y = mulhJolt x y`.

From Lemma 3 we know:
  floor(x*y / 2^w) = floor(x'*y' / 2^w) + s_x*y' + s_y*x' + s_x*s_y*2^w

The mulh result is this value mod 2^w (via BitVec.ofInt).
The mulhJolt result is `floor(x'*y' / 2^w) + s_x*y' + s_y*x'` mod 2^w.

The difference between these two expressions is `s_x * s_y * 2^w`, which is
an exact multiple of 2^w. Therefore it vanishes under mod 2^w:

  bmod(A + s_x*s_y*2^w, 2^w) = bmod(A, 2^w)

This is exactly `Int.bmod_add_mul_cancel`.

Note: In the paper proof, this corresponds to the observation that
"s_x * s_y * 2^w ≡ 0 mod 2^w, thus we can safely drop the last term."
-/
theorem mulh_eq_mulhJolt (x y : BitVec w) : mulh x y = mulhJolt x y := by
  -- Step 1: Unfold both definitions to expose `BitVec.ofInt w (...)`.
  unfold mulh mulhJolt
  -- Step 2: Two BitVecs from ofInt are equal iff their toInt values are equal.
  apply BitVec.eq_of_toInt_eq
  -- Step 3: toInt(ofInt(i)) = i.bmod(2^w), so we reduce to a bmod equality.
  simp only [BitVec.toInt_ofInt]
  -- Goal is now:
  --   (x.toInt * y.toInt / 2^w).bmod(2^w)
  --   = (x'*y'/2^w + s_x*y' + s_y*x').bmod(2^w)

  -- Step 4: Apply Lemma 3 to rewrite the LHS numerator.
  -- After this, LHS becomes:
  --   (x'*y'/2^w + s_x*y' + s_y*x' + s_x*s_y*2^w).bmod(2^w)
  rw [div_signed_product]

  -- Step 5: The LHS has an extra `s_x*s_y*2^w` compared to the RHS.
  -- We rewrite this term into the form `↑(2^w : Nat) * k` so that
  -- Int.bmod_add_mul_cancel can absorb it.
  -- Concretely: s_x * s_y * (2:Int)^w = ↑(2^w : Nat) * (s_x * s_y)
  have key : signExtract x * signExtract y * (2 : Int) ^ w =
    ↑(2 ^ w : Nat) * (signExtract x * signExtract y) := by
    -- push_cast normalizes ↑(2^w : Nat) to (2:Int)^w, then ring rearranges
    push_cast; ring

  -- Step 6: Rewrite and apply bmod_add_mul_cancel.
  -- Due to left-associativity of +, the goal is:
  --   bmod((A + B + C) + ↑n * k, n) = bmod(A + B + C, n)
  -- which is exactly Int.bmod_add_mul_cancel with x := A+B+C, n := 2^w, k := s_x*s_y.
  rw [key, Int.bmod_add_mul_cancel]
  -- QED: both sides are now identical. ∎

end MULH

-- ============================================================================
-- EVALUATION / SANITY CHECKS
-- ============================================================================

/-! ## Concrete evaluations

We trace through concrete 8-bit examples to sanity-check the definitions,
matching the virtual instruction sequence from the paper:

```
VirtualMovsign  v_sx, rs1, 0      -- s_x = sign(rs1)
VirtualMovsign  v_sy, rs2, 0      -- s_y = sign(rs2)
MULHU           v_0,  rs1, rs2    -- v_0 = floor(x' * y' / 2^w)  (unsigned high mul)
MUL             v_sx, v_sx, rs2   -- v_sx = s_x * y'
MUL             v_sy, v_sy, rs1   -- v_sy = s_y * x'
ADD             v_0,  v_0,  v_sx  -- v_0 = floor(x'*y'/2^w) + s_x*y'
ADD             rd,   v_0,  v_sy  -- rd  = floor(x'*y'/2^w) + s_x*y' + s_y*x'
```
-/

section Evals

-- For convenience, define a helper that traces the full virtual instruction sequence
-- for an 8-bit example, returning each intermediate value as the assembly would compute.
def traceVirtualMulh8 (x y : BitVec 8) : String :=
  let sx := signExtract x            -- VirtualMovsign: s_x = sign(rs1)
  let sy := signExtract y            -- VirtualMovsign: s_y = sign(rs2)
  let x' := (x.toNat : Int)          -- unsigned interpretation of rs1
  let y' := (y.toNat : Int)          -- unsigned interpretation of rs2
  let v0 := x' * y' / (2^8 : Int)    -- MULHU: floor(x' * y' / 2^w)
  let vsx := sx * y'                  -- MUL: s_x * y' (reuses v_sx register)
  let vsy := sy * x'                  -- MUL: s_y * x' (reuses v_sy register)
  let v0' := v0 + vsx                -- ADD: v_0 = floor(x'*y'/2^w) + s_x*y'
  let rd := v0' + vsy                -- ADD: rd = v_0 + s_y*x'
  s!"  x = {x.toInt}, y = {y.toInt} (x' = {x'}, y' = {y'})\n" ++
  s!"  VirtualMovsign: s_x = {sx}, s_y = {sy}\n" ++
  s!"  MULHU:  v_0  = floor({x'}*{y'}/256) = {v0}\n" ++
  s!"  MUL:    v_sx = s_x * y' = {sx} * {y'} = {vsx}\n" ++
  s!"  MUL:    v_sy = s_y * x' = {sy} * {x'} = {vsy}\n" ++
  s!"  ADD:    v_0  = {v0} + {vsx} = {v0'}\n" ++
  s!"  ADD:    rd   = {v0'} + {vsy} = {rd}\n" ++
  s!"  Expected (MULH): floor({x.toInt}*{y.toInt}/256) = {x.toInt * y.toInt / 256}\n" ++
  s!"  mulh result:     {(mulh x y).toInt}\n" ++
  s!"  mulhJolt result: {(mulhJolt x y).toInt}\n" ++
  s!"  Match: {mulh x y == mulhJolt x y}"

-- ============================================================================
-- Example 1: Both positive (7 * 3 = 21, high bits = 0)
-- ============================================================================
-- x = 7, y = 3. Both positive, so s_x = s_y = 0.
-- x * y = 21, floor(21/256) = 0. No sign correction needed.
#eval do
  IO.println "=== Example 1: 7 * 3 (both positive) ==="
  IO.println (traceVirtualMulh8 (BitVec.ofInt 8 7) (BitVec.ofInt 8 3))

-- ============================================================================
-- Example 2: Max positive * max positive (127 * 127 = 16129)
-- ============================================================================
-- x = 127, y = 127. Both positive, so s_x = s_y = 0.
-- x * y = 16129, floor(16129/256) = 63.
#eval do
  IO.println "=== Example 2: 127 * 127 (large positive) ==="
  IO.println (traceVirtualMulh8 (BitVec.ofInt 8 127) (BitVec.ofInt 8 127))

-- ============================================================================
-- Example 3: Both negative (-1 * -1 = 1)
-- ============================================================================
-- x = -1 (unsigned: 255), y = -1 (unsigned: 255). s_x = s_y = -1.
-- x * y = 1, floor(1/256) = 0.
-- Jolt: floor(255*255/256) + (-1)*255 + (-1)*255 = 254 - 255 - 255 = -256 ≡ 0 mod 256.
#eval do
  IO.println "=== Example 3: -1 * -1 (both negative) ==="
  IO.println (traceVirtualMulh8 (BitVec.ofInt 8 (-1)) (BitVec.ofInt 8 (-1)))

-- ============================================================================
-- Example 4: Negative * positive (-128 * 2 = -256)
-- ============================================================================
-- x = -128 (unsigned: 128), y = 2. s_x = -1, s_y = 0.
-- x * y = -256, floor(-256/256) = -1.
-- Jolt: floor(128*2/256) + (-1)*2 + 0*128 = 1 - 2 = -1. ✓
#eval do
  IO.println "=== Example 4: -128 * 2 (negative * positive) ==="
  IO.println (traceVirtualMulh8 (BitVec.ofInt 8 (-128)) (BitVec.ofInt 8 2))

-- ============================================================================
-- Example 5: Negative * positive (-3 * 7 = -21)
-- ============================================================================
-- x = -3 (unsigned: 253), y = 7. s_x = -1, s_y = 0.
-- x * y = -21, floor(-21/256) = -1.
-- Jolt: floor(253*7/256) + (-1)*7 + 0*253 = 6 - 7 = -1. ✓
#eval do
  IO.println "=== Example 5: -3 * 7 (negative * positive) ==="
  IO.println (traceVirtualMulh8 (BitVec.ofInt 8 (-3)) (BitVec.ofInt 8 7))

-- ============================================================================
-- Example 6: Both negative (-3 * -7 = 21)
-- ============================================================================
-- x = -3 (unsigned: 253), y = -7 (unsigned: 249). s_x = s_y = -1.
-- x * y = 21, floor(21/256) = 0.
-- Jolt: floor(253*249/256) + (-1)*249 + (-1)*253
--     = floor(63017/256) - 249 - 253 = 246 - 249 - 253 = -256 ≡ 0 mod 256. ✓
#eval do
  IO.println "=== Example 6: -3 * -7 (both negative) ==="
  IO.println (traceVirtualMulh8 (BitVec.ofInt 8 (-3)) (BitVec.ofInt 8 (-7)))

-- ============================================================================
-- Example 7: Zero cases
-- ============================================================================
#eval do
  IO.println "=== Example 7: 0 * -128 ==="
  IO.println (traceVirtualMulh8 (BitVec.ofInt 8 0) (BitVec.ofInt 8 (-128)))

-- ============================================================================
-- Batch check: verify mulh == mulhJolt for ALL 8-bit pairs (exhaustive)
-- ============================================================================
-- This loops over all 256 * 256 = 65536 pairs and confirms the theorem holds
-- computationally for w=8.
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
