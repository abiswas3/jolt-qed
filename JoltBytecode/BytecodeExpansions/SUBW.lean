import Mathlib.Tactic
import Mathlib.Data.BitVec

/-!
# SUBW Equivalence Theorem

We formally verify that the RISC-V `SUBW` instruction (subtract word) computes
the same result as Jolt's replacement sequence of virtual instructions.

## Background

The RISC-V `SUBW rd, rs1, rs2` instruction (RV64I) subtracts rs2 from rs1,
truncates the result to 32 bits, and sign-extends it to 64 bits, storing in rd.

In Jolt, this single instruction is replaced by:
```
SUB                   rd, rs1, rs2   -- 64-bit subtraction: rd = rs1 - rs2
VirtualSignExtendWord rd, rd, 0      -- sign-extend lower 32 bits of rd
```

## Definitions

- `Jolt.virtualSignExtendWord z` : sign-extends the lower 32 bits of z to 64 bits
- `subw x y`      : the RISC-V SUBW instruction
- `subwJolt x y`   : Jolt's decomposition as SUB + VirtualSignExtendWord

## Proof Strategy

The key insight is that truncation to 32 bits commutes with subtraction:
  (x - y)[31:0] = x[31:0] - y[31:0]  (mod 2^32)

Since both sides apply sign extension to the lower 32 bits of the difference,
the results are equal once we establish this commutativity.
-/

section SUBW

-- ============================================================================
-- DEFINITIONS
-- ============================================================================

namespace Jolt

/-- VirtualSignExtendWord: sign-extends the lower 32 bits of a 64-bit value.
    Interprets bits [31:0] as a signed 32-bit integer and produces the
    64-bit sign-extended result. -/
def virtualSignExtendWord (z : BitVec 64) : BitVec 64 :=
  (z.setWidth 32).signExtend 64

end Jolt

/-- The RISC-V SUBW instruction (RV64I): subtracts the lower 32 bits of rs2
    from the lower 32 bits of rs1, and sign-extends the 32-bit result to 64 bits. -/
def subw (x y : BitVec 64) : BitVec 64 :=
  (x.setWidth 32 - y.setWidth 32).signExtend 64

/-- The Jolt virtual instruction decomposition for SUBW.
    SUB performs a full 64-bit subtraction, then VirtualSignExtendWord
    sign-extends the lower 32 bits of the result. -/
def subwJolt (x y : BitVec 64) : BitVec 64 :=
  let sub := x - y                        -- SUB rd, rs1, rs2
  Jolt.virtualSignExtendWord sub           -- VirtualSignExtendWord rd, rd, 0

-- ============================================================================
-- KEY LEMMA: Truncation commutes with subtraction
-- ============================================================================

/-- Truncation to 32 bits commutes with 64-bit subtraction: the lower 32 bits
    of a 64-bit difference equal the 32-bit difference of the lower 32 bits.
    This follows from modular arithmetic: (a - b) mod 2^32 depends only on
    a mod 2^32 and b mod 2^32, since 2^32 divides 2^64. -/
lemma setWidth_sub_32 (x y : BitVec 64) :
    (x - y).setWidth 32 = x.setWidth 32 - y.setWidth 32 := by
  bv_omega

-- ============================================================================
-- MAIN THEOREM: SUBW ≡ SUBW_JOLT
-- ============================================================================

/-- The RISC-V SUBW instruction computes the same result as Jolt's
    decomposition (SUB followed by VirtualSignExtendWord). -/
theorem subw_eq_subwJolt (x y : BitVec 64) : subw x y = subwJolt x y := by
  unfold subw subwJolt Jolt.virtualSignExtendWord
  simp only [setWidth_sub_32]

end SUBW

-- ============================================================================
-- EVALUATION / SANITY CHECKS
-- ============================================================================

section Evals

/-- Trace the virtual instruction sequence for a concrete example. -/
def traceSubw (x y : BitVec 64) : String :=
  let sub := x - y
  let result_jolt := subwJolt x y
  let result_spec := subw x y
  s!"  x = {x.toInt}, y = {y.toInt}\n" ++
  s!"  SUB:              {sub.toInt}\n" ++
  s!"  SignExtendWord:   {result_jolt.toInt}\n" ++
  s!"  subw (spec):      {result_spec.toInt}\n" ++
  s!"  Match: {result_spec == result_jolt}"

-- Example 1: Simple subtraction, result fits in 32 bits
#eval do
  IO.println "=== Example 1: 10 - 3 ==="
  IO.println (traceSubw (BitVec.ofInt 64 10) (BitVec.ofInt 64 3))

-- Example 2: Result is negative
#eval do
  IO.println "=== Example 2: 3 - 10 ==="
  IO.println (traceSubw (BitVec.ofInt 64 3) (BitVec.ofInt 64 10))

-- Example 3: Large positive, near 32-bit boundary
#eval do
  IO.println "=== Example 3: 2^31 - 1 ==="
  IO.println (traceSubw (BitVec.ofInt 64 (2^31)) (BitVec.ofInt 64 1))

-- Example 4: Overflow in 32-bit subtraction
#eval do
  IO.println "=== Example 4: 0 - 2^31 (overflow) ==="
  IO.println (traceSubw (BitVec.ofInt 64 0) (BitVec.ofInt 64 (2^31)))

-- Example 5: Operands with upper 32 bits set (differ only in upper bits)
#eval do
  IO.println "=== Example 5: large 64-bit values ==="
  IO.println (traceSubw (BitVec.ofInt 64 (2^40 + 5)) (BitVec.ofInt 64 (2^40 + 3)))

-- Example 6: Both negative
#eval do
  IO.println "=== Example 6: -3 - (-7) ==="
  IO.println (traceSubw (BitVec.ofInt 64 (-3)) (BitVec.ofInt 64 (-7)))

-- Exhaustive check: verify subw == subwJolt for all 8-bit value pairs
-- (8-bit values zero-extended to 64 bits)
#eval do
  let mut failures := 0
  for i in List.range 256 do
    for j in List.range 256 do
      let x : BitVec 64 := BitVec.ofNat 64 i
      let y : BitVec 64 := BitVec.ofNat 64 j
      if subw x y != subwJolt x y then
        failures := failures + 1
  if failures == 0 then
    IO.println "✓ Exhaustive check passed: subw == subwJolt for all 65536 test pairs"
  else
    IO.println s!"✗ FAILED: {failures} mismatches found"

end Evals

