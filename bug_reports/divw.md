# Bug Report: DIVW Inline Sequence Incompleteness

## Instruction
DIVW — signed 32-bit division word (RV64M). 
Divides the low 32 bits of `rs1` by the low 32 bits
of `rs2`, treating both as signed 32-bit integers, and writes the quotient sign-extended to 64
bits into `rd`.

## Triggering Input

- `rs1_low = i32::MIN = -2147483648`
- `rs2_low = 0`

## Source of Honest Advice (Completeness Theorem)

The completeness theorem `jolt_divw_concrete` instantiates the Jolt inline sequence with the
following honest advice pair, which must match what the Jolt **tracer** computes — not what the
trusted SAIL transpilation writes:

```lean
(jolt_divw rs2 rs1 rd
    (sail_divw_value dividend divisor false)          -- quotient
    (bv_abs (sail_remw_value dividend divisor false))) -- |remainder|
```

- `sail_divw_value` computes the same value as `execute_DIVW` writes to `rd` — this IS what
  trusted SAIL writes.
- `sail_remw_value` computes the same value as `execute_REMW` would write to `rd` (the **signed**
  remainder). This is NOT directly used as advice.
- `bv_abs (sail_remw_value ...)` takes the absolute value — this matches `x.unsigned_abs()` in
  the Rust tracer. The trusted SAIL transpilation never applies `bv_abs`; it is added to mirror
  the Jolt tracer's choice to supply `|remainder|` as advice, reconstructing the sign inside the
  inline sequence.

This pattern is uniform across all signed division variants (DIV uses `bv_abs (sail_rem_value
...)` in the same way). Unsigned variants (DIVU, DIVUW) supply no remainder advice.

### What the Jolt Tracer Computes for Our Input
From `tracer/src/instruction/divw.rs` line 62-63:
```rust
if y == 0 {
    (-1i32, x.unsigned_abs())
```
For `y = 0` and `x = i32::MIN`:
- **quotient** `a2 := -1`
- **remainder** `a3 := x.unsigned_abs() = 2^31 = 2147483648`

## Inline Sequence Trace

| Line | Instruction | Result | Status |
|------|-------------|--------|--------|
| 1 | `a2 := quotient` | `a2 = -1` | |
| 2 | `a3 := remainder` | `a3 = 2^31` | |
| 3 | `t4 := sext([rs1])` | `t4 = 0xFFFFFFFF80000000` | |
| 4 | `t3 := sext([rs2])` | `t3 = 0` | |
| 5 | `if t3 = 0 then assert a2 = -1` | `t3 = 0` and `a2 = -1` | ✓ |
| 6 | `t0 := if (t4 as i32 = i32::MIN ∧ t3 as i32 = -1) then 1 else t3` | `t0 = 0` (t4 as i32 = i32::MIN but t3 as i32 = 0 ≠ -1) | |
| 7 | `t1 := sext(a2)` | `t1 = -1` | |
| 8 | `assert t1 = a2` | `t1 = -1 = a2` | ✓ |
| 9 | `t2 := SRAI(a3, 31)` | `t2 = SRAI(2^31, 31) = 1` | |
| 10 | `assert t2 = x0` | `t2 = 1 ≠ x0 = 0` | ✗ **PANIC** |

## Nature of the Bug
**Incompleteness**: the inline sequence rejects honest advice that Jolt itself computed.

The check at line 10 (`SRAI(rem, 31) == 0`) is designed to verify that the remainder advice is
non-negative and fits within a signed 32-bit integer, i.e. `rem < 2^31`. However, for the
divide-by-zero case with `rs1_low = i32::MIN`, the honest remainder advice is
`|i32::MIN| = 2^31`, which does not satisfy `rem < 2^31`.

This check does not exist in `div.rs`. It was added in `divw.rs` specifically to verify the
remainder fits in a u32, but uses `shamt = 31` which checks the stricter signed 32-bit range
instead of the unsigned 32-bit range.

## RISC-V / SAIL Spec
For DIVW with divisor = 0, the SAIL spec mandates:
- quotient = `-1` (written to `rd`)
- remainder = dividend = `i32::MIN = -2147483648`

The honest advice uses the absolute value of the remainder: `|i32::MIN| = 2^31`.

## Impact
The Jolt prover panics (`assert_eq!` failure) when asked to prove any execution of DIVW where
`rs1_low = i32::MIN` and `rs2_low = 0`. This is a valid RISC-V execution that Jolt cannot prove.
