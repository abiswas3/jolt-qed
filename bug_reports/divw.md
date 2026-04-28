# Bug Report: DIVW Inline Sequence Incompleteness

## Instruction
DIVW — signed 32-bit division word (RV64M).
Divides the low 32 bits of `rs1` by the low 32 bits of `rs2`, treating both as signed 32-bit
integers, and writes the quotient sign-extended to 64 bits into `rd`.

## Triggering Input
- `rs1_low = i32::MIN = -2147483648`
- `rs2_low = 0`

## Honest Advice (from Jolt Tracer)

From [`tracer/src/instruction/divw.rs#L66`](https://github.com/a16z/jolt/blob/a907f5457a8d1cb18cd17ba5873383887e1042ec/tracer/src/instruction/divw.rs#L66):

```rust
if y == 0 {
    (-1i32, x.unsigned_abs())
```

For `y = 0` and `x = i32::MIN`, the tracer declares:
- **quotient** `a2 = -1`
- **remainder** `a3 = x.unsigned_abs() = 2^31 = 2147483648`

## Inline Sequence Trace

Initial register state:
- `a0 = rs1`, `[a0] = rs1_value` where `rs1_value as i32 = i32::MIN = -2147483648`
- `a1 = rs2`, `[a1] = 0`

| Line | Rust | Instruction | Result | Status |
|------|------|-------------|--------|--------|
| 1 | `emit_j::<VirtualAdvice>(*a2, 0)` | `a2 := quotient` | `a2 = -1` | |
| 2 | `emit_j::<VirtualAdvice>(*a3, 0)` | `a3 := remainder` | `a3 = 2^31` | |
| 3 | `emit_i::<VirtualSignExtendWord>(*t4, a0, 0)` | `t4 := sext([a0])` | `t4 = 0xFFFFFFFF80000000` | |
| 4 | `emit_i::<VirtualSignExtendWord>(*t3, a1, 0)` | `t3 := sext([a1])` | `t3 = 0` | |
| 5 | `emit_b::<VirtualAssertValidDiv0>(*t3, *a2, 0)` | `if t3 = 0 then assert a2 = -1` | `t3 = 0` and `a2 = -1` | OK |
| 6 | `emit_r::<VirtualChangeDivisorW>(*t0, *t4, *t3)` | `t0 := if (t4 as i32 = i32::MIN ∧ t3 as i32 = -1) then 1 else t3` | `t0 = 0` (t4 as i32 = i32::MIN but t3 as i32 = 0 ≠ -1) | |
| 7 | `emit_i::<VirtualSignExtendWord>(*t1, *a2, 0)` | `t1 := sext(a2)` | `t1 = -1` | |
| 8 | `emit_b::<VirtualAssertEQ>(*t1, *a2, 0)` | `assert t1 = a2` | `t1 = -1 = a2` | OK |
| 9 | `emit_i::<SRAI>(*t2, *a3, 31)` | `t2 := SRAI(a3, 31)` | `t2 = SRAI(2^31, 31) = 1` | |
| 10 | `emit_b::<VirtualAssertEQ>(*t2, 0, 0)` | `assert t2 = x0` | `t2 = 1 ≠ x0 = 0` | **PANIC** |

## Nature of the Bug

**Incompleteness**: the inline sequence rejects honest advice that the Jolt tracer itself computed.

The check at line 10 (`SRAI(rem, 31) == 0`) requires `rem < 2^31`.
But the honest remainder advice for `rs1_low = i32::MIN, rs2_low = 0` is `|i32::MIN| = 2^31`,
which fails this check.

The tracer has three cases for the (quotient, remainder) advice, as shown below.

```rust
if y == 0 {
    (-1i32, x.unsigned_abs())            // div-by-zero: rem = |x|
} else if y == -1 && x == i32::MIN {
    (i32::MIN, 0)                        // overflow: rem = 0
} else {
    let remainder = x % y;
    (quotient, remainder.unsigned_abs()) // normal: rem = |x % y|
}
```
The only case the honest pair fails Line 10 is when `y=0`.
Note: Other future tests may fail for the rest, we have not gotten there.
