# Bug Report: DIVUW Inline Sequence Accepts Non-Canonical Quotient Advice

> This is not a bug -- witness does not have to be unique.

## Instruction
DIVUW — unsigned 32-bit division word (RV64M).
Divides the low 32 bits of `rs1` by the low 32 bits of `rs2`, treating both as
unsigned 32-bit integers, and writes the 32-bit quotient sign-extended to 64 bits
into `rd`.

## Nature of the Bug

The current DIVUW inline sequence accepts non-canonical quotient advice when the
low-32 divisor is zero.

This is not the same failure mode as the DIVW incompleteness issue: honest DIVUW
advice does pass the current inline sequence. The problem is that a malicious
prover can provide a different 64-bit advice value with the same low 32 bits, and
the sequence still accepts it.

If the intended soundness statement is that accepted advice must equal the tracer's
honest advice, the current sequence is underconstrained.

## Triggering Input

- `rs2_low = 0`
- `rs1_low` arbitrary

## Honest Advice (from Jolt Tracer)

From `tracer/src/instruction/divuw.rs`:

```rust
if y == 0 {
    u32::MAX as u64 // 32-bit operation: quotient is u32::MAX
} else {
    (x / y) as u64
}
```

For `y = 0`, the tracer declares:

- **quotient advice** `quo = 0x00000000ffffffff`

## Accepted Non-Canonical Advice

Instead provide:

- **quotient advice** `quo = 0xffffffffffffffff`

This is not equal to the tracer's honest advice, but it has the same low 32 bits.

## Inline Sequence Trace

Initial relevant state:

- `rs1 = zext(rs1_low)`
- `rs2 = zext(rs2_low) = 0`
- advice `quo = 0xffffffffffffffff`

| Line | Rust | Instruction | Result | Status |
|------|------|-------------|--------|--------|
| 1 | `emit_i::<VirtualZeroExtendWord>(*rs1, self.operands.rs1, 0)` | `rs1 := zext(rs1.low32)` | `rs1 = zext(rs1_low)` | |
| 2 | `emit_i::<VirtualZeroExtendWord>(*rs2, self.operands.rs2, 0)` | `rs2 := zext(rs2.low32)` | `rs2 = 0` | |
| 3 | `emit_j::<VirtualAdvice>(*quo, 0)` | `quo := advice` | `quo = 0xffffffffffffffff` | |
| 4 | `emit_b::<VirtualAssertMulUNoOverflow>(*quo, *rs2, 0)` | assert `quo * rs2` does not overflow | `quo * 0 = 0` | OK |
| 5 | `emit_r::<MUL>(*temp, *quo, *rs2)` | `temp := quo * rs2` | `temp = 0` | |
| 6 | `emit_b::<VirtualAssertLTE>(*temp, *rs1, 0)` | assert `temp <= rs1` | `0 <= rs1` | OK |
| 7 | `emit_r::<SUB>(*temp, *rs1, *temp)` | `temp := rs1 - temp` | `temp = rs1` | |
| 8 | `emit_b::<VirtualAssertValidUnsignedRemainder>(*temp, *rs2, 0)` | assert `rs2 = 0 ∨ temp < rs2` | `rs2 = 0` | OK |
| 9 | `emit_i::<VirtualSignExtendWord>(*temp, *quo, 0)` | `temp := sext(quo.low32)` | `temp = 0xffffffffffffffff` | |
| 10 | `emit_b::<VirtualAssertValidDiv0>(*rs2, *temp, 0)` | if `rs2 = 0`, assert `temp = -1` | `temp = -1` | OK |
| 11 | `emit_i::<ADDI>(rd, *temp, 0)` | `rd := temp` | correct architectural output | OK |

## Why the Guards Do Not Pin Down the Advice

The final div-by-zero assertion is applied after `VirtualSignExtendWord`:

```rust
asm.emit_i::<VirtualSignExtendWord>(*temp, *quo, 0);
asm.emit_b::<VirtualAssertValidDiv0>(*rs2, *temp, 0);
```

So the assertion only sees `sign_extend(quo.low32)`, not `quo` itself. Both

- `0x00000000ffffffff`
- `0xffffffffffffffff`

sign-extend from low 32 bits to `0xffffffffffffffff`, so both pass.

When `rs2 != 0`, the multiplication and LTE guards force `quo` to be small enough.
The missing constraint is exposed specifically in the div-by-zero case, because all
product/remainder checks become vacuous under multiplication by zero and the
`divisor = 0` short-circuit.

## Suggested Fix

Add a quotient canonicalization check requiring the advice to be zero-extended u32:

```text
quo >> 32 == 0
```

In the current instruction vocabulary this could be implemented as a shift-right by
32 followed by `VirtualAssertEQ` against `x0` or an equivalent virtual zero check.

It should not be a shift by 31: honest div-by-zero DIVUW advice is
`0x00000000ffffffff`, and shifting it by 31 gives `1`, which would reject honest
advice. A shift by 32 accepts every canonical u32 advice value and rejects high
32-bit pollution such as `0xffffffffffffffff`.

## Impact

This does not appear to produce an incorrect architectural writeback, because the
sequence sign-extends `quo.low32` before writing `rd`. It does, however, invalidate
the stronger advice-uniqueness property:

```text
accepted quotient advice = tracer quotient advice
```

The current sequence only enforces equality after truncating to low 32 bits and
sign-extending for writeback.
