+++
title = "Notes"
+++

## Modelling load from memory

If you look closely at how `lw` is implemented, the `read_word_val` writes stores value at address as a Natural number. 
However, the value in memory might be negative, so you might wonder if this introduces a bug?

```lean
def read_word_val (addr : BitVec 64) (s : State) : Nat :=
  (read_mem addr s).toNat +
  (read_mem (addr + 1) s).toNat * 2^8 +
  (read_mem (addr + 2) s).toNat * 2^16 +
  (read_mem (addr + 3) s).toNat * 2^24 
```

The pipeline `raw bytes → Nat → BitVec 32 → signExtend → BitVec 64` preserves signs.

**Example: the value -1 stored as a 32-bit signed integer**

Memory (little-endian): `[0xFF, 0xFF, 0xFF, 0xFF]`

1. **`read_word_val` → `Nat`:**
   ```
   0xFF + 0xFF * 2^8 + 0xFF * 2^16 + 0xFF * 2^24
   = 4294967295  (= 2^32 - 1)
   ```

2. **`BitVec.ofNat 32` → `BitVec 32`:**
   No information is lost because the value already fits in 32 bits
   (`n % 2^32 = n` when `n < 2^32`). The bit pattern `0xFFFFFFFF` is -1
   in two's complement.

3. **`.signExtend 64` → `BitVec 64`:**
   `signExtend` checks bit 31 (MSB). It's 1, so it extends with 1s,
   giving `0xFFFFFFFFFFFFFFFF` — which is -1 as a 64-bit signed integer.

**Why it's lossless:** The `Nat` intermediate can represent every possible
4-byte combination (range `[0, 2^32 - 1]`), and `BitVec.ofNat 32` maps
that range bijectively onto `BitVec 32`. No bits are ever dropped, so
`signExtend` always sees the correct bit pattern to recover the sign.

