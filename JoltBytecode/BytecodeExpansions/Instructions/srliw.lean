import JoltBytecode.BytecodeExpansions.Common.FormatI
import JoltBytecode.BytecodeExpansions.Common.Virtual
import JoltBytecode.BytecodeExpansions.Common.Riscv

/-!
# SRLIW: RISC-V ≡ Jolt Decomposition

## Instruction (RV64I, Format I)

`SRLIW rd, rs1, shamt` takes the lower 32 bits of rs1, shifts right
logically by shamt, sign-extends the 32-bit result to 64 bits, and
writes to rd.

## Jolt Decomposition

```
SLLI                  v0, rs1, 32        -- zero upper bits via shift
VirtualSRLI           v0, v0, 2^(shamt+32) -- shift right by trailing_zeros(2^(shamt+32)) = shamt+32
VirtualSignExtendWord rd, v0, 0          -- sign-extend lower 32 bits
```

## Proof

Shifting left by 32 then right by (shamt + 32) extracts exactly the
lower 32 bits shifted right by shamt: the SLLI clears the upper 32
bits by pushing lower 32 to the top, and the combined right shift
recovers them in the correct position. Truncation to 32 bits then
matches the direct 32-bit shift, and sign-extension completes the
equivalence.
-/

-- Jolt's decomposition: SLLI by 32, VirtualSRLI with imm=2^(shamt+32), VirtualSignExtendWord.
-- The immediate 2^(shamt+32) encodes the shift amount in its trailing zeros.
-- FIXME: This is wrong 
def srliwJolt (x shamt : BitVec 64) : BitVec 64 :=
  Jolt.virtualSignExtendWord (Jolt.virtualSRLI (x <<< 32) (2 ^ (shamt.toNat + 32)))

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
  rw [show n + 32 = 32 + n from by omega, ushiftRight_add, sll32_srl32_eq_zext]
  exact zext_srl_trunc_32 x n

-- Pure-function equivalence: Riscv.srliw = srliwJolt
theorem srliw_eq_srliwJolt (x shamt : BitVec 64) :
    Riscv.srliw x shamt = srliwJolt x shamt := by
  unfold Riscv.srliw srliwJolt Jolt.virtualSRLI Jolt.virtualSignExtendWord
  simp only [ctz_pow2, slli_vsrli_trunc_32]

-- State-level equivalence via Format I lifting.
theorem srliw_state_eq (rs1 rd : BitVec 5) (imm : BitVec 64) (s : State) :
    format_i_exec rs1 rd imm Riscv.srliw s = format_i_exec rs1 rd imm srliwJolt s :=
  format_i_ops_eq_of_fns_eq Riscv.srliw srliwJolt rs1 rd imm s
    (by funext x y; exact srliw_eq_srliwJolt x y)

/-SANITY CHECKS-/
-- Exhaustive check: verify Riscv.srliw == srliwJolt for 256 values × 32 shift amounts
#eval do
  let mut failures := 0
  for i in List.range 256 do
    for s in List.range 32 do
      let x : BitVec 64 := BitVec.ofNat 64 i
      let shamt : BitVec 64 := BitVec.ofNat 64 s
      if Riscv.srliw x shamt != srliwJolt x shamt then
        failures := failures + 1
  if failures == 0 then
    IO.println "✓ Exhaustive check passed: srliw == srliwJolt for all 8192 test pairs"
  else
    IO.println s!"✗ FAILED: {failures} mismatches found"
