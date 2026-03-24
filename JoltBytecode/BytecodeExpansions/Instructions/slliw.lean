/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari
-/

import JoltBytecode.BytecodeExpansions.Common.FormatI
import JoltBytecode.BytecodeExpansions.Common.Virtual
import JoltBytecode.BytecodeExpansions.Common.Riscv

/-!
# SLLIW: RISC-V ≡ Jolt Decomposition

## Instruction (RV64I, Format I)

`SLLIW rd, rs1, shamt` takes the lower 32 bits of rs1, left shifts by
shamt[4:0], sign-extends the 32-bit result to 64 bits, and writes to rd.

## Jolt Decomposition (faithful to Rust implementation)

```
VirtualMULI              rd, rs1, (1 << shift)        -- multiply rs1 by 2^shift
VirtualSignExtendWord    rd, rd, 0                     -- sign-extend result to 64
```

where shift = imm & 0x1f.

## Proof

Left-shifting by s is equivalent to multiplying by 2^s. The 64-bit
multiplication truncated to 32 bits equals the direct 32-bit left shift,
because modular multiplication commutes with truncation:
  (x % 2^32) * 2^s % 2^32 = x * 2^s % 2^32.
Sign-extension of the 32-bit result completes the equivalence.
-/

-- ============================================================================
-- Jolt decomposition
-- ============================================================================

-- Jolt's decomposition: VirtualMULI → VirtualSignExtendWord.
-- VirtualMULI multiplies rs1 by 2^shift (the immediate is 1 << shift).
def slliwJolt (rs1_val shamt : BitVec 64) : BitVec 64 :=
  let shift := (shamt.setWidth 5).toNat
  let v_mul := rs1_val * BitVec.ofNat 64 (2 ^ shift)
  Jolt.virtualSignExtendWord v_mul

-- ============================================================================
-- Core lemma
-- ============================================================================

-- 32-bit left shift equals 64-bit multiply by 2^s, truncated to 32 bits.
private lemma sll_32_eq_mul_trunc (x : BitVec 64) (s : Nat) (hs : s < 32) :
    x.setWidth 32 <<< s = (x * BitVec.ofNat 64 (2 ^ s)).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, BitVec.toNat_mul,
             BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  -- Step 1: 2^s % 2^64 = 2^s (since s < 32 < 64)
  rw [Nat.mod_eq_of_lt (show 2 ^ s < 2 ^ 64 from Nat.pow_lt_pow_right (by omega) (by omega))]
  -- Step 2: ... % 2^64 % 2^32 = ... % 2^32
  rw [Nat.mod_mod_of_dvd _ (show (2:Nat) ^ 32 ∣ 2 ^ 64 from ⟨2 ^ 32, by norm_num⟩)]
  -- Step 3: (a % n) * b % n = a * b % n
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

-- ============================================================================
-- Main theorems
-- ============================================================================

-- Pure-function equivalence: Riscv.slliw = slliwJolt
theorem slliw_eq_slliwJolt (rs1_val shamt : BitVec 64) :
    Riscv.slliw rs1_val shamt = slliwJolt rs1_val shamt := by
  unfold Riscv.slliw slliwJolt Jolt.virtualSignExtendWord
  congr 1
  exact sll_32_eq_mul_trunc rs1_val (shamt.setWidth 5).toNat (by
    have := (shamt.setWidth 5).isLt; norm_num at this; exact this)

-- State-level equivalence via Format I lifting.
theorem slliw_state_eq (rs1 rd : BitVec 5) (imm : BitVec 64) (s : State) :
    format_i_exec rs1 rd imm Riscv.slliw s = format_i_exec rs1 rd imm slliwJolt s :=
  format_i_ops_eq_of_fns_eq Riscv.slliw slliwJolt rs1 rd imm s
    (by funext rs1_val shamt; exact slliw_eq_slliwJolt rs1_val shamt)

/-SANITY CHECKS-/
-- Exhaustive check: verify Riscv.slliw == slliwJolt for 256 values × 32 shift amounts
#eval show IO Unit from do
  let mut failures := 0
  for i in [0:256] do
    for s in [0:32] do
      let rs1_val : BitVec 64 := BitVec.ofNat 64 i
      let shamt : BitVec 64 := BitVec.ofNat 64 s
      if Riscv.slliw rs1_val shamt != slliwJolt rs1_val shamt then
        failures := failures + 1
  if failures == 0 then
    IO.println "✓ Exhaustive check passed: slliw == slliwJolt for all 8192 test pairs"
  else
    IO.println s!"✗ FAILED: {failures} mismatches found"
