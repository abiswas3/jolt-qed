/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari
-/

import JoltBytecode.BytecodeExpansions.Common.FormatI
import JoltBytecode.BytecodeExpansions.Common.Virtual
import JoltBytecode.BytecodeExpansions.Common.Riscv
import JoltBytecode.BytecodeExpansions.Common.SimpLemmas

/-!
# SRAI: RISC-V ≡ Jolt Decomposition

## Instruction (RV64I, Format I)

`SRAI rd, rs1, shamt` arithmetically right-shifts the full 64-bit value
in rs1 by shamt[5:0] bits (sign-filling the upper bits) and writes to rd.

## Jolt Decomposition (faithful to Rust implementation)

```
VirtualSRAI              rd, rs1, bitmask             -- arith right shift via ctz(bitmask)
```

where bitmask is precomputed:
```
shift   := imm & 0x3f
ones    := (1 << (64 - shift)) - 1
bitmask := ones << shift
```

## Proof

The bitmask has `shift` trailing zeros, so `ctz(bitmask) = shift = shamt[5:0]`.
VirtualSRAI performs arithmetic right shift by ctz(bitmask) bits, which equals
the RISC-V SRAI semantics.
-/

-- ============================================================================
-- Bitmask computation (faithful to Jolt Rust implementation)
-- ============================================================================

def srai_bitmask (shamt : BitVec 64) : Nat :=
  let shift := (shamt.setWidth 6).toNat
  let ones := (1 <<< (64 - shift)) - 1
  ones <<< shift

-- ctz of the bitmask recovers the shift amount.
lemma ctz_srai_bitmask (shamt : BitVec 64) :
    ctz (srai_bitmask shamt) = (shamt.setWidth 6).toNat := by
  unfold srai_bitmask
  simp only [Nat.shiftLeft_eq, one_mul]
  set shift := (shamt.setWidth 6).toNat
  have h_lt : shift < 64 := by
    have := (shamt.setWidth 6).isLt
    norm_num at this; exact this
  have h_diff_pos : 0 < 64 - shift := by omega
  have h_m_pos : 0 < 2 ^ (64 - shift) - 1 := by
    have : 2 ≤ 2 ^ (64 - shift) :=
      le_trans (show (2 : Nat) ≤ 2 ^ 1 from by norm_num)
        (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  rw [mul_comm, ctz_mul_pow2 shift h_m_pos,
      ctz_of_odd (pow2_sub_one_odd h_diff_pos)]
  omega

-- ============================================================================
-- Jolt decomposition
-- ============================================================================

-- Jolt's decomposition: VirtualSRAI with bitmask.
-- VirtualSRAI performs arithmetic right shift by ctz(bitmask) bits.
def sraiJolt (rs1_val shamt : BitVec 64) : BitVec 64 :=
  rs1_val.sshiftRight (ctz (srai_bitmask shamt))

-- ============================================================================
-- Main theorems
-- ============================================================================

-- Pure-function equivalence: Riscv.srai64 = sraiJolt
theorem srai_eq_sraiJolt (rs1_val shamt : BitVec 64) :
    Riscv.srai64 rs1_val shamt = sraiJolt rs1_val shamt := by
  unfold Riscv.srai64 sraiJolt
  rw [ctz_srai_bitmask]

-- State-level equivalence via Format I lifting.
theorem srai_state_eq (rs1 rd : BitVec 5) (imm : BitVec 64) (s : State) :
    format_i_exec rs1 rd imm Riscv.srai64 s = format_i_exec rs1 rd imm sraiJolt s :=
  format_i_ops_eq_of_fns_eq Riscv.srai64 sraiJolt rs1 rd imm s
    (by funext rs1_val shamt; exact srai_eq_sraiJolt rs1_val shamt)

/-SANITY CHECKS-/
#eval show IO Unit from do
  let mut failures := 0
  for i in [0:256] do
    for s in [0:64] do
      let rs1_val : BitVec 64 := BitVec.ofNat 64 i
      let shamt : BitVec 64 := BitVec.ofNat 64 s
      if Riscv.srai64 rs1_val shamt != sraiJolt rs1_val shamt then
        failures := failures + 1
  if failures == 0 then
    IO.println "✓ Exhaustive check passed: srai64 == sraiJolt for all 16384 test pairs"
  else
    IO.println s!"✗ FAILED: {failures} mismatches found"
