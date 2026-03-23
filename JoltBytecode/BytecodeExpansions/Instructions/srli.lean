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
# SRLI: RISC-V ≡ Jolt Decomposition

## Instruction (RV64I, Format I)

`SRLI rd, rs1, shamt` logically right-shifts the full 64-bit value in rs1
by shamt[5:0] bits and writes the result to rd.

## Jolt Decomposition (faithful to Rust implementation)

```
VirtualSRLI              rd, rs1, bitmask             -- logical right shift via ctz(bitmask)
```

where bitmask is precomputed:
```
shift   := imm & 0x3f
ones    := (1 << (64 - shift)) - 1
bitmask := ones << shift
```

## Proof

The bitmask has `shift` trailing zeros, so `ctz(bitmask) = shift = shamt[5:0]`.
Both sides then compute `rs1 >>> shift`.
-/

-- ============================================================================
-- Bitmask computation (faithful to Jolt Rust implementation)
-- ============================================================================

def srli_bitmask (shamt : BitVec 64) : Nat :=
  let shift := (shamt.setWidth 6).toNat
  let ones := (1 <<< (64 - shift)) - 1
  ones <<< shift

-- ctz of the bitmask recovers the shift amount.
lemma ctz_srli_bitmask (shamt : BitVec 64) :
    ctz (srli_bitmask shamt) = (shamt.setWidth 6).toNat := by
  unfold srli_bitmask
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

-- Jolt's decomposition: VirtualSRLI with bitmask.
def srliJolt (rs1_val shamt : BitVec 64) : BitVec 64 :=
  rs1_val >>> ctz (srli_bitmask shamt)

-- ============================================================================
-- Main theorems
-- ============================================================================

-- Pure-function equivalence: Riscv.srli64 = srliJolt
theorem srli_eq_srliJolt (rs1_val shamt : BitVec 64) :
    Riscv.srli64 rs1_val shamt = srliJolt rs1_val shamt := by
  unfold Riscv.srli64 srliJolt
  rw [ctz_srli_bitmask]

-- State-level equivalence via Format I lifting.
theorem srli_state_eq (rs1 rd : BitVec 5) (imm : BitVec 64) (s : State) :
    format_i_exec rs1 rd imm Riscv.srli64 s = format_i_exec rs1 rd imm srliJolt s :=
  format_i_ops_eq_of_fns_eq Riscv.srli64 srliJolt rs1 rd imm s
    (by funext rs1_val shamt; exact srli_eq_srliJolt rs1_val shamt)

/-SANITY CHECKS-/
#eval show IO Unit from do
  let mut failures := 0
  for i in [0:256] do
    for s in [0:64] do
      let rs1_val : BitVec 64 := BitVec.ofNat 64 i
      let shamt : BitVec 64 := BitVec.ofNat 64 s
      if Riscv.srli64 rs1_val shamt != srliJolt rs1_val shamt then
        failures := failures + 1
  if failures == 0 then
    IO.println "✓ Exhaustive check passed: srli64 == srliJolt for all 16384 test pairs"
  else
    IO.println s!"✗ FAILED: {failures} mismatches found"
