/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari
-/

import JoltBytecode.BytecodeExpansions.Common.FormatR
import JoltBytecode.BytecodeExpansions.Common.Virtual
import JoltBytecode.BytecodeExpansions.Common.Riscv
import JoltBytecode.BytecodeExpansions.Common.SimpLemmas

/-!
# SRL: RISC-V ≡ Jolt Decomposition

## Instruction (RV64I, Format R)

`SRL rd, rs1, rs2` logically right-shifts rs1 by rs2[5:0] bits and writes
the result to rd.

## Jolt Decomposition (faithful to Rust implementation)

```
VirtualShiftRightBitmask v_bitmask, rs2, 0           -- compute bitmask from rs2
VirtualSRL               rd, rs1, v_bitmask           -- logical right shift via ctz(bitmask)
```

## Proof

The bitmask has `shift` trailing zeros, so `ctz(bitmask) = shift = rs2[5:0]`.
Both sides compute `rs1 >>> shift`.
-/

-- ============================================================================
-- Bitmask computation (VirtualShiftRightBitmask, 64-bit mode)
-- ============================================================================

def srl_bitmask (rs2_val : BitVec 64) : Nat :=
  let shift := (rs2_val.setWidth 6).toNat
  let ones := (1 <<< (64 - shift)) - 1
  ones <<< shift

-- ctz of the bitmask recovers the shift amount.
lemma ctz_srl_bitmask (rs2_val : BitVec 64) :
    ctz (srl_bitmask rs2_val) = (rs2_val.setWidth 6).toNat := by
  unfold srl_bitmask
  simp only [Nat.shiftLeft_eq, one_mul]
  set shift := (rs2_val.setWidth 6).toNat
  have h_lt : shift < 64 := by
    have := (rs2_val.setWidth 6).isLt
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

-- Jolt's decomposition: VirtualShiftRightBitmask → VirtualSRL.
def srlJolt (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  rs1_val >>> ctz (srl_bitmask rs2_val)

-- ============================================================================
-- Main theorems
-- ============================================================================

-- Pure-function equivalence: Riscv.srl = srlJolt
theorem srl_eq_srlJolt (rs1_val rs2_val : BitVec 64) :
    Riscv.srl rs1_val rs2_val = srlJolt rs1_val rs2_val := by
  unfold Riscv.srl srlJolt
  rw [ctz_srl_bitmask]

-- State-level equivalence via Format R lifting.
theorem srl_state_eq (rs1 rs2 rd : BitVec 5) (s : State) :
    format_r_exec rs1 rs2 rd Riscv.srl s = format_r_exec rs1 rs2 rd srlJolt s :=
  format_r_ops_eq_of_fns_eq Riscv.srl srlJolt rs1 rs2 rd s
    (by funext rs1_val rs2_val; exact srl_eq_srlJolt rs1_val rs2_val)

/-SANITY CHECKS-/
#eval show IO Unit from do
  let mut failures := 0
  for i in [0:256] do
    for s in [0:64] do
      let rs1_val : BitVec 64 := BitVec.ofNat 64 i
      let rs2_val : BitVec 64 := BitVec.ofNat 64 s
      if Riscv.srl rs1_val rs2_val != srlJolt rs1_val rs2_val then
        failures := failures + 1
  if failures == 0 then
    IO.println "✓ Exhaustive check passed: srl == srlJolt for all 16384 test pairs"
  else
    IO.println s!"✗ FAILED: {failures} mismatches found"
