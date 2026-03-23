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
# SRA: RISC-V ≡ Jolt Decomposition

## Instruction (RV64I, Format R)

`SRA rd, rs1, rs2` arithmetically right-shifts rs1 by rs2[5:0] bits
(sign-filling the upper bits) and writes to rd.

## Jolt Decomposition (faithful to Rust implementation)

```
VirtualShiftRightBitmask v_bitmask, rs2, 0           -- compute bitmask from rs2
VirtualSRA               rd, rs1, v_bitmask           -- arith right shift via ctz(bitmask)
```

## Proof

The bitmask has `shift` trailing zeros, so `ctz(bitmask) = shift = rs2[5:0]`.
VirtualSRA performs arithmetic right shift by ctz(bitmask), which equals
the RISC-V SRA semantics.
-/

-- ============================================================================
-- Bitmask computation (VirtualShiftRightBitmask, 64-bit mode)
-- ============================================================================

def sra_bitmask (rs2_val : BitVec 64) : Nat :=
  let shift := (rs2_val.setWidth 6).toNat
  let ones := (1 <<< (64 - shift)) - 1
  ones <<< shift

-- ctz of the bitmask recovers the shift amount.
lemma ctz_sra_bitmask (rs2_val : BitVec 64) :
    ctz (sra_bitmask rs2_val) = (rs2_val.setWidth 6).toNat := by
  unfold sra_bitmask
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

-- Jolt's decomposition: VirtualShiftRightBitmask → VirtualSRA.
def sraJolt (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  rs1_val.sshiftRight (ctz (sra_bitmask rs2_val))

-- ============================================================================
-- Main theorems
-- ============================================================================

-- Pure-function equivalence: Riscv.sra = sraJolt
theorem sra_eq_sraJolt (rs1_val rs2_val : BitVec 64) :
    Riscv.sra rs1_val rs2_val = sraJolt rs1_val rs2_val := by
  unfold Riscv.sra sraJolt
  rw [ctz_sra_bitmask]

-- State-level equivalence via Format R lifting.
theorem sra_state_eq (rs1 rs2 rd : BitVec 5) (s : State) :
    format_r_exec rs1 rs2 rd Riscv.sra s = format_r_exec rs1 rs2 rd sraJolt s :=
  format_r_ops_eq_of_fns_eq Riscv.sra sraJolt rs1 rs2 rd s
    (by funext rs1_val rs2_val; exact sra_eq_sraJolt rs1_val rs2_val)

/-SANITY CHECKS-/
#eval show IO Unit from do
  let mut failures := 0
  for i in [0:256] do
    for s in [0:64] do
      let rs1_val : BitVec 64 := BitVec.ofNat 64 i
      let rs2_val : BitVec 64 := BitVec.ofNat 64 s
      if Riscv.sra rs1_val rs2_val != sraJolt rs1_val rs2_val then
        failures := failures + 1
  if failures == 0 then
    IO.println "✓ Exhaustive check passed: sra == sraJolt for all 16384 test pairs"
  else
    IO.println s!"✗ FAILED: {failures} mismatches found"
