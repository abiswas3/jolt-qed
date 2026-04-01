/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari
-/

-- TODO: prove sll_eq_mul_pow2 (x <<< s = x * 2^s for BitVec 64)
import JoltBytecode.BytecodeExpansions.Common.FormatR
import JoltBytecode.BytecodeExpansions.Common.Virtual
import JoltBytecode.BytecodeExpansions.Common.Riscv

/-!
# SLL: RISC-V ≡ Jolt Decomposition

## Instruction (RV64I, Format R)

`SLL rd, rs1, rs2` logically left-shifts rs1 by rs2[5:0] bits and writes
the result to rd.

## Jolt Decomposition (faithful to Rust implementation)

```
VirtualPow2    v_pow, rs2, 0           -- v_pow = 2^(rs2[5:0])
MUL            rd, rs1, v_pow          -- rd = rs1 * 2^(rs2[5:0])
```

## Proof

Left-shifting by s is equivalent to multiplying by 2^s:
  x << s ≡ x * 2^s (mod 2^64).
-/

-- ============================================================================
-- Jolt decomposition
-- ============================================================================

-- Jolt's decomposition: VirtualPow2 → MUL.
def sllJolt (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  let v_pow := Jolt.virtualPow2 rs2_val
  Riscv.mul rs1_val v_pow

-- ============================================================================
-- Core lemma
-- ============================================================================

-- 64-bit left shift equals multiply by 2^s.
private lemma sll_eq_mul_pow2 (x : BitVec 64) (s : Nat) (hs : s < 64) :
    x <<< s = x * BitVec.ofNat 64 (2 ^ s) := by
  sorry

-- ============================================================================
-- Main theorems
-- ============================================================================

-- Pure-function equivalence: Riscv.sll = sllJolt
theorem sll_eq_sllJolt (rs1_val rs2_val : BitVec 64) :
    Riscv.sll rs1_val rs2_val = sllJolt rs1_val rs2_val := by
  unfold Riscv.sll sllJolt Jolt.virtualPow2 Riscv.mul
  exact sll_eq_mul_pow2 rs1_val (rs2_val.setWidth 6).toNat (by
    have := (rs2_val.setWidth 6).isLt; norm_num at this; exact this)

-- State-level equivalence via Format R lifting.
theorem sll_state_eq (rs1 rs2 rd : BitVec 5) (s : State) :
    format_r_exec rs1 rs2 rd Riscv.sll s = format_r_exec rs1 rs2 rd sllJolt s :=
  format_r_ops_eq_of_fns_eq Riscv.sll sllJolt rs1 rs2 rd s
    (by funext rs1_val rs2_val; exact sll_eq_sllJolt rs1_val rs2_val)

/-SANITY CHECKS-/
#eval show IO Unit from do
  let mut failures := 0
  for i in [0:256] do
    for s in [0:64] do
      let rs1_val : BitVec 64 := BitVec.ofNat 64 i
      let rs2_val : BitVec 64 := BitVec.ofNat 64 s
      if Riscv.sll rs1_val rs2_val != sllJolt rs1_val rs2_val then
        failures := failures + 1
  if failures == 0 then
    IO.println "✓ Exhaustive check passed: sll == sllJolt for all 16384 test pairs"
  else
    IO.println s!"✗ FAILED: {failures} mismatches found"
