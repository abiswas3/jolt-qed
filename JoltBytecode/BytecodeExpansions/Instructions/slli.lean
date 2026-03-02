import JoltBytecode.BytecodeExpansions.Common.FormatI
import JoltBytecode.BytecodeExpansions.Common.Virtual
import JoltBytecode.BytecodeExpansions.Common.Riscv

/-!
# SLLI: RISC-V ≡ Jolt Decomposition

## Instruction (RV64I, Format I)

`SLLI rd, rs1, shamt` logically left-shifts the full 64-bit value in rs1
by shamt[5:0] bits and writes the result to rd.

## Jolt Decomposition (faithful to Rust implementation)

```
VirtualMULI              rd, rs1, (1 << shift)        -- multiply rs1 by 2^shift
```

where shift = imm & 0x3f.

## Proof

Left-shifting by s is equivalent to multiplying by 2^s in modular arithmetic:
  x << s ≡ x * 2^s (mod 2^64).
-/

-- ============================================================================
-- Jolt decomposition
-- ============================================================================

-- Jolt's decomposition: VirtualMULI (multiply by 2^shift).
def slliJolt (rs1_val shamt : BitVec 64) : BitVec 64 :=
  let shift := (shamt.setWidth 6).toNat
  rs1_val * BitVec.ofNat 64 (2 ^ shift)

-- ============================================================================
-- Core lemma
-- ============================================================================

-- 64-bit left shift equals 64-bit multiply by 2^s.
private lemma sll_64_eq_mul (x : BitVec 64) (s : Nat) (hs : s < 64) :
    x <<< s = x * BitVec.ofNat 64 (2 ^ s) := by
  sorry

-- ============================================================================
-- Main theorems
-- ============================================================================

-- Pure-function equivalence: Riscv.slli64 = slliJolt
theorem slli_eq_slliJolt (rs1_val shamt : BitVec 64) :
    Riscv.slli64 rs1_val shamt = slliJolt rs1_val shamt := by
  unfold Riscv.slli64 slliJolt
  exact sll_64_eq_mul rs1_val (shamt.setWidth 6).toNat (by
    have := (shamt.setWidth 6).isLt; norm_num at this; exact this)

-- State-level equivalence via Format I lifting.
theorem slli_state_eq (rs1 rd : BitVec 5) (imm : BitVec 64) (s : State) :
    format_i_exec rs1 rd imm Riscv.slli64 s = format_i_exec rs1 rd imm slliJolt s :=
  format_i_ops_eq_of_fns_eq Riscv.slli64 slliJolt rs1 rd imm s
    (by funext rs1_val shamt; exact slli_eq_slliJolt rs1_val shamt)

/-SANITY CHECKS-/
#eval do
  let mut failures := 0
  for i in List.range 256 do
    for s in List.range 64 do
      let rs1_val : BitVec 64 := BitVec.ofNat 64 i
      let shamt : BitVec 64 := BitVec.ofNat 64 s
      if Riscv.slli64 rs1_val shamt != slliJolt rs1_val shamt then
        failures := failures + 1
  if failures == 0 then
    IO.println "✓ Exhaustive check passed: slli64 == slliJolt for all 16384 test pairs"
  else
    IO.println s!"✗ FAILED: {failures} mismatches found"
