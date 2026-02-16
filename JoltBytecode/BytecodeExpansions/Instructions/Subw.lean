import JoltBytecode.BytecodeExpansions.Common.FormatR
import JoltBytecode.BytecodeExpansions.Common.Virtual
import JoltBytecode.BytecodeExpansions.Common.Riscv

/-!
# SUBW: RISC-V ≡ Jolt Decomposition

## Instruction (RV64I, Format R)

`SUBW rd, rs1, rs2` subtracts the lower 32 bits of rs2 from rs1,
sign-extends the 32-bit result to 64 bits, and writes to rd.

## Jolt Decomposition

```
SUB                   rd, rs1, rs2   -- 64-bit subtraction
VirtualSignExtendWord rd, rd, 0      -- sign-extend lower 32 bits
```

## Proof

Truncation to 32 bits commutes with subtraction (mod 2^32), so the
64-bit SUB followed by truncate+sign-extend equals truncate first
then subtract+sign-extend. State-level equality follows via Format R
lifting.
-/

-- Jolt's decomposition: full 64-bit SUB then sign-extend the lower 32 bits.
def subwJolt (x y : BitVec 64) : BitVec 64 :=
  Jolt.virtualSignExtendWord (Riscv.sub x y)

-- Truncation to 32 bits commutes with subtraction.
private lemma setWidth_sub_32 (x y : BitVec 64) :
    (x - y).setWidth 32 = x.setWidth 32 - y.setWidth 32 := by
  bv_omega

-- Pure-function equivalence: Riscv.subw = subwJolt
theorem subw_eq_subwJolt (x y : BitVec 64) : Riscv.subw x y = subwJolt x y := by
  unfold Riscv.subw subwJolt Riscv.sub Jolt.virtualSignExtendWord
  simp only [setWidth_sub_32]

-- State-level equivalence via Format R lifting.
theorem subw_state_eq (r1 r2 rd : BitVec 5) (s : State) :
    format_r_exec r1 r2 rd Riscv.subw s = format_r_exec r1 r2 rd subwJolt s :=
  format_r_ops_eq_of_fns_eq Riscv.subw subwJolt r1 r2 rd s
    (by funext x y; exact subw_eq_subwJolt x y)

/-SANITY CHECKS-/
-- Sanity check: exhaustive 8-bit test
#eval do
  let mut failures := 0
  for i in List.range 256 do
    for j in List.range 256 do
      let x : BitVec 64 := BitVec.ofNat 64 i
      let y : BitVec 64 := BitVec.ofNat 64 j
      if Riscv.subw x y != subwJolt x y then
        failures := failures + 1
  if failures == 0 then
    IO.println "✓ Exhaustive check passed: subw == subwJolt for all 65536 test pairs"
  else
    IO.println s!"✗ FAILED: {failures} mismatches found"
