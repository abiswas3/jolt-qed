import JoltBytecode.BytecodeExpansions.Common.FormatR
import JoltBytecode.BytecodeExpansions.Common.Virtual
import JoltBytecode.BytecodeExpansions.Common.Riscv

/-!
# MULW: RISC-V ≡ Jolt Decomposition

## Instruction (RV64M, Format R)

`MULW rd, rs1, rs2` multiplies the lower 32 bits of rs1 and rs2,
sign-extends the lower 32 bits of the product to 64 bits, and writes to rd.

## Jolt Decomposition (faithful to Rust implementation)

```
MUL                      rd, rs1, rs2                 -- 64-bit multiply
VirtualSignExtendWord    rd, rd, 0                    -- sign-extend lower 32 bits
```

## Proof

Both sides compute `((rs1 * rs2).setWidth 32).signExtend 64`. The Jolt
decomposition performs the full 64-bit multiply (MUL) then truncates and
sign-extends (VirtualSignExtendWord), which is definitionally equal to the
RISC-V MULW semantics since truncation to 32 bits commutes with multiplication.
-/

-- ============================================================================
-- Jolt decomposition
-- ============================================================================

-- Jolt's decomposition: MUL → VirtualSignExtendWord.
def mulwJolt (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  Jolt.virtualSignExtendWord (Riscv.mul rs1_val rs2_val)

-- ============================================================================
-- Main theorems
-- ============================================================================

-- Pure-function equivalence: Riscv.mulw = mulwJolt
theorem mulw_eq_mulwJolt (rs1_val rs2_val : BitVec 64) :
    Riscv.mulw rs1_val rs2_val = mulwJolt rs1_val rs2_val := by
  unfold Riscv.mulw mulwJolt Riscv.mul Jolt.virtualSignExtendWord
  rfl

-- State-level equivalence via Format R lifting.
theorem mulw_state_eq (rs1 rs2 rd : BitVec 5) (s : State) :
    format_r_exec rs1 rs2 rd Riscv.mulw s = format_r_exec rs1 rs2 rd mulwJolt s :=
  format_r_ops_eq_of_fns_eq Riscv.mulw mulwJolt rs1 rs2 rd s
    (by funext rs1_val rs2_val; exact mulw_eq_mulwJolt rs1_val rs2_val)

/-SANITY CHECKS-/
#eval do
  let mut failures := 0
  for i in List.range 256 do
    for j in List.range 256 do
      let rs1_val : BitVec 64 := BitVec.ofNat 64 i
      let rs2_val : BitVec 64 := BitVec.ofNat 64 j
      if Riscv.mulw rs1_val rs2_val != mulwJolt rs1_val rs2_val then
        failures := failures + 1
  if failures == 0 then
    IO.println "✓ Exhaustive check passed: mulw == mulwJolt for all 65536 test pairs"
  else
    IO.println s!"✗ FAILED: {failures} mismatches found"
