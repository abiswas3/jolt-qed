import JoltBytecode.BytecodeExpansions.Common.FormatI
import JoltBytecode.BytecodeExpansions.Common.Virtual
import JoltBytecode.BytecodeExpansions.Common.Riscv

/-!
# ADDIW: RISC-V ≡ Jolt Decomposition

## Instruction (RV64I, Format I)

`ADDIW rd, rs1, imm` adds the sign-extended immediate to rs1, truncates the
result to 32 bits, sign-extends to 64 bits, and writes to rd.

## Jolt Decomposition (faithful to Rust implementation)

```
ADDI                     rd, rs1, imm                 -- add immediate (64-bit)
VirtualSignExtendWord    rd, rd, 0                    -- sign-extend lower 32 bits
```

## Proof

Both sides compute `(rs1 + imm).setWidth 32 |>.signExtend 64`. The Jolt
decomposition performs the full 64-bit add (ADDI) then truncates and
sign-extends (VirtualSignExtendWord), which is definitionally equal to the
RISC-V ADDIW semantics.
-/

-- ============================================================================
-- Jolt decomposition
-- ============================================================================

-- Jolt's decomposition: ADDI → VirtualSignExtendWord.
def addiwJolt (rs1_val imm : BitVec 64) : BitVec 64 :=
  Jolt.virtualSignExtendWord (rs1_val + imm)

-- ============================================================================
-- Main theorems
-- ============================================================================

-- Pure-function equivalence: Riscv.addiw = addiwJolt
theorem addiw_eq_addiwJolt (rs1_val imm : BitVec 64) :
    Riscv.addiw rs1_val imm = addiwJolt rs1_val imm := by
  unfold Riscv.addiw addiwJolt Jolt.virtualSignExtendWord
  rfl

-- State-level equivalence via Format I lifting.
theorem addiw_state_eq (rs1 rd : BitVec 5) (imm : BitVec 64) (s : State) :
    format_i_exec rs1 rd imm Riscv.addiw s = format_i_exec rs1 rd imm addiwJolt s :=
  format_i_ops_eq_of_fns_eq Riscv.addiw addiwJolt rs1 rd imm s
    (by funext rs1_val shamt; exact addiw_eq_addiwJolt rs1_val shamt)

/-SANITY CHECKS-/
-- Exhaustive check: verify Riscv.addiw == addiwJolt for 256 × 256 values
#eval do
  let mut failures := 0
  for i in List.range 256 do
    for j in List.range 256 do
      let rs1_val : BitVec 64 := BitVec.ofNat 64 i
      let imm : BitVec 64 := BitVec.ofNat 64 j
      if Riscv.addiw rs1_val imm != addiwJolt rs1_val imm then
        failures := failures + 1
  if failures == 0 then
    IO.println "✓ Exhaustive check passed: addiw == addiwJolt for all 65536 test pairs"
  else
    IO.println s!"✗ FAILED: {failures} mismatches found"
