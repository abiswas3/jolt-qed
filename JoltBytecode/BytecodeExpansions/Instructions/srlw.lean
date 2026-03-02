-- TODO: prove ctz_srlw_bitmask and srlw_eq_srlwJolt
import JoltBytecode.BytecodeExpansions.Common.FormatR
import JoltBytecode.BytecodeExpansions.Common.Virtual
import JoltBytecode.BytecodeExpansions.Common.Riscv
import JoltBytecode.BytecodeExpansions.Common.SimpLemmas

/-!
# SRLW: RISC-V ≡ Jolt Decomposition

## Instruction (RV64I, Format R)

`SRLW rd, rs1, rs2` takes the lower 32 bits of rs1, logically right-shifts
by rs2[4:0], sign-extends the 32-bit result to 64 bits, and writes to rd.

## Jolt Decomposition (faithful to Rust implementation)

```
SLLI                     v_rs1, rs1, 32               -- clear upper 32 bits
ORI                      v_bitmask, rs2, 32           -- shift amount += 32
VirtualShiftRightBitmask v_bitmask, v_bitmask, 0      -- compute bitmask
VirtualSRL               rd, v_rs1, v_bitmask         -- logical right shift
VirtualSignExtendWord    rd, rd, 0                    -- sign-extend lower 32
```

## Proof

The SLLI 32 clears the upper 32 bits by pushing low bits to the top.
ORI with 32 sets bit 5 of the shift amount, making it (rs2[4:0] + 32).
The combined right shift by (n+32) after left shift by 32 extracts the
lower 32 bits shifted right by n. The same pattern as SRLIW.
-/

-- ============================================================================
-- Bitmask computation
-- ============================================================================

-- The bitmask encodes shift = rs2[4:0] + 32 (from ORI rs2, 32 + VirtualShiftRightBitmask).
def srlw_bitmask (rs2_val : BitVec 64) : Nat :=
  let v_bitmask_in := Riscv.ori rs2_val 32#64
  let shift := (v_bitmask_in.setWidth 6).toNat
  let ones := (1 <<< (64 - shift)) - 1
  ones <<< shift

-- ctz of the bitmask recovers rs2[4:0] + 32.
lemma ctz_srlw_bitmask (rs2_val : BitVec 64) :
    ctz (srlw_bitmask rs2_val) = (rs2_val.setWidth 5).toNat + 32 := by
  sorry

-- ============================================================================
-- Jolt decomposition
-- ============================================================================

-- Jolt's decomposition: SLLI 32 → ORI 32 → VirtualShiftRightBitmask → VirtualSRL → VirtualSignExtendWord.
def srlwJolt (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  let v_rs1 := Riscv.slli rs1_val 32
  let bitmask := srlw_bitmask rs2_val
  let v_result := v_rs1 >>> ctz bitmask
  Jolt.virtualSignExtendWord v_result

-- ============================================================================
-- Main theorems
-- ============================================================================

-- Pure-function equivalence: Riscv.srlw = srlwJolt
theorem srlw_eq_srlwJolt (rs1_val rs2_val : BitVec 64) :
    Riscv.srlw rs1_val rs2_val = srlwJolt rs1_val rs2_val := by
  sorry

-- State-level equivalence via Format R lifting.
theorem srlw_state_eq (rs1 rs2 rd : BitVec 5) (s : State) :
    format_r_exec rs1 rs2 rd Riscv.srlw s = format_r_exec rs1 rs2 rd srlwJolt s :=
  format_r_ops_eq_of_fns_eq Riscv.srlw srlwJolt rs1 rs2 rd s
    (by funext rs1_val rs2_val; exact srlw_eq_srlwJolt rs1_val rs2_val)

/-SANITY CHECKS-/
#eval do
  let mut failures := 0
  for i in List.range 256 do
    for s in List.range 32 do
      let rs1_val : BitVec 64 := BitVec.ofNat 64 i
      let rs2_val : BitVec 64 := BitVec.ofNat 64 s
      if Riscv.srlw rs1_val rs2_val != srlwJolt rs1_val rs2_val then
        failures := failures + 1
  if failures == 0 then
    IO.println "✓ Exhaustive check passed: srlw == srlwJolt for all 8192 test pairs"
  else
    IO.println s!"✗ FAILED: {failures} mismatches found"
