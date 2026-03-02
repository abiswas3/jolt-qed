-- TODO: prove sll_32_eq_mul_trunc (32-bit shift = multiply truncated)
import JoltBytecode.BytecodeExpansions.Common.FormatR
import JoltBytecode.BytecodeExpansions.Common.Virtual
import JoltBytecode.BytecodeExpansions.Common.Riscv

/-!
# SLLW: RISC-V ≡ Jolt Decomposition

## Instruction (RV64I, Format R)

`SLLW rd, rs1, rs2` takes the lower 32 bits of rs1, left-shifts by
rs2[4:0], sign-extends the 32-bit result to 64 bits, and writes to rd.

## Jolt Decomposition (faithful to Rust implementation)

```
VirtualPow2W             v_pow, rs2, 0                -- v_pow = 2^(rs2[4:0])
MUL                      rd, rs1, v_pow               -- rd = rs1 * 2^(rs2[4:0])
VirtualSignExtendWord    rd, rd, 0                    -- sign-extend lower 32 bits
```

## Proof

Left-shifting by s is equivalent to multiplying by 2^s. The 64-bit
multiplication truncated to 32 bits equals the direct 32-bit left shift,
because modular multiplication commutes with truncation:
  (x % 2^32) * 2^s % 2^32 = x * 2^s % 2^32.
Sign-extension of the 32-bit result completes the equivalence.
-/

-- ============================================================================
-- Jolt decomposition
-- ============================================================================

-- Jolt's decomposition: VirtualPow2W → MUL → VirtualSignExtendWord.
def sllwJolt (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  let v_pow := Jolt.virtualPow2W rs2_val
  let product := Riscv.mul rs1_val v_pow
  Jolt.virtualSignExtendWord product

-- ============================================================================
-- Core lemma
-- ============================================================================

-- 32-bit left shift equals 64-bit multiply by 2^s, truncated to 32 bits.
private lemma sll_32_eq_mul_trunc (x : BitVec 64) (s : Nat) (hs : s < 32) :
    x.setWidth 32 <<< s = (x * BitVec.ofNat 64 (2 ^ s)).setWidth 32 := by
  sorry

-- ============================================================================
-- Main theorems
-- ============================================================================

-- Pure-function equivalence: Riscv.sllw = sllwJolt
theorem sllw_eq_sllwJolt (rs1_val rs2_val : BitVec 64) :
    Riscv.sllw rs1_val rs2_val = sllwJolt rs1_val rs2_val := by
  unfold Riscv.sllw sllwJolt Jolt.virtualPow2W Riscv.mul Jolt.virtualSignExtendWord
  congr 1
  exact sll_32_eq_mul_trunc rs1_val (rs2_val.setWidth 5).toNat (by
    have := (rs2_val.setWidth 5).isLt; norm_num at this; exact this)

-- State-level equivalence via Format R lifting.
theorem sllw_state_eq (rs1 rs2 rd : BitVec 5) (s : State) :
    format_r_exec rs1 rs2 rd Riscv.sllw s = format_r_exec rs1 rs2 rd sllwJolt s :=
  format_r_ops_eq_of_fns_eq Riscv.sllw sllwJolt rs1 rs2 rd s
    (by funext rs1_val rs2_val; exact sllw_eq_sllwJolt rs1_val rs2_val)

/-SANITY CHECKS-/
#eval do
  let mut failures := 0
  for i in List.range 256 do
    for s in List.range 32 do
      let rs1_val : BitVec 64 := BitVec.ofNat 64 i
      let rs2_val : BitVec 64 := BitVec.ofNat 64 s
      if Riscv.sllw rs1_val rs2_val != sllwJolt rs1_val rs2_val then
        failures := failures + 1
  if failures == 0 then
    IO.println "✓ Exhaustive check passed: sllw == sllwJolt for all 8192 test pairs"
  else
    IO.println s!"✗ FAILED: {failures} mismatches found"
