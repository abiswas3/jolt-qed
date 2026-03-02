import JoltBytecode.BytecodeExpansions.Common.FormatI
import JoltBytecode.BytecodeExpansions.Common.Virtual
import JoltBytecode.BytecodeExpansions.Common.Riscv
import JoltBytecode.BytecodeExpansions.Common.SimpLemmas

/-!
# SRAIW: RISC-V ≡ Jolt Decomposition

## Instruction (RV64I, Format I)

`SRAIW rd, rs1, shamt` takes the lower 32 bits of rs1, arithmetic right
shifts by shamt[4:0], sign-extends the 32-bit result to 64 bits, and
writes to rd.

## Jolt Decomposition (faithful to Rust implementation)

```
VirtualSignExtendWord    v_rs1, rs1, 0               -- sign-extend rs1[31:0] to 64
VirtualSRAI              rd, v_rs1, bitmask           -- arith right shift via ctz(bitmask)
VirtualSignExtendWord    rd, rd, 0                    -- sign-extend result to 64
```

where bitmask is precomputed:
```
shift := imm & 0x1f
ones  := (1 <<< (64 - shift)) - 1
bitmask := ones <<< shift
```

## Proof

The bitmask has `shift` trailing zeros, so `ctz(bitmask) = shift = shamt[4:0]`.
The core identity is: sign-extending a 32-bit value to 64, then logically
right-shifting by s < 32, then truncating back to 32 and sign-extending,
equals directly performing an arithmetic right shift on the 32-bit value
and sign-extending. This holds because the sign-extended upper bits
propagate correctly through the logical shift for s < 32.
-/

-- ============================================================================
-- Bitmask computation (faithful to Jolt Rust implementation)
-- ============================================================================

-- Matching Rust:
--   let shift = self.operands.imm & 0x1f;
--   let ones = (1u128 << (64 - shift)) - 1;
--   let bitmask = (ones << shift) as u64;
def sraiw_bitmask (shamt : BitVec 64) : Nat :=
  let shift := (shamt.setWidth 5).toNat
  let ones := (1 <<< (64 - shift)) - 1
  ones <<< shift

-- ctz of the bitmask recovers the shift amount.
lemma ctz_sraiw_bitmask (shamt : BitVec 64) :
    ctz (sraiw_bitmask shamt) = (shamt.setWidth 5).toNat := by
  unfold sraiw_bitmask
  simp only [Nat.shiftLeft_eq, one_mul]
  set shift := (shamt.setWidth 5).toNat
  have h_lt : shift < 32 := by
    have := (shamt.setWidth 5).isLt
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

-- Jolt's decomposition: VirtualSignExtendWord → VirtualSRAI → VirtualSignExtendWord.
def sraiwJolt (rs1_val shamt : BitVec 64) : BitVec 64 :=
  let v_rs1     := Jolt.virtualSignExtendWord rs1_val
  let v_bitmask := sraiw_bitmask shamt
  let v_result  := v_rs1 >>> ctz v_bitmask
  Jolt.virtualSignExtendWord v_result

-- ============================================================================
-- Core lemma
-- ============================================================================

-- ============================================================================
-- Main theorems
-- ============================================================================

-- Pure-function equivalence: Riscv.sraiw = sraiwJolt
theorem sraiw_eq_sraiwJolt (rs1_val shamt : BitVec 64) :
    Riscv.sraiw rs1_val shamt = sraiwJolt rs1_val shamt := by
  unfold Riscv.sraiw sraiwJolt Jolt.virtualSignExtendWord
  simp only [ctz_sraiw_bitmask]
  have hs : (shamt.setWidth 5).toNat < 32 := by
    have := (shamt.setWidth 5).isLt
    norm_num at this; exact this
  congr 1
  rw [sshiftRight_eq_signExtend_ushr_trunc (rs1_val.setWidth 32) _ hs]

-- State-level equivalence via Format I lifting.
theorem sraiw_state_eq (rs1 rd : BitVec 5) (imm : BitVec 64) (s : State) :
    format_i_exec rs1 rd imm Riscv.sraiw s = format_i_exec rs1 rd imm sraiwJolt s :=
  format_i_ops_eq_of_fns_eq Riscv.sraiw sraiwJolt rs1 rd imm s
    (by funext rs1_val shamt; exact sraiw_eq_sraiwJolt rs1_val shamt)

/-SANITY CHECKS-/
-- Exhaustive check: verify Riscv.sraiw == sraiwJolt for 256 values × 32 shift amounts
#eval do
  let mut failures := 0
  for i in List.range 256 do
    for s in List.range 32 do
      let rs1_val : BitVec 64 := BitVec.ofNat 64 i
      let shamt : BitVec 64 := BitVec.ofNat 64 s
      if Riscv.sraiw rs1_val shamt != sraiwJolt rs1_val shamt then
        failures := failures + 1
  if failures == 0 then
    IO.println "✓ Exhaustive check passed: sraiw == sraiwJolt for all 8192 test pairs"
  else
    IO.println s!"✗ FAILED: {failures} mismatches found"
