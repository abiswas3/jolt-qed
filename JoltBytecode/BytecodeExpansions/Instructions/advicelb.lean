import JoltBytecode.BytecodeExpansions.Common.Riscv

/-!
# ADVICELB: RISC-V ≡ Jolt Decomposition

## Instruction (Jolt virtual)

`ADVICELB` loads 1 byte from the advice tape and sign-extends to 64 bits.

## Jolt Decomposition (64-bit)

1. `VirtualAdviceLoad rd, 1` — zero-extends byte to 64 bits
2. `SLLI rd, rd, 56`
3. `SRAI rd, rd, 56`

## Proof

Shift-based sign extension (SLLI 56 + SRAI 56) equals `signExtend 64`
for an 8-bit value.
-/

-- ============================================================================
-- Sign-extension lemma
-- ============================================================================

lemma sshiftRight_slli_signExtend_8 (x : BitVec 8) :
    (x.setWidth 64 <<< 56).sshiftRight 56 = x.signExtend 64 := by
  bv_decide

-- ============================================================================
-- Definitions
-- ============================================================================

/-- Jolt decomposition of ADVICELB: VirtualAdviceLoad + SLLI 56 + SRAI 56. -/
def jolt_advicelb (rd : BitVec 5) (advice : BitVec 8) (s : State) : State :=
  let val := advice.setWidth 64
  let val := (val <<< 56).sshiftRight 56
  { s with reg := write rd val s.reg }

-- ============================================================================
-- Main theorem
-- ============================================================================

theorem advicelb_eq (rd : BitVec 5) (advice : BitVec 8) (s : State) :
    Riscv.advicelb rd advice s = jolt_advicelb rd advice s := by
  simp only [Riscv.advicelb, jolt_advicelb, sshiftRight_slli_signExtend_8]
