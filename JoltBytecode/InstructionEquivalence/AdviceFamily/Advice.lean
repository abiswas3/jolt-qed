import JoltBytecode.JoltISA.Environment


open Sail PreSail LeanRV64D.Functions

/-!
# Advice-Family Bit-Vector Helpers

Advice-load source instructions are proved through `JoltISA.Program`
expansions in the instruction-specific files. This module only keeps the shared
bit-vector facts needed to identify the final shifted value with Sail's
sign-extension result.
-/

theorem sshiftRight_slli_signExtend_8 (x : BitVec 8) :
    (x.setWidth 64 <<< 56).sshiftRight 56 = x.signExtend 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_signExtend]
  by_cases hlt : i < 8
  · have hsi : 56 + i < 64 := by omega
    simp [hi, hlt, hsi, BitVec.getElem_setWidth]
    have hnot_hi : ¬ 64 ≤ i := by omega
    have hnot_underflow : ¬ 56 + i < 56 := by omega
    simp [hnot_hi, hnot_underflow]
  · have hnlt : ¬ 56 + i < 64 := by omega
    simp [hi, hlt, hnlt, BitVec.msb_eq_getLsbD_last,
      BitVec.getElem_setWidth]

theorem sshiftRight_slli_signExtend_16 (x : BitVec 16) :
    (x.setWidth 64 <<< 48).sshiftRight 48 = x.signExtend 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_signExtend]
  by_cases hlt : i < 16
  · have hsi : 48 + i < 64 := by omega
    simp [hi, hlt, hsi, BitVec.getElem_setWidth]
    have hnot_hi : ¬ 64 ≤ i := by omega
    have hnot_underflow : ¬ 48 + i < 48 := by omega
    simp [hnot_hi, hnot_underflow]
  · have hnlt : ¬ 48 + i < 64 := by omega
    simp [hi, hlt, hnlt, BitVec.msb_eq_getLsbD_last,
      BitVec.getElem_setWidth]

theorem sshiftRight_slli_signExtend_32 (x : BitVec 32) :
    (x.setWidth 64 <<< 32).sshiftRight 32 = x.signExtend 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_signExtend]
  by_cases hlt : i < 32
  · have hsi : 32 + i < 64 := by omega
    simp [hi, hlt, hsi, BitVec.getElem_setWidth]
    have hnot_hi : ¬ 64 ≤ i := by omega
    have hnot_underflow : ¬ 32 + i < 32 := by omega
    simp [hnot_hi, hnot_underflow]
  · have hnlt : ¬ 32 + i < 64 := by omega
    simp [hi, hlt, hnlt, BitVec.msb_eq_getLsbD_last,
      BitVec.getElem_setWidth]
