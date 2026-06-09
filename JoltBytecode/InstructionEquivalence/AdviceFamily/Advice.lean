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
  bv_decide

theorem sshiftRight_slli_signExtend_16 (x : BitVec 16) :
    (x.setWidth 64 <<< 48).sshiftRight 48 = x.signExtend 64 := by
  bv_decide

theorem sshiftRight_slli_signExtend_32 (x : BitVec 32) :
    (x.setWidth 64 <<< 32).sshiftRight 32 = x.signExtend 64 := by
  bv_decide
