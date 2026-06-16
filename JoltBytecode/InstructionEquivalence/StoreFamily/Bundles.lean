import JoltBytecode.InstructionEquivalence.LoadDefUtils

/-!
# Store-family public theorem bundles

This file contains only proof-facing bundles. Every field is a primitive
assumption, or a bundle of primitive assumptions, from `JoltBytecode.Bundles`;
derived memory facts live in
`StoreFamily.Derived`.
-/

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace StoreFamily

/-- Register and configuration assumptions shared by every public store-family
equivalence theorem.

This record intentionally contains no memory assumptions. The memory window is
the enclosing dword read and written by Jolt's store expansion. -/
structure StoreRegisterConfigAssumptions
    (rs2 rs1 : regidx) (js : SailJoltState) where
  rs1_val : BitVec 64
  rs2_val : BitVec 64
  rs1_read : rX_bits rs1 js.sail = .ok rs1_val js.sail
  rs2_read : rX_bits rs2 js.sail = .ok rs2_val js.sail
  cur_privilege : Assumptions.CurPrivilegeMachine js.sail
  mstatus_mprv : Assumptions.MstatusMprvZero js.sail

/-- Shared public assumptions for Jolt store-family equivalence theorems.

Store expansions read the enclosing dword, splice in the source register's
low bytes, and write the enclosing dword back. Native Sail writes only the
instruction width; that exact write fact is derived from this 8-byte window. -/
structure StoreProgramEqSailAssumptions
    (imm : BitVec 12) (rs2 rs1 : regidx) (js : SailJoltState)
    extends StoreRegisterConfigAssumptions rs2 rs1 js where
  dword_window :
    DwordReadWriteWindowAssumptions
      (compute_aligned_dword_base_address rs1_val imm) js.sail

end StoreFamily

end
