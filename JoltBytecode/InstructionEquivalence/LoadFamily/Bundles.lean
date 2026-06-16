import JoltBytecode.InstructionEquivalence.LoadDefUtils

/-!
# Load-family public theorem bundles

This file contains only proof-facing bundles. The fields are primitive
assumptions, or bundles of primitive assumptions, from `JoltBytecode.Bundles`;
derived facts live in
`LoadFamily.Derived`.
-/

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace LoadFamily

/-- Register and configuration assumptions shared by every public load-family
equivalence theorem.

This record intentionally contains no memory assumptions. The memory window is
the enclosing dword read by Jolt's load expansion. -/
structure LoadRegisterConfigAssumptions (rs1 : regidx)
    (js : SailJoltState) where
  rs1_val : BitVec 64
  rs1_read : rX_bits rs1 js.sail = .ok rs1_val js.sail
  cur_privilege : Assumptions.CurPrivilegeMachine js.sail
  mstatus_mprv : Assumptions.MstatusMprvZero js.sail

/-- Shared public assumptions for Jolt load-family equivalence theorems.

All current load expansions (`LB/LBU/LH/LHU/LW/LWU`) read the enclosing
8-byte dword on the Jolt side. The exact Sail byte/halfword/word access is
derived from this window in `LoadFamily.Derived`; it is not repeated here. -/
structure LoadProgramEqSailAssumptions (imm : BitVec 12) (rs1 : regidx)
    (js : SailJoltState)
    extends LoadRegisterConfigAssumptions rs1 js where
  dword_window :
    DwordReadWindowAssumptions
      (compute_aligned_dword_base_address rs1_val imm) js.sail

end LoadFamily

end
