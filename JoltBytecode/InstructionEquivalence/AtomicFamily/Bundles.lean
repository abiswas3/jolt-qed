import JoltBytecode.InstructionEquivalence.LoadDefUtils

/-!
# Atomic-family public theorem bundles

This file contains only proof-facing bundles for AMO public theorems. Every
field is ultimately a primitive assumption from `JoltBytecode.Bundles`;
exact memory context is derived in `AtomicFamily.Derived`.

The family uses two bundles because `.D` and `.W` AMOs have different memory
shapes:

* `.D` AMOs use the architectural address as both the Jolt dword window and the
  native Sail atomic access.
* `.W` AMOs use the enclosing aligned dword on the Jolt side, while native Sail
  atomically accesses only the selected 4-byte word.
-/

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace AtomicFamily

/-- The enclosing dword used by `.W` AMO expansions.

This is intentionally repeated at the bundle layer so public theorem assumptions
do not need to import the large word-proof module just to name the memory
window. It is definitionally the same expression as `amoWordBase`. -/
abbrev amoWordAssumptionBase (addr : BitVec 64) : BitVec 64 :=
  addr &&& (-8 : BitVec 64)

/-- Register and configuration assumptions shared by every public AMO theorem.

This record intentionally contains no memory assumptions. The memory window is
separate because `.D` and `.W` AMOs use different dword bases. -/
structure AmoRegisterConfigAssumptions
    (rs2 rs1 rd : regidx) (js : SailJoltState) where
  rs1_val : BitVec 64
  rs2_val : BitVec 64
  rs1_read : rX_bits rs1 js.sail = .ok rs1_val js.sail
  rs2_read : rX_bits rs2 js.sail = .ok rs2_val js.sail
  rd_readable : Assumptions.XRegReadable rd js.sail
  cur_privilege : Assumptions.CurPrivilegeMachine js.sail
  mstatus_mprv : Assumptions.MstatusMprvZero js.sail

/-- Public assumptions for a dword AMO equivalence theorem.

The dword window is assumed once, as an 8-byte primitive window. Exact Jolt load
/ store evidence and exact native Sail atomic evidence are derived from these
fields; they are not additional assumptions. -/
structure AmoDwordProgramEqSailAssumptions
    (op : amoop) (rs2 rs1 rd : regidx) (js : SailJoltState)
    extends AmoRegisterConfigAssumptions rs2 rs1 rd js where
  dword_window : AmoDwordWindowAssumptions op rs1_val js.sail

/-- Public assumptions for a word AMO equivalence theorem.

The primitive memory window is the enclosing 8-byte dword at
`amoWordAssumptionBase rs1_val`. Native Sail's exact 4-byte atomic access is
derived from that same window in the aligned branch. -/
structure AmoWordProgramEqSailAssumptions
    (op : amoop) (rs2 rs1 rd : regidx) (js : SailJoltState)
    extends AmoRegisterConfigAssumptions rs2 rs1 rd js where
  dword_window :
    AmoDwordWindowAssumptions op (amoWordAssumptionBase rs1_val) js.sail

end AtomicFamily

end
