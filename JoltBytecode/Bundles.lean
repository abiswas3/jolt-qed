import JoltBytecode.Assumptions

/-!
# Jolt proof bundles

Bundles package primitive assumptions from `JoltBytecode.Assumptions`. They do
not introduce new primitive assumptions and contain no theorem declarations.
-/

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

-- ============================================================================
-- Execution bundles
-- ============================================================================

/-- Global execution configuration needed by the Sail/Jolt equivalence proofs.

This is a bundle of primitive register-state assumptions. Bare translation is a
derived theorem from this bundle, not an assumption. -/
structure JoltConfig (s : SailState) : Prop where
  cur_privilege : Assumptions.CurPrivilegeMachine s
  mstatus_mprv : Assumptions.MstatusMprvZero s

-- ============================================================================
-- Register/CSR-link bundles
-- ============================================================================

/-- Public assumptions for two-source instructions proved under
`System.systemProject`.

Every field is a primitive `Assumptions.*` predicate. -/
structure BinarySourceReadWithLinkedCSRs
    (rs2 rs1 : regidx) (js : SailJoltState) : Type where
  rs1_readable : Assumptions.XRegReadable rs1 js.sail
  rs2_readable : Assumptions.XRegReadable rs2 js.sail
  mstatus_matches : Assumptions.MstatusVRegMatchesSail js
  mtvec_matches : Assumptions.MtvecVRegMatchesSail js
  mscratch_matches : Assumptions.MscratchVRegMatchesSail js
  mepc_matches : Assumptions.MepcVRegMatchesSail js
  mcause_matches : Assumptions.McauseVRegMatchesSail js
  mtval_matches : Assumptions.MtvalVRegMatchesSail js

def BinarySourceReadWithLinkedCSRs.linkedCSRs
    {rs2 rs1 : regidx} {js : SailJoltState}
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    Assumptions.MstatusVRegMatchesSail js ∧
    Assumptions.MtvecVRegMatchesSail js ∧
    Assumptions.MscratchVRegMatchesSail js ∧
    Assumptions.MepcVRegMatchesSail js ∧
    Assumptions.McauseVRegMatchesSail js ∧
    Assumptions.MtvalVRegMatchesSail js :=
  ⟨h.mstatus_matches, h.mtvec_matches, h.mscratch_matches, h.mepc_matches,
    h.mcause_matches, h.mtval_matches⟩

noncomputable def BinarySourceReadWithLinkedCSRs.rs1_val
    {rs2 rs1 : regidx} {js : SailJoltState}
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : BitVec 64 :=
  Classical.choose h.rs1_readable.exists_value

theorem BinarySourceReadWithLinkedCSRs.rs1_read
    {rs2 rs1 : regidx} {js : SailJoltState}
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    rX_bits rs1 js.sail = .ok h.rs1_val js.sail :=
  Classical.choose_spec h.rs1_readable.exists_value

noncomputable def BinarySourceReadWithLinkedCSRs.rs2_val
    {rs2 rs1 : regidx} {js : SailJoltState}
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : BitVec 64 :=
  Classical.choose h.rs2_readable.exists_value

theorem BinarySourceReadWithLinkedCSRs.rs2_read
    {rs2 rs1 : regidx} {js : SailJoltState}
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    rX_bits rs2 js.sail = .ok h.rs2_val js.sail :=
  Classical.choose_spec h.rs2_readable.exists_value

/-- Public assumptions for one-source instructions proved under
`System.systemProject`.

Every field is a primitive `Assumptions.*` predicate. -/
structure UnarySourceReadWithLinkedCSRs
    (rs1 : regidx) (js : SailJoltState) : Type where
  rs1_readable : Assumptions.XRegReadable rs1 js.sail
  mstatus_matches : Assumptions.MstatusVRegMatchesSail js
  mtvec_matches : Assumptions.MtvecVRegMatchesSail js
  mscratch_matches : Assumptions.MscratchVRegMatchesSail js
  mepc_matches : Assumptions.MepcVRegMatchesSail js
  mcause_matches : Assumptions.McauseVRegMatchesSail js
  mtval_matches : Assumptions.MtvalVRegMatchesSail js

def UnarySourceReadWithLinkedCSRs.linkedCSRs
    {rs1 : regidx} {js : SailJoltState}
    (h : UnarySourceReadWithLinkedCSRs rs1 js) :
    Assumptions.MstatusVRegMatchesSail js ∧
    Assumptions.MtvecVRegMatchesSail js ∧
    Assumptions.MscratchVRegMatchesSail js ∧
    Assumptions.MepcVRegMatchesSail js ∧
    Assumptions.McauseVRegMatchesSail js ∧
    Assumptions.MtvalVRegMatchesSail js :=
  ⟨h.mstatus_matches, h.mtvec_matches, h.mscratch_matches, h.mepc_matches,
    h.mcause_matches, h.mtval_matches⟩

-- ============================================================================
-- Memory-window bundles
-- ============================================================================

/-- Primitive assumptions for one 8-byte readable dword window.

This is used by Jolt expansions that read an enclosing dword and then derive
smaller Sail reads from that window. -/
structure DwordReadWindowAssumptions (base : BitVec 64) (s : SailState) :
    Prop where
  bytes : Assumptions.DwordPresent base s
  load_pmp :
    ∀ offset accessWidth : Nat, offset + accessWidth ≤ 8 →
      Assumptions.LoadPmpOk (base + BitVec.ofNat 64 offset) accessWidth s
  not_readable_mmio :
    ∀ offset accessWidth : Nat, offset + accessWidth ≤ 8 →
      Assumptions.NotReadableMmio
        (base + BitVec.ofNat 64 offset) accessWidth s

/-- Primitive assumptions for one 8-byte dword window that Jolt both reads and
writes.

This is used by Jolt store-style expansions that load the enclosing dword,
splice a narrower value, and store the enclosing dword back. -/
structure DwordReadWriteWindowAssumptions (base : BitVec 64) (s : SailState) :
    Prop extends DwordReadWindowAssumptions base s where
  store_pmp :
    ∀ offset accessWidth : Nat, offset + accessWidth ≤ 8 →
      Assumptions.StorePmpOk (base + BitVec.ofNat 64 offset) accessWidth s
  not_writable_mmio :
    ∀ offset accessWidth : Nat, offset + accessWidth ≤ 8 →
      Assumptions.NotWritableMmio
        (base + BitVec.ofNat 64 offset) accessWidth s

/-- Primitive assumptions for one 8-byte AMO/Jolt memory window.

The `base` parameter is the important address: `.D` AMOs use the architectural
address, while `.W` AMOs use the enclosing aligned dword base. -/
structure AmoDwordWindowAssumptions
    (op : amoop) (base : BitVec 64) (s : SailState) :
    Prop extends DwordReadWriteWindowAssumptions base s where
  atomic_pmp :
    ∀ offset accessWidth : Nat, offset + accessWidth ≤ 8 →
      Assumptions.AtomicPmpOk op
        (base + BitVec.ofNat 64 offset) accessWidth s

end
