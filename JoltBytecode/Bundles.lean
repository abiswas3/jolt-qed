import JoltBytecode.Assumptions
import JoltBytecode.Memory

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
-- ALU-family bundles
-- ============================================================================

namespace ALUFamily

/-- Public assumptions for one-source ALU instructions.

This bundles exactly one source-register read: `rs1` has value `rs1_val` in the
initial Sail state. -/
structure UnarySourceReadAssumptions (rs1 : regidx) (js : SailJoltState) where
  rs1_val : BitVec 64
  rs1_read : rX_bits rs1 js.sail = .ok rs1_val js.sail

/-- Public assumptions for two-source ALU instructions.

This bundles exactly the two source-register reads: `rs1` and `rs2` have the
recorded values in the initial Sail state. -/
structure BinarySourceReadAssumptions
    (rs2 rs1 : regidx) (js : SailJoltState) where
  rs1_val : BitVec 64
  rs2_val : BitVec 64
  rs1_read : rX_bits rs1 js.sail = .ok rs1_val js.sail
  rs2_read : rX_bits rs2 js.sail = .ok rs2_val js.sail

end ALUFamily

-- ============================================================================
-- Register/CSR-link bundles
-- ============================================================================

/-- Public assumptions for two-source instructions proved under
`System.systemProject`.

Source-register reads carry named values and concrete read facts. The remaining
fields are primitive CSR-link assumptions. -/
structure BinarySourceReadWithLinkedCSRs
    (rs2 rs1 : regidx) (js : SailJoltState) : Type where
  rs1_val : BitVec 64
  rs2_val : BitVec 64
  rs1_read : rX_bits rs1 js.sail = .ok rs1_val js.sail
  rs2_read : rX_bits rs2 js.sail = .ok rs2_val js.sail
  mstatus_matches : Assumptions.MstatusVRegMatchesSail js
  mtvec_matches : Assumptions.MtvecVRegMatchesSail js
  mscratch_matches : Assumptions.MscratchVRegMatchesSail js
  mepc_matches : Assumptions.MepcVRegMatchesSail js
  mcause_matches : Assumptions.McauseVRegMatchesSail js
  mtval_matches : Assumptions.MtvalVRegMatchesSail js

-- Just filter down the above structure for the linked CSR's
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

/-- Public assumptions for one-source instructions proved under
`System.systemProject`.

Source-register reads carry named values and concrete read facts. The remaining
fields are primitive CSR-link assumptions. -/
structure UnarySourceReadWithLinkedCSRs
    (rs1 : regidx) (js : SailJoltState) : Type where
  rs1_val : BitVec 64
  rs1_read : rX_bits rs1 js.sail = .ok rs1_val js.sail
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
-- Load-family bundles
-- ============================================================================

namespace LoadFamily

/-- Shared public assumptions for Jolt load-family equivalence theorems.

All current load expansions (`LB/LBU/LH/LHU/LW/LWU`) read the enclosing
8-byte dword on the Jolt side. The exact Sail byte/halfword/word access is
derived directly from this window in the instruction proofs; it is not repeated
here. -/
structure LoadProgramEqSailAssumptions (imm : BitVec 12) (rs1 : regidx)
    (js : SailJoltState)
    extends UnarySourceReadWithLinkedCSRs rs1 js where
  cur_privilege : Assumptions.CurPrivilegeMachine js.sail
  mstatus_mprv : Assumptions.MstatusMprvZero js.sail
  dword_present :
    Assumptions.DwordPresent
      (compute_aligned_dword_base_address rs1_val imm) js.sail
  load_pmp :
    Assumptions.LoadPmpOkWindow
      (compute_aligned_dword_base_address rs1_val imm) 8 js.sail
  not_readable_mmio :
    Assumptions.NotReadableMmioWindow
      (compute_aligned_dword_base_address rs1_val imm) 8 js.sail

def LoadProgramEqSailAssumptions.linkedCSRs
    {imm : BitVec 12} {rs1 : regidx} {js : SailJoltState}
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    Assumptions.MstatusVRegMatchesSail js ∧
    Assumptions.MtvecVRegMatchesSail js ∧
    Assumptions.MscratchVRegMatchesSail js ∧
    Assumptions.MepcVRegMatchesSail js ∧
    Assumptions.McauseVRegMatchesSail js ∧
    Assumptions.MtvalVRegMatchesSail js :=
  ⟨h.mstatus_matches, h.mtvec_matches, h.mscratch_matches, h.mepc_matches,
    h.mcause_matches, h.mtval_matches⟩

end LoadFamily

-- ============================================================================
-- Store-family bundles
-- ============================================================================

namespace StoreFamily

/-- Shared public assumptions for Jolt store-family equivalence theorems.

Store expansions read the enclosing dword, splice in the source register's
low bytes, and write the enclosing dword back. Native Sail writes only the
instruction width; that exact write fact is derived from this 8-byte window. -/
structure StoreProgramEqSailAssumptions
    (imm : BitVec 12) (rs2 rs1 : regidx) (js : SailJoltState)
    extends BinarySourceReadWithLinkedCSRs rs2 rs1 js where
  cur_privilege : Assumptions.CurPrivilegeMachine js.sail
  mstatus_mprv : Assumptions.MstatusMprvZero js.sail
  dword_present :
    Assumptions.DwordPresent
      (compute_aligned_dword_base_address rs1_val imm) js.sail
  load_pmp :
    Assumptions.LoadPmpOkWindow
      (compute_aligned_dword_base_address rs1_val imm) 8 js.sail
  not_readable_mmio :
    Assumptions.NotReadableMmioWindow
      (compute_aligned_dword_base_address rs1_val imm) 8 js.sail
  store_pmp :
    Assumptions.StorePmpOkWindow
      (compute_aligned_dword_base_address rs1_val imm) 8 js.sail
  not_writable_mmio :
    Assumptions.NotWritableMmioWindow
      (compute_aligned_dword_base_address rs1_val imm) 8 js.sail

def StoreProgramEqSailAssumptions.linkedCSRs
    {imm : BitVec 12} {rs2 rs1 : regidx} {js : SailJoltState}
    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js) :
    Assumptions.MstatusVRegMatchesSail js ∧
    Assumptions.MtvecVRegMatchesSail js ∧
    Assumptions.MscratchVRegMatchesSail js ∧
    Assumptions.MepcVRegMatchesSail js ∧
    Assumptions.McauseVRegMatchesSail js ∧
    Assumptions.MtvalVRegMatchesSail js :=
  ⟨h.mstatus_matches, h.mtvec_matches, h.mscratch_matches, h.mepc_matches,
    h.mcause_matches, h.mtval_matches⟩

end StoreFamily

-- ============================================================================
-- Atomic-family bundles
-- ============================================================================

namespace AtomicFamily

/-- The enclosing dword used by `.W` AMO expansions. -/
abbrev amoWordAssumptionBase (addr : BitVec 64) : BitVec 64 :=
  addr &&& (-8 : BitVec 64)

/-- Public assumptions for a dword AMO equivalence theorem. -/
structure AmoDwordProgramEqSailAssumptions
    (op : amoop) (rs2 rs1 rd : regidx) (js : SailJoltState)
    extends ALUFamily.BinarySourceReadAssumptions rs2 rs1 js where
  rd_readable : Assumptions.XRegReadable rd js.sail
  cur_privilege : Assumptions.CurPrivilegeMachine js.sail
  mstatus_mprv : Assumptions.MstatusMprvZero js.sail
  dword_present : Assumptions.DwordPresent rs1_val js.sail
  load_pmp : Assumptions.LoadPmpOkWindow rs1_val 8 js.sail
  not_readable_mmio : Assumptions.NotReadableMmioWindow rs1_val 8 js.sail
  store_pmp : Assumptions.StorePmpOkWindow rs1_val 8 js.sail
  not_writable_mmio : Assumptions.NotWritableMmioWindow rs1_val 8 js.sail
  atomic_pmp : Assumptions.AtomicPmpOkWindow op rs1_val 8 js.sail

/-- Public assumptions for a word AMO equivalence theorem. -/
structure AmoWordProgramEqSailAssumptions
    (op : amoop) (rs2 rs1 rd : regidx) (js : SailJoltState)
    extends ALUFamily.BinarySourceReadAssumptions rs2 rs1 js where
  rd_readable : Assumptions.XRegReadable rd js.sail
  cur_privilege : Assumptions.CurPrivilegeMachine js.sail
  mstatus_mprv : Assumptions.MstatusMprvZero js.sail
  dword_present :
    Assumptions.DwordPresent (amoWordAssumptionBase rs1_val) js.sail
  load_pmp :
    Assumptions.LoadPmpOkWindow (amoWordAssumptionBase rs1_val) 8 js.sail
  not_readable_mmio :
    Assumptions.NotReadableMmioWindow (amoWordAssumptionBase rs1_val) 8 js.sail
  store_pmp :
    Assumptions.StorePmpOkWindow (amoWordAssumptionBase rs1_val) 8 js.sail
  not_writable_mmio :
    Assumptions.NotWritableMmioWindow (amoWordAssumptionBase rs1_val) 8 js.sail
  atomic_pmp :
    Assumptions.AtomicPmpOkWindow op (amoWordAssumptionBase rs1_val) 8 js.sail

end AtomicFamily

end
