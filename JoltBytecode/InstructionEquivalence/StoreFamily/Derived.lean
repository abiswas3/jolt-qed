import JoltBytecode.InstructionEquivalence.StoreFamily.Bundles
import JoltBytecode.InstructionEquivalence.StoreFamily.MemoryPipeline
import JoltBytecode.InstructionEquivalence.Memory.Derived

/-!
# Derived facts from store-family bundles

No primitive assumptions live here. These theorems unpack the shared store
bundle into the exact read/write memory facts needed by the store proofs.
-/

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace StoreFamily
namespace StoreProgramEqSailAssumptions

theorem cfg
    {imm : BitVec 12} {rs2 rs1 : regidx} {js : SailJoltState}
    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js) :
    JoltConfig js.sail :=
  { cur_privilege := h.cur_privilege
    mstatus_mprv := h.mstatus_mprv }

theorem joltMem
    {imm : BitVec 12} {rs2 rs1 : regidx} {js : SailJoltState}
    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js) :
    FlatLoadStoreMem (compute_aligned_dword_base_address h.rs1_val imm) 8 js.sail :=
  FlatLoadStoreMem.ofReadWriteWindow
    (compute_aligned_dword_base_address h.rs1_val imm) 8 js.sail
    h.dword_window.bytes h.dword_window.load_pmp h.dword_window.store_pmp
    h.dword_window.not_readable_mmio h.dword_window.not_writable_mmio

/-- Derive an exact Sail write subaccess from the enclosing 8-byte writable
window. The caller supplies the width-specific fit proof. -/
theorem subaccessStore
    {imm : BitVec 12} {rs2 rs1 : regidx} {js : SailJoltState}
    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js) (accessWidth : Nat)
    (hfits :
      (load_effective_address h.rs1_val imm &&& (7 : BitVec 64)).toNat +
          accessWidth ≤ 8) :
    FlatStoreMem (load_effective_address h.rs1_val imm) accessWidth js.sail := by
  let ea := load_effective_address h.rs1_val imm
  let base := compute_aligned_dword_base_address h.rs1_val imm
  let offset := (ea &&& (7 : BitVec 64)).toNat
  have haddr : base + BitVec.ofNat 64 offset = ea := by
    simpa [base, ea, offset, compute_aligned_dword_base_address]
      using addr_split_aligned_offset ea
  have hstore :=
    FlatStoreMem.ofWriteWindowSubaccess base 8 offset accessWidth js.sail
      (by simpa [base] using h.dword_window.store_pmp)
      (by simpa [base] using h.dword_window.not_writable_mmio)
      (by simpa [offset, ea] using hfits)
  simpa [haddr] using hstore

theorem byteStore
    {imm : BitVec 12} {rs2 rs1 : regidx} {js : SailJoltState}
    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js) :
    FlatStoreMem (load_effective_address h.rs1_val imm) 1 js.sail := by
  refine h.subaccessStore 1 ?_
  exact Nat.succ_le_of_lt
    (by simpa using addr_and_seven_lt_eight (load_effective_address h.rs1_val imm))

theorem halfwordStore
    {imm : BitVec 12} {rs2 rs1 : regidx} {js : SailJoltState}
    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js)
    (halign : load_effective_address h.rs1_val imm &&& (1 : BitVec 64) = 0) :
    FlatStoreMem (load_effective_address h.rs1_val imm) 2 js.sail := by
  refine h.subaccessStore 2 ?_
  have hoff_cases :=
    halfword_offset_cases (load_effective_address h.rs1_val imm) halign
  omega

theorem wordStore
    {imm : BitVec 12} {rs2 rs1 : regidx} {js : SailJoltState}
    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js)
    (halign : load_effective_address h.rs1_val imm &&& (3 : BitVec 64) = 0) :
    FlatStoreMem (load_effective_address h.rs1_val imm) 4 js.sail := by
  refine h.subaccessStore 4 ?_
  have hoff_cases :=
    word_offset_cases (load_effective_address h.rs1_val imm) halign
  omega

theorem accessContext
    {imm : BitVec 12} {rs2 rs1 : regidx} {js : SailJoltState}
    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js) (width : Nat)
    (hstore : FlatStoreMem (load_effective_address h.rs1_val imm) width js.sail) :
    StoreMemoryContext
      (load_effective_address h.rs1_val imm)
      (compute_aligned_dword_base_address h.rs1_val imm) width js.sail :=
  { jolt_mem := h.joltMem
    sail_store_mem := hstore
    cfg := h.cfg }

end StoreProgramEqSailAssumptions
end StoreFamily

end
