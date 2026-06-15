import JoltBytecode.InstructionEquivalence.LoadFamily.Bundles
import JoltBytecode.InstructionEquivalence.LoadFamily.DwordArithmetic
import JoltBytecode.InstructionEquivalence.Memory.Derived

/-!
# Derived facts from load-family bundles

No primitive assumptions live here. These theorems unpack the shared load
bundle into the exact memory facts needed by each load width.
-/

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace LoadFamily
namespace LoadProgramEqSailAssumptions

theorem cfg
    {imm : BitVec 12} {rs1 : regidx} {js : SailJoltState}
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    JoltConfig js.sail :=
  { cur_privilege := h.cur_privilege
    mstatus_mprv := h.mstatus_mprv }

theorem dwordPhys
    {imm : BitVec 12} {rs1 : regidx} {js : SailJoltState}
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    FlatPhysMem (compute_aligned_dword_base_address h.rs1_val imm) 8 js.sail :=
  FlatPhysMem.ofReadWindow
    (compute_aligned_dword_base_address h.rs1_val imm) 8 js.sail
    h.dword_window.bytes h.dword_window.load_pmp
    h.dword_window.not_readable_mmio

/-- Derive an exact Sail read subaccess from the enclosing 8-byte Jolt read
window. The caller supplies the only width-specific fact: the requested access
fits inside the dword lane selected by the effective address. -/
theorem subaccessPhys
    {imm : BitVec 12} {rs1 : regidx} {js : SailJoltState}
    (h : LoadProgramEqSailAssumptions imm rs1 js) (accessWidth : Nat)
    (hfits :
      (load_effective_address h.rs1_val imm &&& (7 : BitVec 64)).toNat +
          accessWidth ≤ 8) :
    FlatPhysMem (load_effective_address h.rs1_val imm) accessWidth js.sail := by
  let ea := load_effective_address h.rs1_val imm
  let base := compute_aligned_dword_base_address h.rs1_val imm
  let offset := (ea &&& (7 : BitVec 64)).toNat
  have haddr : base + BitVec.ofNat 64 offset = ea := by
    simpa [base, ea, offset, compute_aligned_dword_base_address]
      using addr_split_aligned_offset ea
  have hbase_no_ovf : base.toNat + offset < 2 ^ 64 := by
    have hbase_align : base &&& (7 : BitVec 64) = 0 := by
      simpa [base, compute_aligned_dword_base_address, ea]
        using align_down_8_and_7_eq_zero ea
    have hbase_window : base.toNat + 7 < 2 ^ 64 :=
      aligned_addr_no_ovf_of_align base hbase_align
    have hoff_lt : offset < 8 := by
      simpa [offset, ea] using addr_and_seven_lt_eight ea
    omega
  have hphys :=
    FlatPhysMem.ofReadWindowSubaccess base 8 offset accessWidth js.sail
      (by simpa [base] using h.dword_window.bytes)
      (by simpa [base] using h.dword_window.load_pmp)
      (by simpa [base] using h.dword_window.not_readable_mmio)
      (by simpa [offset, ea] using hfits)
      hbase_no_ovf
  simpa [haddr] using hphys

theorem bytePhys
    {imm : BitVec 12} {rs1 : regidx} {js : SailJoltState}
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    FlatPhysMem (load_effective_address h.rs1_val imm) 1 js.sail := by
  refine h.subaccessPhys 1 ?_
  exact Nat.succ_le_of_lt
    (by simpa using addr_and_seven_lt_eight (load_effective_address h.rs1_val imm))

theorem halfwordPhys
    {imm : BitVec 12} {rs1 : regidx} {js : SailJoltState}
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (halign : load_effective_address h.rs1_val imm &&& (1 : BitVec 64) = 0) :
    FlatPhysMem (load_effective_address h.rs1_val imm) 2 js.sail := by
  refine h.subaccessPhys 2 ?_
  have hoff_cases :=
    halfword_offset_cases (load_effective_address h.rs1_val imm) halign
  omega

theorem wordPhys
    {imm : BitVec 12} {rs1 : regidx} {js : SailJoltState}
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (halign : load_effective_address h.rs1_val imm &&& (3 : BitVec 64) = 0) :
    FlatPhysMem (load_effective_address h.rs1_val imm) 4 js.sail := by
  refine h.subaccessPhys 4 ?_
  have hoff_cases :=
    word_offset_cases (load_effective_address h.rs1_val imm) halign
  omega

theorem halfwordNoOvf
    {imm : BitVec 12} {rs1 : regidx} {js : SailJoltState}
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (halign : load_effective_address h.rs1_val imm &&& (1 : BitVec 64) = 0) :
    (load_effective_address h.rs1_val imm).toNat + 1 < 2 ^ 64 :=
  aligned_halfword_addr_no_ovf (load_effective_address h.rs1_val imm) halign

theorem wordNoOvf
    {imm : BitVec 12} {rs1 : regidx} {js : SailJoltState}
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (halign : load_effective_address h.rs1_val imm &&& (3 : BitVec 64) = 0) :
    (load_effective_address h.rs1_val imm).toNat + 3 < 2 ^ 64 :=
  aligned_word_addr_no_ovf (load_effective_address h.rs1_val imm) halign

end LoadProgramEqSailAssumptions
end LoadFamily

end
