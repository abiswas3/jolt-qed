import JoltBytecode.InstructionEquivalence.AtomicFamily.Bundles
import JoltBytecode.InstructionEquivalence.AtomicFamily.Common
import JoltBytecode.InstructionEquivalence.LoadFamily.DwordArithmetic
import JoltBytecode.InstructionEquivalence.Memory.Derived

/-!
# Derived facts from atomic-family bundles

No primitive assumptions live here. These theorems unpack the public AMO bundles
into the exact memory context consumed by the existing AMO proof pipeline.
-/

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace AtomicFamily

namespace AmoDwordProgramEqSailAssumptions

theorem cfg
    {op : amoop} {rs2 rs1 rd : regidx} {js : SailJoltState}
    (h : AmoDwordProgramEqSailAssumptions op rs2 rs1 rd js) :
    JoltConfig js.sail :=
  { cur_privilege := h.cur_privilege
    mstatus_mprv := h.mstatus_mprv }

theorem joltMem
    {op : amoop} {rs2 rs1 rd : regidx} {js : SailJoltState}
    (h : AmoDwordProgramEqSailAssumptions op rs2 rs1 rd js) :
    FlatLoadStoreMem h.rs1_val 8 js.sail :=
  FlatLoadStoreMem.ofReadWriteWindow h.rs1_val 8 js.sail
    (Assumptions.DwordPresent.memBytesPresent h.dword_window.bytes)
    h.dword_window.load_pmp h.dword_window.store_pmp
    h.dword_window.not_readable_mmio h.dword_window.not_writable_mmio

theorem sailAtomicMem
    {op : amoop} {rs2 rs1 rd : regidx} {js : SailJoltState}
    (h : AmoDwordProgramEqSailAssumptions op rs2 rs1 rd js) :
    FlatAtomicMem op h.rs1_val 8 js.sail :=
  FlatAtomicMem.ofAtomicWindow op h.rs1_val 8 js.sail
    (Assumptions.DwordPresent.memBytesPresent h.dword_window.bytes)
    h.dword_window.atomic_pmp
    h.dword_window.not_readable_mmio h.dword_window.not_writable_mmio

/-- Derive the internal AMO dword memory context from the public primitive
bundle. -/
theorem memoryContext
    {op : amoop} {rs2 rs1 rd : regidx} {js : SailJoltState}
    (h : AmoDwordProgramEqSailAssumptions op rs2 rs1 rd js) :
    AmoMemoryContext op 8 h.rs1_val h.rs1_val js.sail :=
  { jolt_mem := h.joltMem
    sail_atomic_mem := h.sailAtomicMem
    cfg := h.cfg }

end AmoDwordProgramEqSailAssumptions

namespace AmoWordProgramEqSailAssumptions

theorem cfg
    {op : amoop} {rs2 rs1 rd : regidx} {js : SailJoltState}
    (h : AmoWordProgramEqSailAssumptions op rs2 rs1 rd js) :
    JoltConfig js.sail :=
  { cur_privilege := h.cur_privilege
    mstatus_mprv := h.mstatus_mprv }

theorem joltMem
    {op : amoop} {rs2 rs1 rd : regidx} {js : SailJoltState}
    (h : AmoWordProgramEqSailAssumptions op rs2 rs1 rd js) :
    FlatLoadStoreMem (amoWordAssumptionBase h.rs1_val) 8 js.sail :=
  FlatLoadStoreMem.ofReadWriteWindow
    (amoWordAssumptionBase h.rs1_val) 8 js.sail
    (Assumptions.DwordPresent.memBytesPresent h.dword_window.bytes)
    h.dword_window.load_pmp h.dword_window.store_pmp
    h.dword_window.not_readable_mmio h.dword_window.not_writable_mmio

theorem sailAtomicMem
    {op : amoop} {rs2 rs1 rd : regidx} {js : SailJoltState}
    (h : AmoWordProgramEqSailAssumptions op rs2 rs1 rd js)
    (halign : h.rs1_val &&& (3 : BitVec 64) = 0) :
    FlatAtomicMem op h.rs1_val 4 js.sail := by
  let base := amoWordAssumptionBase h.rs1_val
  let offset := (h.rs1_val &&& (7 : BitVec 64)).toNat
  have haddr : base + BitVec.ofNat 64 offset = h.rs1_val := by
    simpa [base, offset, amoWordAssumptionBase]
      using addr_split_aligned_offset h.rs1_val
  have hfits : offset + 4 ≤ 8 := by
    have hoff_cases := word_offset_cases h.rs1_val halign
    omega
  have hbase_no_ovf : base.toNat + offset < 2 ^ 64 := by
    have hbase_align : base &&& (7 : BitVec 64) = 0 := by
      simpa [base, amoWordAssumptionBase]
        using align_down_8_and_7_eq_zero h.rs1_val
    have hbase_window : base.toNat + 7 < 2 ^ 64 :=
      aligned_addr_no_ovf_of_align base hbase_align
    have hoff_lt : offset < 8 := by
      simpa [offset] using addr_and_seven_lt_eight h.rs1_val
    omega
  have hmem :=
    FlatAtomicMem.ofAtomicWindowSubaccess op base 8 offset 4 js.sail
      (by simpa [base] using Assumptions.DwordPresent.memBytesPresent h.dword_window.bytes)
      (by simpa [base] using h.dword_window.atomic_pmp)
      (by simpa [base] using h.dword_window.not_readable_mmio)
      (by simpa [base] using h.dword_window.not_writable_mmio)
      hfits hbase_no_ovf
  simpa [haddr] using hmem

/-- Derive the internal AMO word memory context from the public primitive
bundle. This is only needed in the aligned branch; misaligned AMO.W proofs stop
before any memory access. -/
theorem memoryContext
    {op : amoop} {rs2 rs1 rd : regidx} {js : SailJoltState}
    (h : AmoWordProgramEqSailAssumptions op rs2 rs1 rd js)
    (halign : h.rs1_val &&& (3 : BitVec 64) = 0) :
    AmoMemoryContext op 4 (amoWordAssumptionBase h.rs1_val) h.rs1_val js.sail :=
  { jolt_mem := h.joltMem
    sail_atomic_mem := h.sailAtomicMem halign
    cfg := h.cfg }

end AmoWordProgramEqSailAssumptions

end AtomicFamily

end
