import JoltBytecode.InstructionEquivalence.AtomicFamily.Common

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace AtomicFamily

theorem amoordProgram_eq_sail_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_mem : AmoMemoryAssumptions amoop.AMOOR 8 addr addr js.sail)
    (h_no_ovf : addr.toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoordProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOOR false false rs2 rs1 8 rd).run js.sail := by
  sorry

end AtomicFamily

end
