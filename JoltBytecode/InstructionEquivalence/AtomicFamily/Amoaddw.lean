import JoltBytecode.InstructionEquivalence.AtomicFamily.Common

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace AtomicFamily

theorem amoaddwProgram_eq_sail_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_mem : AmoMemoryAssumptions amoop.AMOADD 4
      (addr &&& (-8 : BitVec 64)) addr js.sail)
    (h_no_ovf : (addr &&& (-8 : BitVec 64)).toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoaddwProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOADD false false rs2 rs1 4 rd).run js.sail := by
  sorry

end AtomicFamily

end
