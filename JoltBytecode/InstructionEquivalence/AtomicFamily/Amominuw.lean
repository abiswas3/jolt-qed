import JoltBytecode.InstructionEquivalence.AtomicFamily.WordSelectRust

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace AtomicFamily

/-- Canonical Sail state after aligned `AMOMINU.W`. -/
abbrev amominuwFinalSailState
    (rd : regidx) (s : SailState) (addr rs2Val : BitVec 64) : SailState :=
  amoWordFinalSailState rd s addr
    (if (zopz0zI_u
        (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
        (loaded_word_at s addr) : Bool) then
      (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
    else
      loaded_word_at s addr)

/-- Sail's generated `AMOMINU.W` result expression reduces to unsigned word min. -/
theorem amominuw_sail_result (rs2Val : BitVec 64) (loaded : BitVec 32) :
    amoWordSailResult amoop.AMOMINU
      (show BitVec (4 * 8) from
        trunc (m := (((4 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
      (BitVec.setWidth (4 * 8) loaded) =
    if (zopz0zI_u
        (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
        loaded : Bool) then
      (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
    else
      loaded := by
  rw [amo_word_trunc_4x8_eq_extract]
  rw [amo_word_setWidth_4x8_eq_self]

/-- Jolt-side aligned concrete execution for `AMOMINU.W`. -/
theorem amominuwProgram_concrete_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_mem : AmoMemoryAssumptions amoop.AMOMINU 4
      (amoWordBase addr) addr js.sail)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    ∃ jsf : SailJoltState,
      (JoltISA.execProgram (JoltISA.amominuwProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail = amominuwFinalSailState rd js.sail addr rs2Val := by
  change
    ∃ jsf : SailJoltState,
      (JoltISA.execProgram
        (JoltISA.amoWordSelectRustProgram
          (fun dst src => .VirtualZeroExtendWord dst src)
          (fun dst lhs rhs => .SLTU dst lhs rhs)
          (.vreg JoltISA.amoWordSelectNewVReg) (.vreg JoltISA.amoWordSelectMaskVReg)
          rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail = amominuwFinalSailState rd js.sail addr rs2Val
  exact
    amo_word_rust_select_program_concrete_aligned
      amoop.AMOMINU
      (fun dst src => .VirtualZeroExtendWord dst src)
      (fun dst lhs rhs => .SLTU dst lhs rhs)
      (.vreg JoltISA.amoWordSelectNewVReg) (.vreg JoltISA.amoWordSelectMaskVReg)
      rs2 rs1 rd js hcfg addr
      (if (zopz0zI_u
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
          (Sail.BitVec.extractLsb
            (amoWordShiftedOld js.sail addr) 31 0 : BitVec 32) : Bool) then
        rs2Val
      else
        amoWordShiftedOld js.sail addr)
      (if (zopz0zI_u
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
          (loaded_word_at js.sail addr) : Bool) then
        (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
      else
        loaded_word_at js.sail addr)
      hrs1 h_mem h_align
      (amo_word_minu_result_extract_eq js.sail addr rs2Val h_align)
      (amo_word_rust_select_minu_middle_after_pre rs2 js addr rs2Val hrs2)

/-- Sail-side aligned concrete execution for native `AMOMINU.W`. -/
theorem execute_AMOMINUW_reduces_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryAssumptions amoop.AMOMINU 4
      (amoWordBase addr) addr js.sail)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    (execute_AMO amoop.AMOMINU false false rs2 rs1 4 rd).run js.sail =
      .ok RETIRE_SUCCESS (amominuwFinalSailState rd js.sail addr rs2Val) := by
  exact
    execute_AMO_word_non_cas_aligned
      amoop.AMOMINU rs2 rs1 rd js hcfg addr rs2Val
      (if (zopz0zI_u
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
          (loaded_word_at js.sail addr) : Bool) then
        (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
      else
        loaded_word_at js.sail addr)
      hrs1 hrs2 hrd h_mem h_align
      (by decide)
      (amominuw_sail_result rs2Val (loaded_word_at js.sail addr))

/-- Aligned public branch for `AMOMINU.W`. -/
theorem amominuwProgram_eq_sail_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryAssumptions amoop.AMOMINU 4
      (amoWordBase addr) addr js.sail)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amominuwProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOMINU false false rs2 rs1 4 rd).run js.sail := by
  change
    projectResult ((JoltISA.execProgram
      (JoltISA.amoWordSelectRustProgram
        (fun dst src => .VirtualZeroExtendWord dst src)
        (fun dst lhs rhs => .SLTU dst lhs rhs)
        (.vreg JoltISA.amoWordSelectNewVReg) (.vreg JoltISA.amoWordSelectMaskVReg)
        rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOMINU false false rs2 rs1 4 rd).run js.sail
  exact
    amo_word_rust_select_program_eq_sail_aligned
      amoop.AMOMINU
      (fun dst src => .VirtualZeroExtendWord dst src)
      (fun dst lhs rhs => .SLTU dst lhs rhs)
      (.vreg JoltISA.amoWordSelectNewVReg) (.vreg JoltISA.amoWordSelectMaskVReg)
      rs2 rs1 rd js hcfg addr rs2Val
      (if (zopz0zI_u
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
          (Sail.BitVec.extractLsb
            (amoWordShiftedOld js.sail addr) 31 0 : BitVec 32) : Bool) then
        rs2Val
      else
        amoWordShiftedOld js.sail addr)
      (if (zopz0zI_u
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
          (loaded_word_at js.sail addr) : Bool) then
        (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
      else
        loaded_word_at js.sail addr)
      hrs1 hrs2 hrd h_mem h_align
      (by decide)
      (amo_word_minu_result_extract_eq js.sail addr rs2Val h_align)
      (amo_word_rust_select_minu_middle_after_pre rs2 js addr rs2Val hrs2)
      (amominuw_sail_result rs2Val (loaded_word_at js.sail addr))

/-- Main public theorem for `AMOMINU.W`. -/
theorem amominuwProgram_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryAssumptions amoop.AMOMINU 4
      (amoWordBase addr) addr js.sail) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amominuwProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOMINU false false rs2 rs1 4 rd).run js.sail := by
  change
    projectResult ((JoltISA.execProgram
      (JoltISA.amoWordSelectRustProgram
        (fun dst src => .VirtualZeroExtendWord dst src)
        (fun dst lhs rhs => .SLTU dst lhs rhs)
        (.vreg JoltISA.amoWordSelectNewVReg) (.vreg JoltISA.amoWordSelectMaskVReg)
        rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOMINU false false rs2 rs1 4 rd).run js.sail
  exact
    amo_word_rust_select_program_eq_sail
      amoop.AMOMINU
      (fun dst src => .VirtualZeroExtendWord dst src)
      (fun dst lhs rhs => .SLTU dst lhs rhs)
      (.vreg JoltISA.amoWordSelectNewVReg) (.vreg JoltISA.amoWordSelectMaskVReg)
      rs2 rs1 rd js hcfg addr rs2Val
      (if (zopz0zI_u
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
          (Sail.BitVec.extractLsb
            (amoWordShiftedOld js.sail addr) 31 0 : BitVec 32) : Bool) then
        rs2Val
      else
        amoWordShiftedOld js.sail addr)
      (if (zopz0zI_u
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
          (loaded_word_at js.sail addr) : Bool) then
        (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
      else
        loaded_word_at js.sail addr)
      hrs1 hrs2 hrd h_mem
      (by decide)
      (fun h_align => amo_word_minu_result_extract_eq js.sail addr rs2Val h_align)
      (amo_word_rust_select_minu_middle_after_pre rs2 js addr rs2Val hrs2)
      (amominuw_sail_result rs2Val (loaded_word_at js.sail addr))

end AtomicFamily

end
