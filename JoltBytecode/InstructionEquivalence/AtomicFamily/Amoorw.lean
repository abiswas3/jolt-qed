import JoltBytecode.InstructionEquivalence.AtomicFamily.Word

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions
open virtaddr

set_option autoImplicit true

noncomputable section

namespace AtomicFamily

/-- Canonical Sail state after aligned `AMOOR.W`. -/
abbrev amoorwFinalSailState
    (rd : regidx) (s : SailState) (addr rs2Val : BitVec 64) : SailState :=
  amoWordFinalSailState rd s addr
    ((Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32) |||
      loaded_word_at s addr)

/-- Sail's generated `AMOOR.W` result expression reduces to word bitwise-or. -/
theorem amoorw_sail_result (rs2Val : BitVec 64) (loaded : BitVec 32) :
    amoWordSailResult amoop.AMOOR
      (show BitVec (4 * 8) from
        trunc (m := (((4 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
      (BitVec.setWidth (4 * 8) loaded) =
    (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32) ||| loaded := by
  rw [amo_word_trunc_4x8_eq_extract]
  rw [amo_word_setWidth_4x8_eq_self]

/-- Jolt-side aligned concrete execution for `AMOOR.W`. -/
theorem amoorwProgram_concrete_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_mem : AmoMemoryContext amoop.AMOOR 4
      (amoWordBase addr) addr js.sail)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    ∃ jsf : SailJoltState,
      (JoltISA.execProgram (JoltISA.amoorwProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail = amoorwFinalSailState rd js.sail addr rs2Val := by
  change
    ∃ jsf : SailJoltState,
      (JoltISA.execProgram
        (JoltISA.amoWordBinopProgram
          (fun dst lhs rhs => .OR dst lhs rhs) rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail = amoorwFinalSailState rd js.sail addr rs2Val
  exact
    amo_word_binop_program_concrete_aligned
      amoop.AMOOR (fun dst lhs rhs => .OR dst lhs rhs)
      rs2 rs1 rd js hcfg addr
      (rs2Val |||
        shift_bits_right
          (loaded_dword_at js.sail (amoWordBase addr))
          (Sail.BitVec.extractLsb
            (shift_bits_left addr (3 : BitVec 6)) 5 0))
      ((Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32) |||
        loaded_word_at js.sail addr)
      hrs1 h_mem h_align
      (amo_word_or_result_extract_eq js.sail addr rs2Val h_align)
      (amo_word_or_middle_after_pre rs2 js addr rs2Val hrs2)

/-- Sail-side aligned concrete execution for native `AMOOR.W`. -/
theorem execute_AMOORW_reduces_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryContext amoop.AMOOR 4
      (amoWordBase addr) addr js.sail)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    (execute_AMO amoop.AMOOR false false rs2 rs1 4 rd).run js.sail =
      .ok RETIRE_SUCCESS (amoorwFinalSailState rd js.sail addr rs2Val) := by
  exact
    execute_AMO_word_non_cas_aligned
      amoop.AMOOR rs2 rs1 rd js hcfg addr rs2Val
      ((Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32) |||
        loaded_word_at js.sail addr)
      hrs1 hrs2 hrd h_mem h_align
      (by decide)
      (amoorw_sail_result rs2Val (loaded_word_at js.sail addr))

/-- Aligned public branch for `AMOOR.W`. -/
theorem amoorwProgram_eq_sail_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryContext amoop.AMOOR 4
      (amoWordBase addr) addr js.sail)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoorwProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOOR false false rs2 rs1 4 rd).run js.sail := by
  rcases amoorwProgram_concrete_aligned
      rs2 rs1 rd js hcfg addr rs2Val hrs1 hrs2 h_mem h_align with
    ⟨jsf, hjolt, hjolt_sail⟩
  have hsail := execute_AMOORW_reduces_aligned
    rs2 rs1 rd js hcfg addr rs2Val hrs1 hrs2 hrd h_mem h_align
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail, hsail]

/-- Jolt-side misaligned execution for `AMOOR.W`. -/
theorem amoorwProgram_concrete_misaligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (addr : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (h_align : addr &&& (3 : BitVec 64) ≠ 0) :
    (JoltISA.execProgram (JoltISA.amoorwProgram rs2 rs1 rd)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr addr, ExceptionType.E_SAMO_Addr_Align ())) js := by
  unfold JoltISA.amoorwProgram JoltISA.amoWordBinopProgram
  exact
    amo_word_pre64_misaligned_run rs1 JoltISA.amoOldVReg
      JoltISA.amoDwordVReg JoltISA.amoShiftVReg
      (.instr (.OR (.vreg JoltISA.amoNewVReg)
        (.vreg JoltISA.amoOldVReg) (.xreg rs2)) <|
        JoltISA.amoPost64Program rs1 rd (.vreg JoltISA.amoNewVReg)
          JoltISA.amoDwordVReg JoltISA.amoShiftVReg
          JoltISA.amoMaskVReg JoltISA.amoOldVReg)
      js addr hrs1 h_align

/-- Sail-side misaligned execution for native `AMOOR.W`. -/
theorem execute_AMOORW_misaligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_align : addr &&& (3 : BitVec 64) ≠ 0) :
    (execute_AMO amoop.AMOOR false false rs2 rs1 4 rd).run js.sail =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr addr, ExceptionType.E_SAMO_Addr_Align ())) js.sail := by
  exact
    execute_AMO_word_misaligned
      amoop.AMOOR rs2 rs1 rd js hcfg addr rs2Val hrs1 hrs2 h_align

/-- Misaligned public branch for `AMOOR.W`. -/
theorem amoorwProgram_eq_sail_misaligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_align : addr &&& (3 : BitVec 64) ≠ 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoorwProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOOR false false rs2 rs1 4 rd).run js.sail := by
  have hjolt := amoorwProgram_concrete_misaligned
    rs2 rs1 rd js addr hrs1 h_align
  have hsail := execute_AMOORW_misaligned
    rs2 rs1 rd js hcfg addr rs2Val hrs1 hrs2 h_align
  rw [hjolt]
  simp only [projectResult, project]
  symm
  exact hsail

/-- Internal memory-context theorem for `AMOOR.W`. -/
theorem amoorwProgram_eq_sail_of_memory_context
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryContext amoop.AMOOR 4
      (amoWordBase addr) addr js.sail) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoorwProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOOR false false rs2 rs1 4 rd).run js.sail := by
  by_cases h_align : addr &&& (3 : BitVec 64) = 0
  · exact amoorwProgram_eq_sail_aligned
      rs2 rs1 rd js hcfg addr rs2Val hrs1 hrs2 hrd h_mem h_align
  · exact amoorwProgram_eq_sail_misaligned
      rs2 rs1 rd js hcfg addr rs2Val hrs1 hrs2 h_align

/-- Main public theorem for `AMOOR.W`.

The theorem takes one primitive-only atomic bundle. The aligned branch derives
exact memory context from the enclosing dword window; the misaligned branch
stops before memory context is needed. -/
private theorem amoorwProgram_project_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoWordProgramEqSailAssumptions amoop.AMOOR rs2 rs1 rd js) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoorwProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOOR false false rs2 rs1 4 rd).run js.sail := by
  let addr := h.rs1_val
  let rs2Val := h.rs2_val
  by_cases h_align : addr &&& (3 : BitVec 64) = 0
  · have h_mem_base :
        AmoMemoryContext amoop.AMOOR 4 (amoWordAssumptionBase addr) addr js.sail := by
      simpa [addr] using h.memoryContext (by simpa [addr] using h_align)
    have h_mem : AmoMemoryContext amoop.AMOOR 4 (amoWordBase addr) addr js.sail := by
      simpa [amoWordBase, amoWordAssumptionBase] using h_mem_base
    exact amoorwProgram_eq_sail_aligned
      rs2 rs1 rd js h.cfg addr rs2Val
      h.rs1_read h.rs2_read h.rd_readable.exists_value
      h_mem h_align
  · exact amoorwProgram_eq_sail_misaligned
      rs2 rs1 rd js h.cfg addr rs2Val
      h.rs1_read h.rs2_read h_align

/-- Main public theorem for `AMOOR.W`. -/
theorem amoorwProgram_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoWordProgramEqSailAssumptions amoop.AMOOR rs2 rs1 rd js) :
    ProgramMatchesSailWithProtectedFrame js
      ((JoltISA.execProgram (JoltISA.amoorwProgram rs2 rs1 rd)).run js)
      ((execute_AMO amoop.AMOOR false false rs2 rs1 4 rd).run js.sail) := by
  apply programMatchesSailWithProtectedFrame_of_projectResult_eq
  · exact amoorwProgram_project_eq_sail rs2 rs1 rd js h
  · simp [JoltISA.amoorwProgram, JoltISA.amoWordBinopProgram,
      JoltISA.amoPre64Program, JoltISA.amoPre64ProgramWithScratch,
      JoltISA.amoPost64Program, JoltISA.amoPost64ProgramWithScratch,
      JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg,
      JoltISA.DstWritesNoProtectedVReg,
      JoltISA.amoOldVReg, JoltISA.amoNewVReg, JoltISA.amoMaskVReg,
      JoltISA.amoDwordVReg, JoltISA.amoShiftVReg, JoltISA.amoInlineTmpVReg]

end AtomicFamily

end
