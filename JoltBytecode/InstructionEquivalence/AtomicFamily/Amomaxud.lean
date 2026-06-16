import JoltBytecode.InstructionEquivalence.AtomicFamily.Dword

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace AtomicFamily

/-- Canonical Sail state after aligned `AMOMAXU.D`. -/
abbrev amomaxudFinalSailState
    (rd : regidx) (s : SailState) (addr rs2Val : BitVec 64) : SailState :=
  amoDwordFinalSailState rd s addr
    (if (zopz0zK_u rs2Val (loaded_dword_at s addr) : Bool) then
      rs2Val
    else
      loaded_dword_at s addr)

/-- Sail's generated `AMOMAXU.D` result expression reduces to unsigned max. -/
theorem amomaxud_sail_result (rs2Val loaded : BitVec 64) :
    amoDwordSailResult amoop.AMOMAXU
      (show BitVec (8 * 8) from
        trunc (m := (((8 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
      (BitVec.setWidth (8 * 8) loaded) =
    if (zopz0zK_u rs2Val loaded : Bool) then rs2Val else loaded := by
  unfold amoDwordSailResult
  unfold trunc Sail.BitVec.truncate
  rfl

/-- Sail-side aligned concrete execution for native `AMOMAXU.D`. -/
theorem execute_AMOMAXUD_reduces_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryContext amoop.AMOMAXU 8 addr addr js.sail)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    (execute_AMO amoop.AMOMAXU false false rs2 rs1 8 rd).run js.sail =
      .ok RETIRE_SUCCESS (amomaxudFinalSailState rd js.sail addr rs2Val) := by
  change
    (execute_AMO amoop.AMOMAXU false false rs2 rs1 8 rd).run js.sail =
      .ok RETIRE_SUCCESS
        (amoDwordFinalSailState rd js.sail addr
          (if (zopz0zK_u rs2Val (loaded_dword_at js.sail addr) : Bool) then
            rs2Val
          else
            loaded_dword_at js.sail addr))
  exact
    execute_AMO_dword_non_cas_aligned
      amoop.AMOMAXU rs2 rs1 rd js hcfg addr rs2Val
      (if (zopz0zK_u rs2Val (loaded_dword_at js.sail addr) : Bool) then
        rs2Val
      else
        loaded_dword_at js.sail addr)
      hrs1 hrs2 hrd h_mem h_align
      (by decide)
      (amomaxud_sail_result rs2Val (loaded_dword_at js.sail addr))

/-- Jolt-side aligned concrete execution for `AMOMAXU.D`. -/
theorem amomaxudProgram_concrete_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_mem : AmoMemoryContext amoop.AMOMAXU 8 addr addr js.sail)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    ∃ jsf : SailJoltState,
      (JoltISA.execProgram (JoltISA.amomaxudProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail = amomaxudFinalSailState rd js.sail addr rs2Val := by
  change
    ∃ jsf : SailJoltState,
      (JoltISA.execProgram
        (JoltISA.amoDoubleSelectProgram
          (fun dst lhs rhs => .SLTU dst lhs rhs)
          (.vreg JoltISA.amoOldVReg) (.xreg rs2) rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail =
        amoDwordFinalSailState rd js.sail addr
          (if (zopz0zK_u rs2Val (loaded_dword_at js.sail addr) : Bool) then
            rs2Val
          else
            loaded_dword_at js.sail addr)
  exact
    amo_dword_double_select_program_concrete_aligned
      amoop.AMOMAXU (fun dst lhs rhs => .SLTU dst lhs rhs)
      (.vreg JoltISA.amoOldVReg) (.xreg rs2)
      rs2 rs1 rd js hcfg addr
      (if (zopz0zK_u rs2Val (loaded_dword_at js.sail addr) : Bool) then
        rs2Val
      else
        loaded_dword_at js.sail addr)
      hrs1 h_mem h_align
      (amo_dword_maxu_middle_after_load rs2 js addr rs2Val hrs2)

/-- Aligned public branch for `AMOMAXU.D`. -/
theorem amomaxudProgram_eq_sail_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryContext amoop.AMOMAXU 8 addr addr js.sail)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amomaxudProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOMAXU false false rs2 rs1 8 rd).run js.sail := by
  change
    projectResult ((JoltISA.execProgram
      (JoltISA.amoDoubleSelectProgram
        (fun dst lhs rhs => .SLTU dst lhs rhs)
        (.vreg JoltISA.amoOldVReg) (.xreg rs2) rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOMAXU false false rs2 rs1 8 rd).run js.sail
  exact
    amo_dword_double_select_program_eq_sail_aligned
      amoop.AMOMAXU (fun dst lhs rhs => .SLTU dst lhs rhs)
      (.vreg JoltISA.amoOldVReg) (.xreg rs2)
      rs2 rs1 rd js hcfg addr rs2Val
      (if (zopz0zK_u rs2Val (loaded_dword_at js.sail addr) : Bool) then
        rs2Val
      else
        loaded_dword_at js.sail addr)
      hrs1 hrs2 hrd h_mem h_align
      (by decide)
      (amo_dword_maxu_middle_after_load rs2 js addr rs2Val hrs2)
      (amomaxud_sail_result rs2Val (loaded_dword_at js.sail addr))

/-- Internal memory-context theorem for `AMOMAXU.D`. -/
theorem amomaxudProgram_eq_sail_of_memory_context
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryContext amoop.AMOMAXU 8 addr addr js.sail) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amomaxudProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOMAXU false false rs2 rs1 8 rd).run js.sail := by
  change
    projectResult ((JoltISA.execProgram
      (JoltISA.amoDoubleSelectProgram
        (fun dst lhs rhs => .SLTU dst lhs rhs)
        (.vreg JoltISA.amoOldVReg) (.xreg rs2) rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOMAXU false false rs2 rs1 8 rd).run js.sail
  exact
    amo_dword_double_select_program_project_eq_sail
      amoop.AMOMAXU (fun dst lhs rhs => .SLTU dst lhs rhs)
      (.vreg JoltISA.amoOldVReg) (.xreg rs2)
      rs2 rs1 rd js hcfg addr rs2Val
      (if (zopz0zK_u rs2Val (loaded_dword_at js.sail addr) : Bool) then
        rs2Val
      else
        loaded_dword_at js.sail addr)
      hrs1 hrs2 hrd h_mem
      (by decide)
      (amo_dword_maxu_middle_after_load rs2 js addr rs2Val hrs2)
      (amomaxud_sail_result rs2Val (loaded_dword_at js.sail addr))

/-- Main public theorem for `AMOMAXU.D`.

The theorem takes one primitive-only atomic bundle. Exact memory context is
derived internally from that bundle. -/
private theorem amomaxudProgram_project_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoDwordProgramEqSailAssumptions amoop.AMOMAXU rs2 rs1 rd js) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amomaxudProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOMAXU false false rs2 rs1 8 rd).run js.sail := by
  let addr := h.rs1_val
  let rs2Val := h.rs2_val
  have h_mem : AmoMemoryContext amoop.AMOMAXU 8 addr addr js.sail := by
    simpa [addr] using h.memoryContext
  exact amomaxudProgram_eq_sail_of_memory_context
    rs2 rs1 rd js h.cfg addr rs2Val
    h.rs1_read h.rs2_read h.rd_readable.exists_value h_mem

/-- Main public theorem for `AMOMAXU.D`. -/
theorem amomaxudProgram_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoDwordProgramEqSailAssumptions amoop.AMOMAXU rs2 rs1 rd js) :
    ProgramMatchesSailWithProtectedFrame js
      ((JoltISA.execProgram (JoltISA.amomaxudProgram rs2 rs1 rd)).run js)
      ((execute_AMO amoop.AMOMAXU false false rs2 rs1 8 rd).run js.sail) := by
  apply programMatchesSailWithProtectedFrame_of_projectResult_eq
  · exact amomaxudProgram_project_eq_sail rs2 rs1 rd js h
  · simp [JoltISA.amomaxudProgram, JoltISA.amoDoubleSelectProgram,
      JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg,
      JoltISA.DstWritesNoProtectedVReg,
      JoltISA.amoOldVReg, JoltISA.amoNewVReg, JoltISA.amoTmpVReg]

end AtomicFamily

end
