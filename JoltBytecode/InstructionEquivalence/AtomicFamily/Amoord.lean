import JoltBytecode.InstructionEquivalence.AtomicFamily.Dword

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace AtomicFamily

/-- Canonical Sail state after aligned `AMOOR.D`.

The native AMO or reads the old dword at `addr`, writes `rs2Val | old`, then
writes the old dword value into `rd`. -/
abbrev amoordFinalSailState
    (rd : regidx) (s : SailState) (addr rs2Val : BitVec 64) : SailState :=
  amoDwordFinalSailState rd s addr (rs2Val ||| loaded_dword_at s addr)

/-- Sail's generated `AMOOR.D` result expression reduces to dword or. -/
theorem amoord_sail_result (rs2Val loaded : BitVec 64) :
    amoDwordSailResult amoop.AMOOR
      (show BitVec (8 * 8) from
        trunc (m := (((8 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
      (BitVec.setWidth (8 * 8) loaded) =
    rs2Val ||| loaded := by
  unfold amoDwordSailResult
  unfold trunc Sail.BitVec.truncate
  rfl

/-- Sail-side aligned concrete execution for native `AMOOR.D`. -/
theorem execute_AMOORD_reduces_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryContext amoop.AMOOR 8 addr addr js.sail)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    (execute_AMO amoop.AMOOR false false rs2 rs1 8 rd).run js.sail =
      .ok RETIRE_SUCCESS (amoordFinalSailState rd js.sail addr rs2Val) := by
  change
    (execute_AMO amoop.AMOOR false false rs2 rs1 8 rd).run js.sail =
      .ok RETIRE_SUCCESS
        (amoDwordFinalSailState rd js.sail addr
          (rs2Val ||| loaded_dword_at js.sail addr))
  exact
    execute_AMO_dword_non_cas_aligned
      amoop.AMOOR rs2 rs1 rd js hcfg addr rs2Val
      (rs2Val ||| loaded_dword_at js.sail addr)
      hrs1 hrs2 hrd h_mem h_align
      (by decide)
      (amoord_sail_result rs2Val (loaded_dword_at js.sail addr))

/-- Jolt-side aligned concrete execution for `AMOOR.D`.

The shared dword binop helper handles the common assert/load/store/writeback
shape; the only operation-specific step is the middle `OR`. -/
theorem amoordProgram_concrete_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_mem : AmoMemoryContext amoop.AMOOR 8 addr addr js.sail)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    ∃ jsf : SailJoltState,
      (JoltISA.execProgram (JoltISA.amoordProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail = amoordFinalSailState rd js.sail addr rs2Val := by
  change
    ∃ jsf : SailJoltState,
      (JoltISA.execProgram
        (JoltISA.amoDoubleBinopProgram
          (fun dst lhs rhs => .OR dst lhs rhs) rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail =
        amoDwordFinalSailState rd js.sail addr
          (rs2Val ||| loaded_dword_at js.sail addr)
  exact
    amo_dword_double_binop_program_concrete_aligned
      amoop.AMOOR (fun dst lhs rhs => .OR dst lhs rhs)
      rs2 rs1 rd js hcfg addr
      (rs2Val ||| loaded_dword_at js.sail addr)
      hrs1 h_mem h_align
      (amo_dword_or_middle_after_load rs2 js addr rs2Val hrs2)

/-- Aligned public branch for `AMOOR.D`, composed through the shared dword
double-binop theorem. -/
theorem amoordProgram_eq_sail_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryContext amoop.AMOOR 8 addr addr js.sail)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoordProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOOR false false rs2 rs1 8 rd).run js.sail := by
  change
    projectResult ((JoltISA.execProgram
      (JoltISA.amoDoubleBinopProgram
        (fun dst lhs rhs => .OR dst lhs rhs) rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOOR false false rs2 rs1 8 rd).run js.sail
  exact
    amo_dword_double_binop_program_eq_sail_aligned
      amoop.AMOOR (fun dst lhs rhs => .OR dst lhs rhs)
      rs2 rs1 rd js hcfg addr rs2Val
      (rs2Val ||| loaded_dword_at js.sail addr)
      hrs1 hrs2 hrd h_mem h_align
      (by decide)
      (amo_dword_or_middle_after_load rs2 js addr rs2Val hrs2)
      (amoord_sail_result rs2Val (loaded_dword_at js.sail addr))

/-- Internal memory-context theorem for `AMOOR.D`.

The theorem exposes no alignment hypothesis; it delegates the aligned and
misaligned cases to the shared dword double-binop theorem. -/
theorem amoordProgram_eq_sail_of_memory_context
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryContext amoop.AMOOR 8 addr addr js.sail) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoordProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOOR false false rs2 rs1 8 rd).run js.sail := by
  change
    projectResult ((JoltISA.execProgram
      (JoltISA.amoDoubleBinopProgram
        (fun dst lhs rhs => .OR dst lhs rhs) rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOOR false false rs2 rs1 8 rd).run js.sail
  exact
    amo_dword_double_binop_program_project_eq_sail
      amoop.AMOOR (fun dst lhs rhs => .OR dst lhs rhs)
      rs2 rs1 rd js hcfg addr rs2Val
      (rs2Val ||| loaded_dword_at js.sail addr)
      hrs1 hrs2 hrd h_mem
      (by decide)
      (amo_dword_or_middle_after_load rs2 js addr rs2Val hrs2)
      (amoord_sail_result rs2Val (loaded_dword_at js.sail addr))

/-- Main public theorem for `AMOOR.D`.

The theorem takes one primitive-only atomic bundle. Exact memory context is
derived internally from that bundle. -/
private theorem amoordProgram_project_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoDwordProgramEqSailAssumptions amoop.AMOOR rs2 rs1 rd js) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoordProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOOR false false rs2 rs1 8 rd).run js.sail := by
  let addr := h.rs1_val
  let rs2Val := h.rs2_val
  have h_mem : AmoMemoryContext amoop.AMOOR 8 addr addr js.sail := by
    simpa [addr] using h.memoryContext
  exact amoordProgram_eq_sail_of_memory_context
    rs2 rs1 rd js h.cfg addr rs2Val
    h.rs1_read h.rs2_read h.rd_readable.exists_value h_mem

/-- Main public theorem for `AMOOR.D`. -/
def amoordProgramEqSailStatement
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (_h : AmoDwordProgramEqSailAssumptions amoop.AMOOR rs2 rs1 rd js) : Prop :=
  ProgramMatchesSailWithProtectedFrame js
    ((JoltISA.execProgram (JoltISA.amoordProgram rs2 rs1 rd)).run js)
    ((execute_AMO amoop.AMOOR false false rs2 rs1 8 rd).run js.sail)

theorem amoordProgram_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoDwordProgramEqSailAssumptions amoop.AMOOR rs2 rs1 rd js) :
    amoordProgramEqSailStatement rs2 rs1 rd js h := by
  apply programMatchesSailWithProtectedFrame_of_projectResult_eq
  · exact amoordProgram_project_eq_sail rs2 rs1 rd js h
  · simp [JoltISA.amoordProgram, JoltISA.amoDoubleBinopProgram,
      JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg,
      JoltISA.DstWritesNoProtectedVReg,
      JoltISA.amoDoubleBinopNewVReg, JoltISA.amoDoubleBinopOldVReg]

end AtomicFamily

end
