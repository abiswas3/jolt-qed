import JoltBytecode.InstructionEquivalence.AtomicFamily.Dword

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace AtomicFamily

/-- Canonical Sail state after aligned `AMOADD.D`.

The native AMO add reads the old dword at `addr`, writes `rs2Val + old`, then
writes the old dword value into `rd`. -/
abbrev amoadddFinalSailState
    (rd : regidx) (s : SailState) (addr rs2Val : BitVec 64) : SailState :=
  amoDwordFinalSailState rd s addr (rs2Val + loaded_dword_at s addr)

/-- Sail's generated `AMOADD.D` result expression reduces to dword addition. -/
theorem amoaddd_sail_result (rs2Val loaded : BitVec 64) :
    amoDwordSailResult amoop.AMOADD
      (show BitVec (8 * 8) from
        trunc (m := (((8 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
      (BitVec.setWidth (8 * 8) loaded) =
    rs2Val + loaded := by
  unfold amoDwordSailResult
  unfold trunc Sail.BitVec.truncate
  rfl

/-- Sail-side aligned concrete execution for native `AMOADD.D`. -/
theorem execute_AMOADDD_reduces_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryContext amoop.AMOADD 8 addr addr js.sail)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    (execute_AMO amoop.AMOADD false false rs2 rs1 8 rd).run js.sail =
      .ok RETIRE_SUCCESS (amoadddFinalSailState rd js.sail addr rs2Val) := by
  change
    (execute_AMO amoop.AMOADD false false rs2 rs1 8 rd).run js.sail =
      .ok RETIRE_SUCCESS
        (amoDwordFinalSailState rd js.sail addr
          (rs2Val + loaded_dword_at js.sail addr))
  exact
    execute_AMO_dword_non_cas_aligned
      amoop.AMOADD rs2 rs1 rd js hcfg addr rs2Val
      (rs2Val + loaded_dword_at js.sail addr)
      hrs1 hrs2 hrd h_mem h_align
      (by decide)
      (amoaddd_sail_result rs2Val (loaded_dword_at js.sail addr))

/-- Jolt-side aligned concrete execution for `AMOADD.D`.

The shared dword binop helper handles the common assert/load/store/writeback
shape; the only operation-specific step is the middle `ADD`. -/
theorem amoadddProgram_concrete_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_mem : AmoMemoryContext amoop.AMOADD 8 addr addr js.sail)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    ∃ jsf : SailJoltState,
      (JoltISA.execProgram (JoltISA.amoadddProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail = amoadddFinalSailState rd js.sail addr rs2Val := by
  change
    ∃ jsf : SailJoltState,
      (JoltISA.execProgram
        (JoltISA.amoDoubleBinopProgram
          (fun dst lhs rhs => .ADD dst lhs rhs) rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail =
        amoDwordFinalSailState rd js.sail addr
          (rs2Val + loaded_dword_at js.sail addr)
  exact
    amo_dword_double_binop_program_concrete_aligned
      amoop.AMOADD (fun dst lhs rhs => .ADD dst lhs rhs)
      rs2 rs1 rd js hcfg addr
      (rs2Val + loaded_dword_at js.sail addr)
      hrs1 h_mem h_align
      (amo_dword_add_middle_after_load rs2 js addr rs2Val hrs2)

/-- Aligned public branch for `AMOADD.D`, composed through the shared dword
double-binop theorem. -/
theorem amoadddProgram_eq_sail_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryContext amoop.AMOADD 8 addr addr js.sail)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoadddProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOADD false false rs2 rs1 8 rd).run js.sail := by
  change
    projectResult ((JoltISA.execProgram
      (JoltISA.amoDoubleBinopProgram
        (fun dst lhs rhs => .ADD dst lhs rhs) rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOADD false false rs2 rs1 8 rd).run js.sail
  exact
    amo_dword_double_binop_program_eq_sail_aligned
      amoop.AMOADD (fun dst lhs rhs => .ADD dst lhs rhs)
      rs2 rs1 rd js h_mem.cfg addr rs2Val
      (rs2Val + loaded_dword_at js.sail addr)
      hrs1 hrs2 hrd h_mem h_align
      (by decide)
      (amo_dword_add_middle_after_load rs2 js addr rs2Val hrs2)
      (amoaddd_sail_result rs2Val (loaded_dword_at js.sail addr))

/-- Internal memory-context theorem for `AMOADD.D`.

The theorem exposes no alignment hypothesis; it delegates the aligned and
misaligned cases to the shared dword double-binop theorem. -/
theorem amoadddProgram_eq_sail_of_memory_context
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryContext amoop.AMOADD 8 addr addr js.sail) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoadddProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOADD false false rs2 rs1 8 rd).run js.sail := by
  change
    projectResult ((JoltISA.execProgram
      (JoltISA.amoDoubleBinopProgram
        (fun dst lhs rhs => .ADD dst lhs rhs) rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOADD false false rs2 rs1 8 rd).run js.sail
  exact
    amo_dword_double_binop_program_project_eq_sail
      amoop.AMOADD (fun dst lhs rhs => .ADD dst lhs rhs)
      rs2 rs1 rd js h_mem.cfg addr rs2Val
      (rs2Val + loaded_dword_at js.sail addr)
      hrs1 hrs2 hrd h_mem
      (by decide)
      (amo_dword_add_middle_after_load rs2 js addr rs2Val hrs2)
      (amoaddd_sail_result rs2Val (loaded_dword_at js.sail addr))

/-- Main public theorem for `AMOADD.D`.

The theorem takes one primitive-only atomic bundle. Exact memory context is
derived internally from that bundle. -/
private theorem amoadddProgram_project_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoDwordProgramEqSailAssumptions amoop.AMOADD rs2 rs1 rd js) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoadddProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOADD false false rs2 rs1 8 rd).run js.sail := by
  let addr := h.rs1_val
  let rs2Val := h.rs2_val
  have h_mem : AmoMemoryContext amoop.AMOADD 8 addr addr js.sail := by
    simpa [addr] using h.memoryContext
  exact amoadddProgram_eq_sail_of_memory_context
    rs2 rs1 rd js addr rs2Val
    h.rs1_read h.rs2_read h.rd_readable.exists_value h_mem

/-- Main public theorem for `AMOADD.D`.

The theorem takes one primitive-only atomic bundle, matches Sail, and preserves
every protected Jolt register on successful runs. -/
def amoadddProgramEqSailStatement
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (_h : AmoDwordProgramEqSailAssumptions amoop.AMOADD rs2 rs1 rd js) : Prop :=
  ProgramMatchesSailWithProtectedFrame js
    ((JoltISA.execProgram (JoltISA.amoadddProgram rs2 rs1 rd)).run js)
    ((execute_AMO amoop.AMOADD false false rs2 rs1 8 rd).run js.sail)

theorem amoadddProgram_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoDwordProgramEqSailAssumptions amoop.AMOADD rs2 rs1 rd js) :
    amoadddProgramEqSailStatement rs2 rs1 rd js h := by
  apply programMatchesSailWithProtectedFrame_of_projectResult_eq
  · exact amoadddProgram_project_eq_sail rs2 rs1 rd js h
  · simp [JoltISA.amoadddProgram, JoltISA.amoDoubleBinopProgram,
      JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg,
      JoltISA.DstWritesNoProtectedVReg,
      JoltISA.amoDoubleBinopNewVReg, JoltISA.amoDoubleBinopOldVReg]

end AtomicFamily

end
