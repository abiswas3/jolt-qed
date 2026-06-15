import JoltBytecode.InstructionEquivalence.AtomicFamily.Dword

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace AtomicFamily

/-- Canonical Sail state after aligned `AMOAND.D`.

The native AMO and reads the old dword at `addr`, writes `rs2Val & old`, then
writes the old dword value into `rd`. -/
abbrev amoanddFinalSailState
    (rd : regidx) (s : SailState) (addr rs2Val : BitVec 64) : SailState :=
  amoDwordFinalSailState rd s addr (rs2Val &&& loaded_dword_at s addr)

/-- Sail's generated `AMOAND.D` result expression reduces to dword and. -/
theorem amoandd_sail_result (rs2Val loaded : BitVec 64) :
    amoDwordSailResult amoop.AMOAND
      (show BitVec (8 * 8) from
        trunc (m := (((8 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
      (BitVec.setWidth (8 * 8) loaded) =
    rs2Val &&& loaded := by
  unfold amoDwordSailResult
  unfold trunc Sail.BitVec.truncate
  rfl

/-- Sail-side aligned concrete execution for native `AMOAND.D`. -/
theorem execute_AMOANDD_reduces_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryContext amoop.AMOAND 8 addr addr js.sail)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    (execute_AMO amoop.AMOAND false false rs2 rs1 8 rd).run js.sail =
      .ok RETIRE_SUCCESS (amoanddFinalSailState rd js.sail addr rs2Val) := by
  change
    (execute_AMO amoop.AMOAND false false rs2 rs1 8 rd).run js.sail =
      .ok RETIRE_SUCCESS
        (amoDwordFinalSailState rd js.sail addr
          (rs2Val &&& loaded_dword_at js.sail addr))
  exact
    execute_AMO_dword_non_cas_aligned
      amoop.AMOAND rs2 rs1 rd js hcfg addr rs2Val
      (rs2Val &&& loaded_dword_at js.sail addr)
      hrs1 hrs2 hrd h_mem h_align
      (by decide)
      (amoandd_sail_result rs2Val (loaded_dword_at js.sail addr))

/-- Jolt-side aligned concrete execution for `AMOAND.D`.

The shared dword binop helper handles the common assert/load/store/writeback
shape; the only operation-specific step is the middle `AND`. -/
theorem amoanddProgram_concrete_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_mem : AmoMemoryContext amoop.AMOAND 8 addr addr js.sail)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    ∃ jsf : SailJoltState,
      (JoltISA.execProgram (JoltISA.amoanddProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail = amoanddFinalSailState rd js.sail addr rs2Val := by
  change
    ∃ jsf : SailJoltState,
      (JoltISA.execProgram
        (JoltISA.amoDoubleBinopProgram
          (fun dst lhs rhs => .AND dst lhs rhs) rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail =
        amoDwordFinalSailState rd js.sail addr
          (rs2Val &&& loaded_dword_at js.sail addr)
  exact
    amo_dword_double_binop_program_concrete_aligned
      amoop.AMOAND (fun dst lhs rhs => .AND dst lhs rhs)
      rs2 rs1 rd js hcfg addr
      (rs2Val &&& loaded_dword_at js.sail addr)
      hrs1 h_mem h_align
      (amo_dword_and_middle_after_load rs2 js addr rs2Val hrs2)

/-- Aligned public branch for `AMOAND.D`, composed through the shared dword
double-binop theorem. -/
theorem amoanddProgram_eq_sail_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryContext amoop.AMOAND 8 addr addr js.sail)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoanddProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOAND false false rs2 rs1 8 rd).run js.sail := by
  change
    projectResult ((JoltISA.execProgram
      (JoltISA.amoDoubleBinopProgram
        (fun dst lhs rhs => .AND dst lhs rhs) rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOAND false false rs2 rs1 8 rd).run js.sail
  exact
    amo_dword_double_binop_program_eq_sail_aligned
      amoop.AMOAND (fun dst lhs rhs => .AND dst lhs rhs)
      rs2 rs1 rd js hcfg addr rs2Val
      (rs2Val &&& loaded_dword_at js.sail addr)
      hrs1 hrs2 hrd h_mem h_align
      (by decide)
      (amo_dword_and_middle_after_load rs2 js addr rs2Val hrs2)
      (amoandd_sail_result rs2Val (loaded_dword_at js.sail addr))

/-- Internal memory-context theorem for `AMOAND.D`.

The theorem exposes no alignment hypothesis; it delegates the aligned and
misaligned cases to the shared dword double-binop theorem. -/
theorem amoanddProgram_eq_sail_of_memory_context
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryContext amoop.AMOAND 8 addr addr js.sail) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoanddProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOAND false false rs2 rs1 8 rd).run js.sail := by
  change
    projectResult ((JoltISA.execProgram
      (JoltISA.amoDoubleBinopProgram
        (fun dst lhs rhs => .AND dst lhs rhs) rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOAND false false rs2 rs1 8 rd).run js.sail
  exact
    amo_dword_double_binop_program_eq_sail
      amoop.AMOAND (fun dst lhs rhs => .AND dst lhs rhs)
      rs2 rs1 rd js hcfg addr rs2Val
      (rs2Val &&& loaded_dword_at js.sail addr)
      hrs1 hrs2 hrd h_mem
      (by decide)
      (amo_dword_and_middle_after_load rs2 js addr rs2Val hrs2)
      (amoandd_sail_result rs2Val (loaded_dword_at js.sail addr))

/-- Main public theorem for `AMOAND.D`.

The theorem takes one primitive-only atomic bundle. Exact memory context is
derived internally from that bundle. -/
theorem amoanddProgram_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoDwordProgramEqSailAssumptions amoop.AMOAND rs2 rs1 rd js) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoanddProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOAND false false rs2 rs1 8 rd).run js.sail := by
  let addr := h.rs1_val
  let rs2Val := h.rs2_val
  have h_mem : AmoMemoryContext amoop.AMOAND 8 addr addr js.sail := by
    simpa [addr] using h.memoryContext
  exact amoanddProgram_eq_sail_of_memory_context
    rs2 rs1 rd js h.cfg addr rs2Val
    h.rs1_read.value_eq h.rs2_read.value_eq h.rd_readable.exists_value h_mem

end AtomicFamily

end
