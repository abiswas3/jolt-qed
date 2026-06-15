import JoltBytecode.InstructionEquivalence.AtomicFamily.Dword

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace AtomicFamily

/-- Canonical Sail state after aligned `AMOMINU.D`.

The native AMO unsigned-min reads the old dword at `addr`, writes `rs2Val` when
`rs2Val < old` unsigned and otherwise writes `old`, then writes the old dword
value into `rd`. -/
abbrev amominudFinalSailState
    (rd : regidx) (s : SailState) (addr rs2Val : BitVec 64) : SailState :=
  amoDwordFinalSailState rd s addr
    (if (zopz0zI_u rs2Val (loaded_dword_at s addr) : Bool) then
      rs2Val
    else
      loaded_dword_at s addr)

/-- Sail's generated `AMOMINU.D` result expression reduces to unsigned min. -/
theorem amominud_sail_result (rs2Val loaded : BitVec 64) :
    amoDwordSailResult amoop.AMOMINU
      (show BitVec (8 * 8) from
        trunc (m := (((8 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
      (BitVec.setWidth (8 * 8) loaded) =
    if (zopz0zI_u rs2Val loaded : Bool) then rs2Val else loaded := by
  unfold amoDwordSailResult
  unfold trunc Sail.BitVec.truncate
  rfl

/-- Sail-side aligned concrete execution for native `AMOMINU.D`. -/
theorem execute_AMOMINUD_reduces_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryContext amoop.AMOMINU 8 addr addr js.sail)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    (execute_AMO amoop.AMOMINU false false rs2 rs1 8 rd).run js.sail =
      .ok RETIRE_SUCCESS (amominudFinalSailState rd js.sail addr rs2Val) := by
  change
    (execute_AMO amoop.AMOMINU false false rs2 rs1 8 rd).run js.sail =
      .ok RETIRE_SUCCESS
        (amoDwordFinalSailState rd js.sail addr
          (if (zopz0zI_u rs2Val (loaded_dword_at js.sail addr) : Bool) then
            rs2Val
          else
            loaded_dword_at js.sail addr))
  exact
    execute_AMO_dword_non_cas_aligned
      amoop.AMOMINU rs2 rs1 rd js hcfg addr rs2Val
      (if (zopz0zI_u rs2Val (loaded_dword_at js.sail addr) : Bool) then
        rs2Val
      else
        loaded_dword_at js.sail addr)
      hrs1 hrs2 hrd h_mem h_align
      (by decide)
      (amominud_sail_result rs2Val (loaded_dword_at js.sail addr))

/-- Jolt-side aligned concrete execution for `AMOMINU.D`.

The shared dword select helper handles the common assert/load/store/writeback
shape and the phased comparison-plus-select middle block. -/
theorem amominudProgram_concrete_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_mem : AmoMemoryContext amoop.AMOMINU 8 addr addr js.sail)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    ∃ jsf : SailJoltState,
      (JoltISA.execProgram (JoltISA.amominudProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail = amominudFinalSailState rd js.sail addr rs2Val := by
  change
    ∃ jsf : SailJoltState,
      (JoltISA.execProgram
        (JoltISA.amoDoubleSelectProgram
          (fun dst lhs rhs => .SLTU dst lhs rhs)
          (.xreg rs2) (.vreg JoltISA.amoOldVReg) rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail =
        amoDwordFinalSailState rd js.sail addr
          (if (zopz0zI_u rs2Val (loaded_dword_at js.sail addr) : Bool) then
            rs2Val
          else
            loaded_dword_at js.sail addr)
  exact
    amo_dword_double_select_program_concrete_aligned
      amoop.AMOMINU (fun dst lhs rhs => .SLTU dst lhs rhs)
      (.xreg rs2) (.vreg JoltISA.amoOldVReg)
      rs2 rs1 rd js hcfg addr
      (if (zopz0zI_u rs2Val (loaded_dword_at js.sail addr) : Bool) then
        rs2Val
      else
        loaded_dword_at js.sail addr)
      hrs1 h_mem h_align
      (amo_dword_minu_middle_after_load rs2 js addr rs2Val hrs2)

/-- Aligned public branch for `AMOMINU.D`, composed through the shared dword
double-select theorem. -/
theorem amominudProgram_eq_sail_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryContext amoop.AMOMINU 8 addr addr js.sail)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amominudProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOMINU false false rs2 rs1 8 rd).run js.sail := by
  change
    projectResult ((JoltISA.execProgram
      (JoltISA.amoDoubleSelectProgram
        (fun dst lhs rhs => .SLTU dst lhs rhs)
        (.xreg rs2) (.vreg JoltISA.amoOldVReg) rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOMINU false false rs2 rs1 8 rd).run js.sail
  exact
    amo_dword_double_select_program_eq_sail_aligned
      amoop.AMOMINU (fun dst lhs rhs => .SLTU dst lhs rhs)
      (.xreg rs2) (.vreg JoltISA.amoOldVReg)
      rs2 rs1 rd js hcfg addr rs2Val
      (if (zopz0zI_u rs2Val (loaded_dword_at js.sail addr) : Bool) then
        rs2Val
      else
        loaded_dword_at js.sail addr)
      hrs1 hrs2 hrd h_mem h_align
      (by decide)
      (amo_dword_minu_middle_after_load rs2 js addr rs2Val hrs2)
      (amominud_sail_result rs2Val (loaded_dword_at js.sail addr))

/-- Internal memory-context theorem for `AMOMINU.D`.

The theorem exposes no alignment hypothesis; it delegates the aligned and
misaligned cases to the shared dword double-select theorem. -/
theorem amominudProgram_eq_sail_of_memory_context
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryContext amoop.AMOMINU 8 addr addr js.sail) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amominudProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOMINU false false rs2 rs1 8 rd).run js.sail := by
  change
    projectResult ((JoltISA.execProgram
      (JoltISA.amoDoubleSelectProgram
        (fun dst lhs rhs => .SLTU dst lhs rhs)
        (.xreg rs2) (.vreg JoltISA.amoOldVReg) rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOMINU false false rs2 rs1 8 rd).run js.sail
  exact
    amo_dword_double_select_program_eq_sail
      amoop.AMOMINU (fun dst lhs rhs => .SLTU dst lhs rhs)
      (.xreg rs2) (.vreg JoltISA.amoOldVReg)
      rs2 rs1 rd js hcfg addr rs2Val
      (if (zopz0zI_u rs2Val (loaded_dword_at js.sail addr) : Bool) then
        rs2Val
      else
        loaded_dword_at js.sail addr)
      hrs1 hrs2 hrd h_mem
      (by decide)
      (amo_dword_minu_middle_after_load rs2 js addr rs2Val hrs2)
      (amominud_sail_result rs2Val (loaded_dword_at js.sail addr))

/-- Main public theorem for `AMOMINU.D`.

The theorem takes one primitive-only atomic bundle. Exact memory context is
derived internally from that bundle. -/
theorem amominudProgram_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoDwordProgramEqSailAssumptions amoop.AMOMINU rs2 rs1 rd js) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amominudProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOMINU false false rs2 rs1 8 rd).run js.sail := by
  let addr := h.rs1_val
  let rs2Val := h.rs2_val
  have h_mem : AmoMemoryContext amoop.AMOMINU 8 addr addr js.sail := by
    simpa [addr] using h.memoryContext
  exact amominudProgram_eq_sail_of_memory_context
    rs2 rs1 rd js h.cfg addr rs2Val
    h.rs1_read.value_eq h.rs2_read.value_eq h.rd_readable.exists_value h_mem

end AtomicFamily

end
