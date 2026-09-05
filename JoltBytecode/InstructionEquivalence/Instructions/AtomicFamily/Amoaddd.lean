import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Dword
import JoltBytecode.InstructionEquivalence.ProofSupport.SystemProjection
import JoltBytecode.JoltISA.automaticEquivHand

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace AtomicFamily

/-- The AmoAddd Jolt program does not write to protected register-/
theorem amoadddProgram_doesNotWriteProtectedVRegs
    (rs2 rs1 rd : regidx) :
    (JoltISA.amoadddProgram rs2 rs1 rd).DoesNotWriteProtectedVRegs := by
  rcases eq_or_ne (JoltISA.isX0 rd) true with hrd | hrd
  · simp [JoltISA.amoadddProgram, JoltISA.amoDoubleBinopProgram,
      JoltISA.Program.DoesNotWriteProtectedVRegs,
      JoltISA.Program.WritesProtectedVReg,
      JoltISA.Instr.WritesProtectedVReg, JoltISA.Dst.WritesProtectedVReg,
      JoltISA.amoDstFor, JoltISA.sideEffectingRdZeroDst, hrd]
  · simp only[JoltISA.amoadddProgram, 
              JoltISA.amoDoubleBinopProgram,
              JoltISA.Program.DoesNotWriteProtectedVRegs,
              JoltISA.Program.WritesProtectedVReg,
              JoltISA.Instr.WritesProtectedVReg, 
              JoltISA.Dst.WritesProtectedVReg,
              JoltISA.amoDstFor, 
              JoltISA.sideEffectingRdZeroDst, 
              hrd]
    simp only [JoltISA.sideEffectingDst_vreg, 
              JoltISA.amoDoubleBinopOldVRegFor_not_protected,
              JoltISA.amoDoubleBinopNewVRegFor_not_protected, 
              Bool.false_eq_true, 
              ↓reduceIte,
              or_self, 
              not_false_eq_true]

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

/-- The theorem takes one primitive-only atomic bundle. Exact memory context is
derived internally from that bundle. -/
private theorem amoadddProgram_project_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoDwordProgramEqSailAssumptions amoop.AMOADD rs2 rs1 rd js) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoadddProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOADD false false rs2 rs1 8 rd).run js.sail := by
  let addr := h.rs1_val
  let rs2Val := h.rs2_val
  have hbytes : MemBytesPresentAt js.sail addr 8 := by
    simpa [addr] using Assumptions.DwordPresent.memBytesPresentAt h.dword_present
  have hload_pmp : Assumptions.LoadPmpOk addr 8 js.sail := by
    simpa [addr] using h.load_pmp.subaccess (offset := 0) (accessWidth := 8) (by omega)
  have hstore_pmp : Assumptions.StorePmpOk addr 8 js.sail := by
    simpa [addr] using h.store_pmp.subaccess (offset := 0) (accessWidth := 8) (by omega)
  have hatomic_pmp : Assumptions.AtomicPmpOk amoop.AMOADD addr 8 js.sail := by
    simpa [addr] using h.atomic_pmp.subaccess (offset := 0) (accessWidth := 8) (by omega)
  have hread_mmio : Assumptions.NotReadableMmio addr 8 js.sail := by
    simpa [addr] using h.not_readable_mmio.subaccess (offset := 0) (accessWidth := 8) (by omega)
  have hwrite_mmio : Assumptions.NotWritableMmio addr 8 js.sail := by
    simpa [addr] using h.not_writable_mmio.subaccess (offset := 0) (accessWidth := 8) (by omega)
  change
    projectResult ((JoltISA.execProgram
      (JoltISA.amoDoubleBinopProgram
        (fun dst lhs rhs => .ADD dst lhs rhs) rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOADD false false rs2 rs1 8 rd).run js.sail
  by_cases h_align : addr &&& (7 : BitVec 64) = 0
  · exact
      amo_dword_double_binop_program_eq_sail_aligned
        amoop.AMOADD (fun dst lhs rhs => .ADD dst lhs rhs)
        rs2 rs1 rd js h.cur_privilege h.mstatus_mprv addr rs2Val
        (rs2Val + loaded_dword_at js.sail addr hbytes
          (amo_dword_aligned_no_ovf addr h_align))
        h.rs1_read h.rs2_read h.rdReadable.exists_value
        hbytes hload_pmp hstore_pmp hatomic_pmp hread_mmio hwrite_mmio
        h_align (by decide)
        (amo_dword_add_middle_after_load_into rs2 js addr rs2Val
          (loaded_dword_at js.sail addr hbytes
            (amo_dword_aligned_no_ovf addr h_align))
          h.rs2_read)
        (amoaddd_sail_result rs2Val
          (loaded_dword_at js.sail addr hbytes
            (amo_dword_aligned_no_ovf addr h_align)))
  · exact
      amo_dword_double_binop_program_eq_sail_misaligned
        amoop.AMOADD (fun dst lhs rhs => .ADD dst lhs rhs)
        rs2 rs1 rd js addr rs2Val h.rs1_read h.rs2_read h_align

/-- Main public theorem for `AMOADD.D`.

The theorem takes one primitive-only atomic bundle, matches Sail, and preserves
every protected Jolt register on successful runs. -/
def amoadddProgramEqSailStatement
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (_h : AmoDwordProgramEqSailAssumptions amoop.AMOADD rs2 rs1 rd js) : Prop :=
  System.systemProjectResult
      ((JoltISA.execProgram
        (JoltISA.amoadddProgramAuto rd rs1 rs2)).run js) =
    (execute_AMO amoop.AMOADD false false rs2 rs1 8 rd).run js.sail

theorem amoadddProgram_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoDwordProgramEqSailAssumptions amoop.AMOADD rs2 rs1 rd js) :
    amoadddProgramEqSailStatement rs2 rs1 rd js h := by
  unfold amoadddProgramEqSailStatement
  rw [← JoltISA.amoaddd_auto_eq rs2 rs1 rd]
  rw [System.systemProjectResult_execProgram_eq_projectResult
    (JoltISA.amoadddProgram rs2 rs1 rd) js h.linkedCSRs
    (amoadddProgram_doesNotWriteProtectedVRegs rs2 rs1 rd)]
  exact amoadddProgram_project_eq_sail rs2 rs1 rd js h

end AtomicFamily

end
