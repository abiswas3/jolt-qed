import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.WordSelectRust

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions
open virtaddr

set_option autoImplicit true

noncomputable section

namespace AtomicFamily

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

/-- Main public theorem for `AMOMINU.W`.

The theorem takes one primitive-only atomic bundle. Exact memory facts are
derived internally from that bundle. -/
private theorem amominuwProgram_project_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoWordProgramEqSailAssumptions amoop.AMOMINU rs2 rs1 rd js) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amominuwProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOMINU false false rs2 rs1 4 rd).run js.sail := by
  let addr := h.rs1_val
  let rs2Val := h.rs2_val
  change
    projectResult ((JoltISA.execProgram
      (JoltISA.amoWordSelectRustProgram
        (fun dst src => .VirtualZeroExtendWord dst src)
        (fun dst lhs rhs => .SLTU dst lhs rhs)
        (.vreg JoltISA.amoWordSelectNewVReg)
        (.vreg JoltISA.amoWordSelectMaskVReg)
        rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOMINU false false rs2 rs1 4 rd).run js.sail
  by_cases h_align : addr &&& (3 : BitVec 64) = 0
  · let base := amoWordBase addr
    let offset := (addr &&& (7 : BitVec 64)).toNat
    have hbase_no_ovf := amo_word_base_no_ovf addr
    have hbytes_base : MemBytesPresentAt js.sail (amoWordBase addr) 8 := by
      simpa [addr] using Assumptions.DwordPresent.memBytesPresentAt h.dword_present
    have hload_pmp_base : Assumptions.LoadPmpOk (amoWordBase addr) 8 js.sail := by
      simpa [addr] using h.load_pmp.subaccess (offset := 0) (accessWidth := 8) (by omega)
    have hstore_pmp_base : Assumptions.StorePmpOk (amoWordBase addr) 8 js.sail := by
      simpa [addr] using h.store_pmp.subaccess (offset := 0) (accessWidth := 8) (by omega)
    have hread_mmio_base :
        Assumptions.NotReadableMmio (amoWordBase addr) 8 js.sail := by
      simpa [addr] using
        h.not_readable_mmio.subaccess (offset := 0) (accessWidth := 8) (by omega)
    have hwrite_mmio_base :
        Assumptions.NotWritableMmio (amoWordBase addr) 8 js.sail := by
      simpa [addr] using
        h.not_writable_mmio.subaccess (offset := 0) (accessWidth := 8) (by omega)
    have hoff : offset + 4 ≤ 8 := by
      have hcases := write_word_offset_cases addr h_align
      rcases hcases with h0 | h4
      · simp [offset, h0]
      · simp [offset, h4]
    have haddr : base + BitVec.ofNat 64 offset = addr := by
      simpa [base, offset, amoWordBase] using addr_split_aligned_offset addr
    have hbytes_word : MemBytesPresentAt js.sail addr 4 := by
      have hsub : MemBytesPresentAt js.sail (base + BitVec.ofNat 64 offset) 4 :=
        memBytesPresentAt_subaccess (s := js.sail) (base := base) (baseWidth := 8)
          (offset := offset) (accessWidth := 4)
          (by simpa [base] using hbytes_base) hoff (by
            have hb : base.toNat + 7 < 2 ^ 64 := by
              simpa [base] using hbase_no_ovf
            omega)
      simpa [haddr] using hsub
    have hatomic_pmp_word : Assumptions.AtomicPmpOk amoop.AMOMINU addr 4 js.sail := by
      have hsub :
          Assumptions.AtomicPmpOk amoop.AMOMINU
            (base + BitVec.ofNat 64 offset) 4 js.sail :=
        h.atomic_pmp.subaccess (offset := offset) (accessWidth := 4) hoff
      simpa [addr, base, haddr] using hsub
    have hread_mmio_word : Assumptions.NotReadableMmio addr 4 js.sail := by
      have hsub :
          Assumptions.NotReadableMmio (base + BitVec.ofNat 64 offset) 4 js.sail :=
        h.not_readable_mmio.subaccess (offset := offset) (accessWidth := 4) hoff
      simpa [addr, base, haddr] using hsub
    have hwrite_mmio_word : Assumptions.NotWritableMmio addr 4 js.sail := by
      have hsub :
          Assumptions.NotWritableMmio (base + BitVec.ofNat 64 offset) 4 js.sail :=
        h.not_writable_mmio.subaccess (offset := offset) (accessWidth := 4) hoff
      simpa [addr, base, haddr] using hsub
    have h_word_no_ovf : addr.toNat + 3 < 2 ^ 64 :=
      amo_word_aligned_no_ovf addr hbase_no_ovf h_align
    let dword : BitVec 64 :=
      loaded_dword_at js.sail (amoWordBase addr) hbytes_base hbase_no_ovf
    let oldWord : BitVec 32 := loaded_word_at js.sail addr hbytes_word h_word_no_ovf
    have hold :
        (Sail.BitVec.extractLsb (amoWordShiftedOld addr dword) 31 0 :
          BitVec 32) = oldWord := by
      have hword_of_dword :
          (Sail.BitVec.extractLsb (amoWordShiftedOld addr dword) 31 0 :
            BitVec 32) =
          word_of_dword dword (addr &&& (7 : BitVec 64)).toNat := by
        apply amo_word_sign_extend_64_injective
        simpa [amoWordShiftedOld] using
          srl_sign_extend_word_extracts_word dword addr h_align
      have hloaded :
          oldWord = word_of_dword dword (addr &&& (7 : BitVec 64)).toNat := by
        unfold oldWord dword
        simpa [amoWordBase] using
          loaded_word_in_dword js.sail addr h_align
            hbytes_base hbase_no_ovf hbytes_word h_word_no_ovf
      rw [hword_of_dword, ← hloaded]
    rcases
        amo_word_rust_select_program_concrete_aligned
          amoop.AMOMINU
          (fun dst src => .VirtualZeroExtendWord dst src)
          (fun dst lhs rhs => .SLTU dst lhs rhs)
          (.vreg JoltISA.amoWordSelectNewVReg)
          (.vreg JoltISA.amoWordSelectMaskVReg)
          rs2 rs1 rd js h.cur_privilege h.mstatus_mprv addr
          (if (zopz0zI_u
              (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
              (Sail.BitVec.extractLsb (amoWordShiftedOld addr dword) 31 0 :
                BitVec 32) : Bool) then
            rs2Val
          else
            amoWordShiftedOld addr dword)
          (if (zopz0zI_u
              (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
              oldWord : Bool) then
            (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
          else
            oldWord)
          oldWord
          h.rs1_read hbytes_base hload_pmp_base hread_mmio_base
          hstore_pmp_base hwrite_mmio_base h_align
          (amo_word_minu_result_extract_eq rs2Val (amoWordShiftedOld addr dword)
            oldWord hold)
          (by simpa [dword] using hold)
          (amo_word_rust_select_minu_middle_after_pre rs2 js addr rs2Val dword
            h.rs2_read) with
      ⟨jsf, hjolt, hjolt_sail⟩
    have hsail :=
      execute_AMO_word_non_cas_aligned
        amoop.AMOMINU rs2 rs1 rd js h.cur_privilege h.mstatus_mprv
        addr rs2Val
        (if (zopz0zI_u
            (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
            oldWord : Bool) then
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
        else
          oldWord)
        h.rs1_read h.rs2_read h.rdReadable.exists_value
        hbytes_word hatomic_pmp_word hread_mmio_word hwrite_mmio_word
        h_align (by decide) (amominuw_sail_result rs2Val oldWord)
    rw [hjolt]
    simp only [projectResult, project]
    rw [hjolt_sail, hsail]
  · have hjolt :
        (JoltISA.execProgram
          (JoltISA.amoWordSelectRustProgram
            (fun dst src => .VirtualZeroExtendWord dst src)
            (fun dst lhs rhs => .SLTU dst lhs rhs)
            (.vreg JoltISA.amoWordSelectNewVReg)
            (.vreg JoltISA.amoWordSelectMaskVReg)
            rs2 rs1 rd)).run js =
          .ok (ExecutionResult.Memory_Exception
            (Virtaddr addr, ExceptionType.E_SAMO_Addr_Align ())) js := by
      exact
        amo_word_rust_select_program_concrete_misaligned
          (fun dst src => .VirtualZeroExtendWord dst src)
          (fun dst lhs rhs => .SLTU dst lhs rhs)
          (.vreg JoltISA.amoWordSelectNewVReg)
          (.vreg JoltISA.amoWordSelectMaskVReg)
          rs2 rs1 rd js addr h.rs1_read h_align
    have hsail :=
      execute_AMO_word_misaligned
        amoop.AMOMINU rs2 rs1 rd js addr rs2Val
        h.rs1_read h.rs2_read h_align
    rw [hjolt]
    simp only [projectResult, project]
    symm
    exact hsail

/-- Main public theorem for `AMOMINU.W`. -/
def amominuwProgramEqSailStatement
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (_h : AmoWordProgramEqSailAssumptions amoop.AMOMINU rs2 rs1 rd js) : Prop :=
  ProgramMatchesSailWithProtectedFrame js
    ((JoltISA.execProgram (JoltISA.amominuwProgram rs2 rs1 rd)).run js)
    ((execute_AMO amoop.AMOMINU false false rs2 rs1 4 rd).run js.sail)

theorem amominuwProgram_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoWordProgramEqSailAssumptions amoop.AMOMINU rs2 rs1 rd js) :
    amominuwProgramEqSailStatement rs2 rs1 rd js h := by
  apply programMatchesSailWithProtectedFrame_of_projectResult_eq
  · exact amominuwProgram_project_eq_sail rs2 rs1 rd js h
  · simp [JoltISA.amominuwProgram, JoltISA.amoWordSelectRustProgram,
      JoltISA.amoPre64ProgramWithScratch,
      JoltISA.amoPost64ProgramWithScratch,
      JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg,
      JoltISA.DstWritesNoProtectedVReg,
      JoltISA.amoWordSelectOldVReg, JoltISA.amoWordSelectDwordVReg,
      JoltISA.amoWordSelectShiftVReg, JoltISA.amoWordSelectNewVReg,
      JoltISA.amoWordSelectMaskVReg, JoltISA.amoWordSelectInlineTmpVReg]

end AtomicFamily

end
