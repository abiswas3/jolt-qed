import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Word

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions
open virtaddr

set_option autoImplicit true

noncomputable section

namespace AtomicFamily

/-- Sail's generated `AMOADD.W` result expression reduces to word addition. -/
theorem amoaddw_sail_result (rs2Val : BitVec 64) (loaded : BitVec 32) :
    amoWordSailResult amoop.AMOADD
      (show BitVec (4 * 8) from
        trunc (m := (((4 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
      (BitVec.setWidth (4 * 8) loaded) =
    (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32) + loaded := by
  rw [amo_word_trunc_4x8_eq_extract]
  rw [amo_word_setWidth_4x8_eq_self]

/-- Main public theorem for `AMOADD.W`.

The theorem takes one primitive-only atomic bundle. Exact memory facts are
derived internally from that bundle. -/
private theorem amoaddwProgram_project_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoWordProgramEqSailAssumptions amoop.AMOADD rs2 rs1 rd js) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoaddwProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOADD false false rs2 rs1 4 rd).run js.sail := by
  let addr := h.rs1_val
  let rs2Val := h.rs2_val
  change
    projectResult ((JoltISA.execProgram
      (JoltISA.amoWordBinopProgram
        (fun dst lhs rhs => .ADD dst lhs rhs) rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOADD false false rs2 rs1 4 rd).run js.sail
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
    have hatomic_pmp_word : Assumptions.AtomicPmpOk amoop.AMOADD addr 4 js.sail := by
      have hsub :
          Assumptions.AtomicPmpOk amoop.AMOADD
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
        amo_word_binop_program_concrete_aligned
          amoop.AMOADD (fun dst lhs rhs => .ADD dst lhs rhs)
          rs2 rs1 rd js h.cur_privilege h.mstatus_mprv addr
          (rs2Val + amoWordShiftedOld addr dword)
          ((Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32) + oldWord)
          h.rs1_read hbytes_base hload_pmp_base hread_mmio_base
          hstore_pmp_base hwrite_mmio_base h_align
          (amo_word_add_result_extract_eq addr rs2Val dword oldWord hold)
          (amo_word_add_middle_after_pre rs2 js rs2Val dword
            (amoWordShiftedOld addr dword)
            (shift_bits_left addr (3 : BitVec 6)) h.rs2_read) with
      ⟨jsf, hjolt, hjolt_sail⟩
    have hsail :=
      execute_AMO_word_non_cas_aligned
        amoop.AMOADD rs2 rs1 rd js h.cur_privilege h.mstatus_mprv
        addr rs2Val
        ((Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32) + oldWord)
        h.rs1_read h.rs2_read h.rdReadable.exists_value
        hbytes_word hatomic_pmp_word hread_mmio_word hwrite_mmio_word
        h_align (by decide) (amoaddw_sail_result rs2Val oldWord)
    rw [hjolt]
    simp only [projectResult, project]
    rw [hjolt_sail, hsail, hold]
  · have hjolt :
        (JoltISA.execProgram
          (JoltISA.amoWordBinopProgram
            (fun dst lhs rhs => .ADD dst lhs rhs) rs2 rs1 rd)).run js =
          .ok (ExecutionResult.Memory_Exception
            (Virtaddr addr, ExceptionType.E_SAMO_Addr_Align ())) js := by
      unfold JoltISA.amoWordBinopProgram
      exact
        amo_word_pre64_misaligned_run rs1 JoltISA.amoOldVReg
          JoltISA.amoDwordVReg JoltISA.amoShiftVReg
          (.instr (.ADD (.vreg JoltISA.amoNewVReg)
            (.vreg JoltISA.amoOldVReg) (.xreg rs2)) <|
            JoltISA.amoPost64Program rs1 rd (.vreg JoltISA.amoNewVReg)
              JoltISA.amoDwordVReg JoltISA.amoShiftVReg
              JoltISA.amoMaskVReg JoltISA.amoOldVReg)
          js addr h.rs1_read h_align
    have hsail :=
      execute_AMO_word_misaligned
        amoop.AMOADD rs2 rs1 rd js addr rs2Val
        h.rs1_read h.rs2_read h_align
    rw [hjolt]
    simp only [projectResult, project]
    symm
    exact hsail

/-- Main public theorem for `AMOADD.W`. -/
def amoaddwProgramEqSailStatement
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (_h : AmoWordProgramEqSailAssumptions amoop.AMOADD rs2 rs1 rd js) : Prop :=
  ProgramMatchesSailWithProtectedFrame js
    ((JoltISA.execProgram (JoltISA.amoaddwProgram rs2 rs1 rd)).run js)
    ((execute_AMO amoop.AMOADD false false rs2 rs1 4 rd).run js.sail)

theorem amoaddwProgram_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoWordProgramEqSailAssumptions amoop.AMOADD rs2 rs1 rd js) :
    amoaddwProgramEqSailStatement rs2 rs1 rd js h := by
  apply programMatchesSailWithProtectedFrame_of_projectResult_eq
  · exact amoaddwProgram_project_eq_sail rs2 rs1 rd js h
  · simp [JoltISA.amoaddwProgram, JoltISA.amoWordBinopProgram,
      JoltISA.amoPre64Program, JoltISA.amoPre64ProgramWithScratch,
      JoltISA.amoPost64Program, JoltISA.amoPost64ProgramWithScratch,
      JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg,
      JoltISA.DstWritesNoProtectedVReg,
      JoltISA.amoOldVReg, JoltISA.amoNewVReg, JoltISA.amoMaskVReg,
      JoltISA.amoDwordVReg, JoltISA.amoShiftVReg, JoltISA.amoInlineTmpVReg]

end AtomicFamily

end
