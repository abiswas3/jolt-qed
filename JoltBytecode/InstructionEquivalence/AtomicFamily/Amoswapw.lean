import JoltBytecode.InstructionEquivalence.AtomicFamily.Word

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace AtomicFamily

/-- Sail's generated top-level width assertion succeeds for `AMOSWAP.W`. -/
theorem amoswapw_width_assert_true :
    (4 ≤b (((8 : Nat) : Int) * (2 : Int)).toNat) = true := by
  decide

/-- Jolt-side aligned concrete execution for `AMOSWAP.W`.

The shared word prelude extracts the old word from the containing dword; the
AMOSWAP postlude splices `rs2[31:0]` back into that lane and writes the old
word to `rd`. -/
theorem amoswapwProgram_concrete_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_mem : AmoMemoryAssumptions amoop.AMOSWAP 4
      (amoWordBase addr) addr js.sail)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    ∃ jsf : SailJoltState,
      (JoltISA.execProgram (JoltISA.amoswapwProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail =
        amoWordFinalSailState rd js.sail addr
          (Sail.BitVec.extractLsb rs2Val 31 0) := by
  have h_no_ovf := amo_word_base_no_ovf addr
  let post :=
    JoltISA.amoPost64Program rs1 rd (.xreg rs2)
      JoltISA.amoDwordVReg JoltISA.amoShiftVReg
      JoltISA.amoMaskVReg JoltISA.amoOldVReg
  obtain ⟨js_pre, hpre_run, hpre_sail, hpre_dword, hpre_shift, hpre_old⟩ :=
    amo_word_pre64_aligned_run post rs1 js hcfg addr hrs1 h_mem
      h_no_ovf h_align
  obtain ⟨jsf, hpost_run, hpost_sail⟩ :=
    amo_word_post64_amoswap_aligned_run rs2 rs1 rd js js_pre hcfg
      addr rs2Val hrs1 hrs2 h_mem h_no_ovf h_align hpre_sail
      hpre_dword hpre_shift hpre_old
  refine ⟨jsf, ?_, hpost_sail⟩
  unfold JoltISA.amoswapwProgram
  rw [hpre_run]
  exact hpost_run

/-- The generated `AMOSWAP.W` store payload is the low 32 bits of `rs2`. -/
theorem amoswapw_store_data_eq (rs2Val : BitVec 64) :
    sign_extend (m := ((8 : Int) * ((4 : Nat) : Int)).toNat)
      (show BitVec (4 * 8) from
        trunc (m := (((4 : Nat) : Int) * (8 : Int)).toNat) rs2Val) =
    (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32) := by
  unfold trunc Sail.BitVec.truncate sign_extend Sail.BitVec.signExtend
    Sail.BitVec.extractLsb
  bv_decide

/-- Sail writes the low word of `rs2` for aligned native `AMOSWAP.W`. -/
theorem amoswapw_mem_write_value_eq_state_after_word_store
    (addr rs2Val : BitVec 64) (s : SailState)
    (hcfg : JoltConfig s)
    (h_align : addr &&& (3 : BitVec 64) = 0)
    (hfm : FlatAtomicMem amoop.AMOSWAP addr 4 s) :
    mem_write_value (physaddr.Physaddr addr) 4
      (sign_extend (m := ((8 : Int) * ((4 : Nat) : Int)).toNat)
        (show BitVec (4 * 8) from
          trunc (m := (((4 : Nat) : Int) * (8 : Int)).toNat) rs2Val))
      (Atomic (amoop.AMOSWAP, Data, Data)) false false true s =
    .ok (Ok true)
      (state_after_word_store s addr
        (Sail.BitVec.extractLsb rs2Val 31 0)) := by
  rw [amoswapw_store_data_eq rs2Val]
  exact
    amo_word_mem_write_value_eq_state_after_word_store
      amoop.AMOSWAP addr (Sail.BitVec.extractLsb rs2Val 31 0)
      s hcfg h_align hfm

/-- The generated Sail old-word writeback cast is the canonical AMOSWAP.W
writeback value. -/
theorem amoswapw_writeback_loaded_direct
    (rd : regidx) (s writebackState : SailState)
    (addr : BitVec 64) (result : BitVec 32)
    (hwriteback :
      wX_bits rd (sign_extend (m := 64) (loaded_word_at s addr))
        (state_after_word_store s addr result) =
        .ok () writebackState) :
    wX_bits rd
      (sign_extend (m := 64)
        (BitVec.setWidth (4 * 8) (loaded_word_at s addr)))
      (state_after_word_store s addr result) =
      .ok () writebackState := by
  rw [amo_word_setWidth_4x8_eq_self]
  exact hwriteback

/-- Sail-side aligned concrete execution for native `AMOSWAP.W`. -/
theorem execute_AMOSWAPW_reduces_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryAssumptions amoop.AMOSWAP 4
      (amoWordBase addr) addr js.sail)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    (execute_AMO amoop.AMOSWAP false false rs2 rs1 4 rd).run js.sail =
      .ok RETIRE_SUCCESS
        (amoWordFinalSailState rd js.sail addr
          (Sail.BitVec.extractLsb rs2Val 31 0)) := by
  let result : BitVec 32 := Sail.BitVec.extractLsb rs2Val 31 0
  have h_no_ovf := amo_word_base_no_ovf addr
  obtain ⟨rdVal, hrd_read⟩ := hrd
  obtain ⟨writebackState, hwriteback, hwriteback_state⟩ :=
    amo_word_writeback_old_shape rd js.sail addr result
  have haddr0 : addr + zeros (n := 64) = addr := by
    unfold zeros
    exact BitVec.add_zero addr
  have h_vaddr_aligned := amo_word_is_aligned_vaddr_true addr h_align
  have htranslate :=
    translateAddr_atomic_data_of_joltConfig amoop.AMOSWAP addr js.sail hcfg
  have hea := amo_word_mem_write_ea_ok addr js.sail h_align
  have hread :=
    amo_word_mem_read_eq_loaded_word amoop.AMOSWAP addr js.sail hcfg
      (amo_word_aligned_no_ovf addr h_no_ovf h_align)
      h_align h_mem.sail_atomic_mem
  have hwrite_value :=
    amoswapw_mem_write_value_eq_state_after_word_store
      addr rs2Val js.sail hcfg h_align h_mem.sail_atomic_mem
  have hwriteback_direct :=
    amoswapw_writeback_loaded_direct
      rd js.sail writebackState addr result hwriteback
  have hwriteback_direct_expanded :
      wX_bits rd
        (sign_extend (m := 64)
          (BitVec.setWidth (4 * 8) (loaded_word_at js.sail addr)))
        (state_after_word_store js.sail addr
          (Sail.BitVec.extractLsb rs2Val 31 0)) =
      .ok () writebackState := by
    exact hwriteback_direct
  have hcas_check :
      decide (amoop.AMOSWAP.ctorIdx = amoop.AMOCAS.ctorIdx) = false := by
    decide
  unfold execute_AMO
  simp only [bind, pure]
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  simp only [amoswapw_width_assert_true, PreSail.assert, pure, EStateM.run,
    if_true]
  unfold SailME.run PreSail.PreSailME.run
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    ExceptT.pure, ExceptT.lift, MonadLift.monadLift, liftM, monadLift,
    Functor.map, SailME.throw, PreSail.PreSailME.throw,
    MonadExceptOf.throw, ext_data_get_addr, hrs1, haddr0,
    h_vaddr_aligned, LeanRV64D.Functions.not, Bool.not_true,
    Bool.false_eq_true, if_false, if_true, htranslate,
    amo_word_width4_true, hrs2, hea, hread, hrd_read, hcas_check,
    Bool.false_and, instBEqAmoop.beq, BEq.beq]
  rw [hwrite_value]
  simp only [EStateM.bind, EStateM.map, ExceptT.bindCont]
  rw [hwriteback_direct_expanded]
  rw [hwriteback_state]
  simp only [EStateM.pure]
  rfl

theorem amoswapwProgram_eq_sail_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryAssumptions amoop.AMOSWAP 4
      (amoWordBase addr) addr js.sail)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoswapwProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOSWAP false false rs2 rs1 4 rd).run js.sail := by
  rcases amoswapwProgram_concrete_aligned
      rs2 rs1 rd js hcfg addr rs2Val hrs1 hrs2 h_mem h_align with
    ⟨jsf, hjolt, hjolt_sail⟩
  have hsail :=
    execute_AMOSWAPW_reduces_aligned
      rs2 rs1 rd js hcfg addr rs2Val hrs1 hrs2 hrd h_mem h_align
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail, hsail]

/-- Jolt-side misaligned execution for `AMOSWAP.W`.

The shared word prelude performs the leading AMO word-alignment check, so the
postlude is skipped on this path. -/
theorem amoswapwProgram_concrete_misaligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (addr : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (h_align : addr &&& (3 : BitVec 64) ≠ 0) :
    (JoltISA.execProgram (JoltISA.amoswapwProgram rs2 rs1 rd)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr addr, ExceptionType.E_SAMO_Addr_Align ())) js := by
  unfold JoltISA.amoswapwProgram
  exact
    amo_word_pre64_misaligned_run rs1 JoltISA.amoOldVReg
      JoltISA.amoDwordVReg JoltISA.amoShiftVReg
      (JoltISA.amoPost64Program rs1 rd (.xreg rs2)
        JoltISA.amoDwordVReg JoltISA.amoShiftVReg
        JoltISA.amoMaskVReg JoltISA.amoOldVReg)
      js addr hrs1 h_align

/-- Sail-side misaligned execution for native `AMOSWAP.W`. -/
theorem execute_AMOSWAPW_misaligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_align : addr &&& (3 : BitVec 64) ≠ 0) :
    (execute_AMO amoop.AMOSWAP false false rs2 rs1 4 rd).run js.sail =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr addr, ExceptionType.E_SAMO_Addr_Align ())) js.sail := by
  exact
    execute_AMO_word_misaligned
      amoop.AMOSWAP rs2 rs1 rd js hcfg addr rs2Val hrs1 hrs2 h_align

/-- Misaligned public branch for `AMOSWAP.W`. -/
theorem amoswapwProgram_eq_sail_misaligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_align : addr &&& (3 : BitVec 64) ≠ 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoswapwProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOSWAP false false rs2 rs1 4 rd).run js.sail := by
  have hjolt := amoswapwProgram_concrete_misaligned
    rs2 rs1 rd js addr hrs1 h_align
  have hsail := execute_AMOSWAPW_misaligned
    rs2 rs1 rd js hcfg addr rs2Val hrs1 hrs2 h_align
  rw [hjolt]
  simp only [projectResult, project]
  symm
  exact hsail

/-- Main public theorem for `AMOSWAP.W`.

The theorem exposes the same alignment split as the load/store families:
aligned addresses use the full memory assumptions, while misaligned addresses
stop at both interpreters' leading alignment check. -/
theorem amoswapwProgram_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryAssumptions amoop.AMOSWAP 4
      (amoWordBase addr) addr js.sail) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoswapwProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOSWAP false false rs2 rs1 4 rd).run js.sail := by
  by_cases h_align : addr &&& (3 : BitVec 64) = 0
  · exact amoswapwProgram_eq_sail_aligned
      rs2 rs1 rd js hcfg addr rs2Val hrs1 hrs2 hrd h_mem h_align
  · exact amoswapwProgram_eq_sail_misaligned
      rs2 rs1 rd js hcfg addr rs2Val hrs1 hrs2 h_align

end AtomicFamily

end
