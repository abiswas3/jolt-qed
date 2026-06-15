import JoltBytecode.InstructionEquivalence.AtomicFamily.Word



set_option linter.unusedVariables false



open Sail PreSail LeanRV64D.Functions

open virtaddr MemoryAccessType mem_payload



set_option autoImplicit true



noncomputable section



namespace AtomicFamily



/-!

# Rust-shaped word select AMO helpers



These helper lemmas mirror the Rust allocator order for RV64 word min/max atomics.

-/

theorem amo_word_rust_select_pre64_aligned_run
    {op : amoop} (tail : JoltISA.Program)
    (rs1 : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (h_mem : AmoMemoryContext op 4 (amoWordBase addr) addr js.sail)
    (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    ∃ js_pre : SailJoltState,
      (JoltISA.execProgram
        (JoltISA.amoPre64ProgramWithScratch rs1 JoltISA.amoWordSelectOldVReg
          JoltISA.amoWordSelectDwordVReg JoltISA.amoWordSelectShiftVReg
          JoltISA.amoWordSelectNewVReg tail)).run js =
        (JoltISA.execProgram tail).run js_pre ∧
      js_pre.sail = js.sail ∧
      js_pre.vregs JoltISA.amoWordSelectDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr) ∧
      js_pre.vregs JoltISA.amoWordSelectShiftVReg =
        shift_bits_left addr (3 : BitVec 6) ∧
      js_pre.vregs JoltISA.amoWordSelectOldVReg =
        shift_bits_right
          (loaded_dword_at js.sail (amoWordBase addr))
          (Sail.BitVec.extractLsb
            (shift_bits_left addr (3 : BitVec 6)) 5 0) := by
  have hassert :=
    amo_word_virtual_assert_aligned_run rs1 js addr hrs1 h_align
  obtain ⟨js_base, _hrs1_base, hbase_sail, hbase_shift_raw,
      _hbase_preserves, hbase_run⟩ :=
    JoltISA.exists_state_after_andi_run_vreg_xreg_of_sail_eq
      JoltISA.amoWordSelectShiftVReg rs1 (-8 : BitVec 12) js js.sail addr rfl hrs1
  have hbase_shift :
      js_base.vregs JoltISA.amoWordSelectShiftVReg = amoWordBase addr := by
    rw [hbase_shift_raw]
    exact amo_word_base_mask addr
  have hcfg_base : JoltConfig js_base.sail := by
    rw [hbase_sail]
    exact hcfg
  have hload_evidence :
      DwordLoadEvidence (amoWordBase addr) js_base.sail := by
    rw [hbase_sail]
    exact
      dwordLoadEvidence_of_aligned_phys (amoWordBase addr) js.sail
        (amo_word_base_aligned_access addr h_no_ovf)
        (AmoMemoryContext.jolt_load_mem h_mem)
  have hld :
      (JoltISA.execInstr
        (.LD (.vreg JoltISA.amoWordSelectDwordVReg)
          (.vreg JoltISA.amoWordSelectShiftVReg) (0 : BitVec 12))).run js_base =
        .ok RETIRE_SUCCESS
          { sail := js_base.sail
            vregs := fun r =>
              if r = JoltISA.amoWordSelectDwordVReg then
                loaded_dword_at js_base.sail (amoWordBase addr)
              else js_base.vregs r } := by
    exact
      vreg_LD_run_of_dword_evidence
        JoltISA.amoWordSelectDwordVReg JoltISA.amoWordSelectShiftVReg js_base
        (amoWordBase addr) hbase_shift hcfg_base hload_evidence
  let js_load : SailJoltState :=
    { sail := js_base.sail
      vregs := fun r =>
        if r = JoltISA.amoWordSelectDwordVReg then
          loaded_dword_at js_base.sail (amoWordBase addr)
        else js_base.vregs r }
  have hld_named :
      (JoltISA.execInstr
        (.LD (.vreg JoltISA.amoWordSelectDwordVReg)
          (.vreg JoltISA.amoWordSelectShiftVReg) (0 : BitVec 12))).run js_base =
        .ok RETIRE_SUCCESS js_load := by
    exact hld
  have hload_sail : js_load.sail = js.sail := by
    exact hbase_sail
  have hload_dword :
      js_load.vregs JoltISA.amoWordSelectDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr) := by
    change
      (if JoltISA.amoWordSelectDwordVReg = JoltISA.amoWordSelectDwordVReg then
          loaded_dword_at js_base.sail (amoWordBase addr)
        else js_base.vregs JoltISA.amoWordSelectDwordVReg) =
        loaded_dword_at js.sail (amoWordBase addr)
    rw [if_pos rfl, hbase_sail]
  have hload_shift :
      js_load.vregs JoltISA.amoWordSelectShiftVReg = amoWordBase addr := by
    change
      (if JoltISA.amoWordSelectShiftVReg = JoltISA.amoWordSelectDwordVReg then
          loaded_dword_at js_base.sail (amoWordBase addr)
        else js_base.vregs JoltISA.amoWordSelectShiftVReg) =
        amoWordBase addr
    rw [if_neg (by decide)]
    exact hbase_shift
  have hrs1_load :
      rX_bits rs1 js_load.sail = .ok addr js_load.sail := by
    rw [hload_sail]
    exact hrs1
  have hmuli :
      (JoltISA.execInstr
        (.VirtualMULI (.vreg JoltISA.amoWordSelectShiftVReg)
          (.xreg rs1) (8 : BitVec 64))).run js_load =
      .ok RETIRE_SUCCESS
        { sail := js_load.sail
          vregs := fun r =>
            if r = JoltISA.amoWordSelectShiftVReg then
              jolt_virtual_muli_value addr (8 : BitVec 64)
            else js_load.vregs r } :=
    amo_word_virtual_muli_run_vreg_xreg
      JoltISA.amoWordSelectShiftVReg rs1 (8 : BitVec 64) js_load addr hrs1_load
  let js_shift : SailJoltState :=
    { sail := js_load.sail
      vregs := fun r =>
        if r = JoltISA.amoWordSelectShiftVReg then
          jolt_virtual_muli_value addr (8 : BitVec 64)
        else js_load.vregs r }
  have hmuli_named :
      (JoltISA.execInstr
        (.VirtualMULI (.vreg JoltISA.amoWordSelectShiftVReg)
          (.xreg rs1) (8 : BitVec 64))).run js_load =
      .ok RETIRE_SUCCESS js_shift := by
    exact hmuli
  have hshift_sail : js_shift.sail = js.sail := by
    exact hload_sail
  have hshift_dword :
      js_shift.vregs JoltISA.amoWordSelectDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr) := by
    change
      (if JoltISA.amoWordSelectDwordVReg = JoltISA.amoWordSelectShiftVReg then
          jolt_virtual_muli_value addr (8 : BitVec 64)
        else js_load.vregs JoltISA.amoWordSelectDwordVReg) =
        loaded_dword_at js.sail (amoWordBase addr)
    rw [if_neg (by decide)]
    exact hload_dword
  have hshift_shift :
      js_shift.vregs JoltISA.amoWordSelectShiftVReg =
        shift_bits_left addr (3 : BitVec 6) := by
    change
      (if JoltISA.amoWordSelectShiftVReg = JoltISA.amoWordSelectShiftVReg then
          jolt_virtual_muli_value addr (8 : BitVec 64)
        else js_load.vregs JoltISA.amoWordSelectShiftVReg) =
        shift_bits_left addr (3 : BitVec 6)
    rw [if_pos rfl]
    exact JoltISA.virtual_muli_eight_eq_shift_left_three addr
  have hbitmask :
      (JoltISA.execInstr
        (.VirtualShiftRightBitmask (.vreg JoltISA.amoWordSelectNewVReg)
          (.vreg JoltISA.amoWordSelectShiftVReg))).run js_shift =
      .ok RETIRE_SUCCESS
        { sail := js_shift.sail
          vregs := fun r =>
            if r = JoltISA.amoWordSelectNewVReg then
              jolt_virtual_shift_right_bitmask_value
                (js_shift.vregs JoltISA.amoWordSelectShiftVReg)
            else js_shift.vregs r } :=
    JoltISA.virtual_shift_right_bitmask_run_vreg_vreg
      JoltISA.amoWordSelectNewVReg JoltISA.amoWordSelectShiftVReg js_shift
  let js_bitmask : SailJoltState :=
    { sail := js_shift.sail
      vregs := fun r =>
        if r = JoltISA.amoWordSelectNewVReg then
          jolt_virtual_shift_right_bitmask_value
            (js_shift.vregs JoltISA.amoWordSelectShiftVReg)
        else js_shift.vregs r }
  have hbitmask_named :
      (JoltISA.execInstr
        (.VirtualShiftRightBitmask (.vreg JoltISA.amoWordSelectNewVReg)
          (.vreg JoltISA.amoWordSelectShiftVReg))).run js_shift =
      .ok RETIRE_SUCCESS js_bitmask := by
    exact hbitmask
  have hbitmask_sail : js_bitmask.sail = js.sail := by
    exact hshift_sail
  have hbitmask_dword :
      js_bitmask.vregs JoltISA.amoWordSelectDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr) := by
    change
      (if JoltISA.amoWordSelectDwordVReg = JoltISA.amoWordSelectNewVReg then
          jolt_virtual_shift_right_bitmask_value
            (js_shift.vregs JoltISA.amoWordSelectShiftVReg)
        else js_shift.vregs JoltISA.amoWordSelectDwordVReg) =
        loaded_dword_at js.sail (amoWordBase addr)
    rw [if_neg (by decide)]
    exact hshift_dword
  have hbitmask_shift :
      js_bitmask.vregs JoltISA.amoWordSelectShiftVReg =
        shift_bits_left addr (3 : BitVec 6) := by
    change
      (if JoltISA.amoWordSelectShiftVReg = JoltISA.amoWordSelectNewVReg then
          jolt_virtual_shift_right_bitmask_value
            (js_shift.vregs JoltISA.amoWordSelectShiftVReg)
        else js_shift.vregs JoltISA.amoWordSelectShiftVReg) =
        shift_bits_left addr (3 : BitVec 6)
    rw [if_neg (by decide)]
    exact hshift_shift
  have hbitmask_tmp :
      js_bitmask.vregs JoltISA.amoWordSelectNewVReg =
        jolt_virtual_shift_right_bitmask_value
          (shift_bits_left addr (3 : BitVec 6)) := by
    change
      (if JoltISA.amoWordSelectNewVReg = JoltISA.amoWordSelectNewVReg then
          jolt_virtual_shift_right_bitmask_value
            (js_shift.vregs JoltISA.amoWordSelectShiftVReg)
        else js_shift.vregs JoltISA.amoWordSelectNewVReg) =
        jolt_virtual_shift_right_bitmask_value
          (shift_bits_left addr (3 : BitVec 6))
    rw [if_pos rfl, hshift_shift]
  have hsrl :
      (JoltISA.execInstr
        (.VirtualSRL (.vreg JoltISA.amoWordSelectOldVReg)
          (.vreg JoltISA.amoWordSelectDwordVReg)
          (.vreg JoltISA.amoWordSelectNewVReg))).run js_bitmask =
      .ok RETIRE_SUCCESS
        { sail := js_bitmask.sail
          vregs := fun r =>
            if r = JoltISA.amoWordSelectOldVReg then
              jolt_virtual_srl_value
                (js_bitmask.vregs JoltISA.amoWordSelectDwordVReg)
                (js_bitmask.vregs JoltISA.amoWordSelectNewVReg)
            else js_bitmask.vregs r } :=
    JoltISA.virtual_srl_run_vreg_vreg_vreg
      JoltISA.amoWordSelectOldVReg JoltISA.amoWordSelectDwordVReg
      JoltISA.amoWordSelectNewVReg js_bitmask
  let js_pre : SailJoltState :=
    { sail := js_bitmask.sail
      vregs := fun r =>
        if r = JoltISA.amoWordSelectOldVReg then
          jolt_virtual_srl_value
            (js_bitmask.vregs JoltISA.amoWordSelectDwordVReg)
            (js_bitmask.vregs JoltISA.amoWordSelectNewVReg)
        else js_bitmask.vregs r }
  have hsrl_named :
      (JoltISA.execInstr
        (.VirtualSRL (.vreg JoltISA.amoWordSelectOldVReg)
          (.vreg JoltISA.amoWordSelectDwordVReg)
          (.vreg JoltISA.amoWordSelectNewVReg))).run js_bitmask =
      .ok RETIRE_SUCCESS js_pre := by
    exact hsrl
  refine ⟨js_pre, ?_, ?_, ?_, ?_, ?_⟩
  · unfold JoltISA.amoPre64ProgramWithScratch
    rw [JoltISA.execProgram_instr_run_retire _ _ js js hassert]
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_base hbase_run]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_base js_load hld_named]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_load js_shift hmuli_named]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_shift js_bitmask hbitmask_named]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_bitmask js_pre hsrl_named]
  · exact hbitmask_sail
  · change
      (if JoltISA.amoWordSelectDwordVReg = JoltISA.amoWordSelectOldVReg then
          jolt_virtual_srl_value
            (js_bitmask.vregs JoltISA.amoWordSelectDwordVReg)
            (js_bitmask.vregs JoltISA.amoWordSelectNewVReg)
        else js_bitmask.vregs JoltISA.amoWordSelectDwordVReg) =
        loaded_dword_at js.sail (amoWordBase addr)
    rw [if_neg (by decide)]
    exact hbitmask_dword
  · change
      (if JoltISA.amoWordSelectShiftVReg = JoltISA.amoWordSelectOldVReg then
          jolt_virtual_srl_value
            (js_bitmask.vregs JoltISA.amoWordSelectDwordVReg)
            (js_bitmask.vregs JoltISA.amoWordSelectNewVReg)
        else js_bitmask.vregs JoltISA.amoWordSelectShiftVReg) =
        shift_bits_left addr (3 : BitVec 6)
    rw [if_neg (by decide)]
    exact hbitmask_shift
  · change
      (if JoltISA.amoWordSelectOldVReg = JoltISA.amoWordSelectOldVReg then
          jolt_virtual_srl_value
            (js_bitmask.vregs JoltISA.amoWordSelectDwordVReg)
            (js_bitmask.vregs JoltISA.amoWordSelectNewVReg)
        else js_bitmask.vregs JoltISA.amoWordSelectOldVReg) =
        shift_bits_right
          (loaded_dword_at js.sail (amoWordBase addr))
          (Sail.BitVec.extractLsb
            (shift_bits_left addr (3 : BitVec 6)) 5 0)
    rw [if_pos rfl, hbitmask_dword, hbitmask_tmp]
    exact
      JoltISA.virtual_srl_shift_right_bitmask_value_eq
        (loaded_dword_at js.sail (amoWordBase addr))
        (shift_bits_left addr (3 : BitVec 6))


/-- The first two postlude instructions seed the low-word mask and preserve the
loaded dword, lane shift, and old word. -/
theorem amo_word_rust_select_mask32_prefix_run
    (js : SailJoltState) (s : SailState) (shift64 dword old : BitVec 64)
    (h_sail : js.sail = s)
    (h_shift : js.vregs JoltISA.amoWordSelectShiftVReg = shift64)
    (h_dword : js.vregs JoltISA.amoWordSelectDwordVReg = dword)
    (h_old : js.vregs JoltISA.amoWordSelectOldVReg = old) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs JoltISA.amoWordSelectMaskVReg =
        (0x00000000FFFFFFFF : BitVec 64) ∧
      js'.vregs JoltISA.amoWordSelectShiftVReg = shift64 ∧
      js'.vregs JoltISA.amoWordSelectDwordVReg = dword ∧
      js'.vregs JoltISA.amoWordSelectOldVReg = old ∧
      js'.vregs JoltISA.amoWordSelectNewVReg = js.vregs JoltISA.amoWordSelectNewVReg ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.ORI (.vreg JoltISA.amoWordSelectMaskVReg)
            (.xreg (regidx.Regidx 0)) (-1 : BitVec 12)) <|
           .instr (.VirtualSRLI (.vreg JoltISA.amoWordSelectMaskVReg)
            (.vreg JoltISA.amoWordSelectMaskVReg)
            (JoltISA.srliBitmask (32 : BitVec 6))) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  obtain ⟨js_ones, _hx0, hones_sail_raw, hones_mask_raw,
      hones_preserves, hones_run⟩ :=
    JoltISA.exists_state_after_ori_run_vreg_xreg_of_sail_eq
      JoltISA.amoWordSelectMaskVReg (regidx.Regidx 0) (-1 : BitVec 12)
      js s (0#64) h_sail (amo_word_read_x0_eq_zero s)
  have hones_sail : js_ones.sail = s := by
    rw [hones_sail_raw, h_sail]
  have hones_mask : js_ones.vregs JoltISA.amoWordSelectMaskVReg = (-1 : BitVec 64) := by
    rw [hones_mask_raw]
    exact amo_word_seed_mask_value
  have hones_shift : js_ones.vregs JoltISA.amoWordSelectShiftVReg = shift64 := by
    rw [hones_preserves JoltISA.amoWordSelectShiftVReg (by decide)]
    exact h_shift
  have hones_dword : js_ones.vregs JoltISA.amoWordSelectDwordVReg = dword := by
    rw [hones_preserves JoltISA.amoWordSelectDwordVReg (by decide)]
    exact h_dword
  have hones_old : js_ones.vregs JoltISA.amoWordSelectOldVReg = old := by
    rw [hones_preserves JoltISA.amoWordSelectOldVReg (by decide)]
    exact h_old
  have hones_new :
      js_ones.vregs JoltISA.amoWordSelectNewVReg = js.vregs JoltISA.amoWordSelectNewVReg := by
    rw [hones_preserves JoltISA.amoWordSelectNewVReg (by decide)]
  obtain ⟨js_mask, hmask_sail_raw, hmask_raw, hmask_preserves,
      hmask_tail⟩ :=
    JoltISA.exists_state_after_srli_block_run_vreg_vreg
      JoltISA.amoWordSelectMaskVReg JoltISA.amoWordSelectMaskVReg (32 : BitVec 6) js_ones
  refine ⟨js_mask, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmask_sail_raw, hones_sail]
  · rw [hmask_raw, hones_mask]
    exact amo_word_low_word_mask_value
  · rw [hmask_preserves JoltISA.amoWordSelectShiftVReg (by decide)]
    exact hones_shift
  · rw [hmask_preserves JoltISA.amoWordSelectDwordVReg (by decide)]
    exact hones_dword
  · rw [hmask_preserves JoltISA.amoWordSelectOldVReg (by decide)]
    exact hones_old
  · rw [hmask_preserves JoltISA.amoWordSelectNewVReg (by decide)]
    exact hones_new
  · intro tail
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_ones hones_run]
    have htail := hmask_tail tail
    unfold JoltISA.srliBlock at htail
    exact htail

/-- The postlude's mask-shift block turns the low-word mask into the selected
word-lane mask. -/
theorem amo_word_rust_select_shift_mask_prefix_run
    (js : SailJoltState) (s : SailState) (shift64 dword old : BitVec 64)
    (h_sail : js.sail = s)
    (h_mask : js.vregs JoltISA.amoWordSelectMaskVReg =
      (0x00000000FFFFFFFF : BitVec 64))
    (h_shift : js.vregs JoltISA.amoWordSelectShiftVReg = shift64)
    (h_dword : js.vregs JoltISA.amoWordSelectDwordVReg = dword)
    (h_old : js.vregs JoltISA.amoWordSelectOldVReg = old) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs JoltISA.amoWordSelectMaskVReg =
        shift_bits_left (0x00000000FFFFFFFF : BitVec 64)
          (Sail.BitVec.extractLsb shift64 5 0) ∧
      js'.vregs JoltISA.amoWordSelectShiftVReg = shift64 ∧
      js'.vregs JoltISA.amoWordSelectDwordVReg = dword ∧
      js'.vregs JoltISA.amoWordSelectOldVReg = old ∧
      js'.vregs JoltISA.amoWordSelectNewVReg = js.vregs JoltISA.amoWordSelectNewVReg ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.VirtualPow2 (.vreg JoltISA.amoWordSelectInlineTmpVReg)
            (.vreg JoltISA.amoWordSelectShiftVReg)) <|
           .instr (.MUL (.vreg JoltISA.amoWordSelectMaskVReg)
            (.vreg JoltISA.amoWordSelectMaskVReg)
            (.vreg JoltISA.amoWordSelectInlineTmpVReg)) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  obtain ⟨js', h_sail_raw, h_mask_raw, h_preserves, htail⟩ :=
    JoltISA.exists_state_after_sll_block_run_vreg_vreg_vreg
      JoltISA.amoWordSelectMaskVReg JoltISA.amoWordSelectMaskVReg
      JoltISA.amoWordSelectShiftVReg JoltISA.amoWordSelectInlineTmpVReg js (by decide)
  refine ⟨js', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_sail_raw, h_sail]
  · rw [h_mask_raw, h_mask, h_shift]
  · rw [h_preserves JoltISA.amoWordSelectShiftVReg (by decide) (by decide)]
    exact h_shift
  · rw [h_preserves JoltISA.amoWordSelectDwordVReg (by decide) (by decide)]
    exact h_dword
  · rw [h_preserves JoltISA.amoWordSelectOldVReg (by decide) (by decide)]
    exact h_old
  · rw [h_preserves JoltISA.amoWordSelectNewVReg (by decide) (by decide)]
  · intro tail
    have h := htail tail
    unfold JoltISA.sllBlock at h
    exact h

/-- The postlude shifts the new word value from `rs2` into the selected dword
lane while preserving the prepared mask and old word. -/
theorem amo_word_rust_select_shift_new_prefix_run
    (rs2 : regidx) (js : SailJoltState) (s : SailState)
    (rs2Val shift64 shiftedMask dword old : BitVec 64)
    (h_sail : js.sail = s)
    (hrs2 : rX_bits rs2 s = .ok rs2Val s)
    (h_mask : js.vregs JoltISA.amoWordSelectMaskVReg = shiftedMask)
    (h_shift : js.vregs JoltISA.amoWordSelectShiftVReg = shift64)
    (h_dword : js.vregs JoltISA.amoWordSelectDwordVReg = dword)
    (h_old : js.vregs JoltISA.amoWordSelectOldVReg = old) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs JoltISA.amoWordSelectShiftVReg =
        shift_bits_left rs2Val (Sail.BitVec.extractLsb shift64 5 0) ∧
      js'.vregs JoltISA.amoWordSelectMaskVReg = shiftedMask ∧
      js'.vregs JoltISA.amoWordSelectDwordVReg = dword ∧
      js'.vregs JoltISA.amoWordSelectOldVReg = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.VirtualPow2 (.vreg JoltISA.amoWordSelectInlineTmpVReg)
            (.vreg JoltISA.amoWordSelectShiftVReg)) <|
           .instr (.MUL (.vreg JoltISA.amoWordSelectShiftVReg)
            (.xreg rs2) (.vreg JoltISA.amoWordSelectInlineTmpVReg)) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  have hrs2_current : rX_bits rs2 js.sail = .ok rs2Val js.sail := by
    rw [h_sail]
    exact hrs2
  obtain ⟨js', _hrs2, h_sail_raw, h_shift_raw, h_preserves, htail⟩ :=
    JoltISA.exists_state_after_sll_block_run_vreg_xreg_vreg
      JoltISA.amoWordSelectShiftVReg rs2 JoltISA.amoWordSelectShiftVReg
      JoltISA.amoWordSelectInlineTmpVReg js rs2Val hrs2_current
  refine ⟨js', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_sail_raw, h_sail]
  · rw [h_shift_raw, h_shift]
  · rw [h_preserves JoltISA.amoWordSelectMaskVReg (by decide) (by decide)]
    exact h_mask
  · rw [h_preserves JoltISA.amoWordSelectDwordVReg (by decide) (by decide)]
    exact h_dword
  · rw [h_preserves JoltISA.amoWordSelectOldVReg (by decide) (by decide)]
    exact h_old
  · intro tail
    have h := htail tail
    unfold JoltISA.sllBlock at h
    exact h

/-- The postlude shifts a virtual-register new word value into the selected
dword lane while preserving the prepared mask and old word. -/
theorem amo_word_rust_select_shift_new_vreg_prefix_run
    (new : JoltISA.VReg) (js : SailJoltState) (s : SailState)
    (newValue shift64 shiftedMask dword old : BitVec 64)
    (h_sail : js.sail = s)
    (h_new : js.vregs new = newValue)
    (h_mask : js.vregs JoltISA.amoWordSelectMaskVReg = shiftedMask)
    (h_shift : js.vregs JoltISA.amoWordSelectShiftVReg = shift64)
    (h_dword : js.vregs JoltISA.amoWordSelectDwordVReg = dword)
    (h_old : js.vregs JoltISA.amoWordSelectOldVReg = old)
    (hnew_ne_tmp : new ≠ JoltISA.amoWordSelectInlineTmpVReg) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs JoltISA.amoWordSelectShiftVReg =
        shift_bits_left newValue (Sail.BitVec.extractLsb shift64 5 0) ∧
      js'.vregs JoltISA.amoWordSelectMaskVReg = shiftedMask ∧
      js'.vregs JoltISA.amoWordSelectDwordVReg = dword ∧
      js'.vregs JoltISA.amoWordSelectOldVReg = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.VirtualPow2 (.vreg JoltISA.amoWordSelectInlineTmpVReg)
            (.vreg JoltISA.amoWordSelectShiftVReg)) <|
           .instr (.MUL (.vreg JoltISA.amoWordSelectShiftVReg)
            (.vreg new) (.vreg JoltISA.amoWordSelectInlineTmpVReg)) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  obtain ⟨js', h_sail_raw, h_shift_raw, h_preserves, htail⟩ :=
    JoltISA.exists_state_after_sll_block_run_vreg_vreg_vreg
      JoltISA.amoWordSelectShiftVReg new JoltISA.amoWordSelectShiftVReg
      JoltISA.amoWordSelectInlineTmpVReg js hnew_ne_tmp
  refine ⟨js', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_sail_raw, h_sail]
  · rw [h_shift_raw, h_new, h_shift]
  · rw [h_preserves JoltISA.amoWordSelectMaskVReg (by decide) (by decide)]
    exact h_mask
  · rw [h_preserves JoltISA.amoWordSelectDwordVReg (by decide) (by decide)]
    exact h_dword
  · rw [h_preserves JoltISA.amoWordSelectOldVReg (by decide) (by decide)]
    exact h_old
  · intro tail
    have h := htail tail
    unfold JoltISA.sllBlock at h
    exact h

/-- The XOR/AND/XOR postlude block splices the shifted new word into the loaded
dword and preserves the shifted old word. -/
theorem amo_word_rust_select_splice_block_run
    (js : SailJoltState) (s : SailState) (addr newValue old : BitVec 64)
    (hsetup : StoreSplice.WordStoreSetup addr (amoWordBase addr))
    (h_sail : js.sail = s)
    (h_dword :
      js.vregs JoltISA.amoWordSelectDwordVReg =
        loaded_dword_at s (amoWordBase addr))
    (h_shift :
      js.vregs JoltISA.amoWordSelectShiftVReg =
        shift_bits_left newValue
          (Sail.BitVec.extractLsb
            (shift_bits_left addr (3 : BitVec 6)) 5 0))
    (h_mask :
      js.vregs JoltISA.amoWordSelectMaskVReg =
        shift_bits_left (0x00000000FFFFFFFF : BitVec 64)
          (Sail.BitVec.extractLsb
            (shift_bits_left addr (3 : BitVec 6)) 5 0))
    (h_old : js.vregs JoltISA.amoWordSelectOldVReg = old) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs JoltISA.amoWordSelectDwordVReg =
        amoWordSplicedDword s addr newValue ∧
      js'.vregs JoltISA.amoWordSelectOldVReg = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.XOR (.vreg JoltISA.amoWordSelectShiftVReg)
            (.vreg JoltISA.amoWordSelectDwordVReg)
            (.vreg JoltISA.amoWordSelectShiftVReg)) <|
           .instr (.AND (.vreg JoltISA.amoWordSelectShiftVReg)
            (.vreg JoltISA.amoWordSelectShiftVReg)
            (.vreg JoltISA.amoWordSelectMaskVReg)) <|
           .instr (.XOR (.vreg JoltISA.amoWordSelectDwordVReg)
            (.vreg JoltISA.amoWordSelectDwordVReg)
            (.vreg JoltISA.amoWordSelectShiftVReg)) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  let shiftedNew :=
    shift_bits_left newValue
      (Sail.BitVec.extractLsb (shift_bits_left addr (3 : BitVec 6)) 5 0)
  let shiftedMask :=
    shift_bits_left (0x00000000FFFFFFFF : BitVec 64)
      (Sail.BitVec.extractLsb (shift_bits_left addr (3 : BitVec 6)) 5 0)
  let dword := loaded_dword_at s (amoWordBase addr)
  obtain ⟨js_xor, hxor_sail_raw, hxor_shift_raw, hxor_preserves,
      hxor_run⟩ :=
    JoltISA.exists_state_after_xor_run_vreg_vreg_vreg
      JoltISA.amoWordSelectShiftVReg JoltISA.amoWordSelectDwordVReg
      JoltISA.amoWordSelectShiftVReg js dword shiftedNew h_dword h_shift
  have hxor_sail : js_xor.sail = s := by
    rw [hxor_sail_raw, h_sail]
  have hxor_shift : js_xor.vregs JoltISA.amoWordSelectShiftVReg = dword ^^^ shiftedNew := by
    exact hxor_shift_raw
  have hxor_mask : js_xor.vregs JoltISA.amoWordSelectMaskVReg = shiftedMask := by
    rw [hxor_preserves JoltISA.amoWordSelectMaskVReg (by decide)]
    exact h_mask
  have hxor_dword : js_xor.vregs JoltISA.amoWordSelectDwordVReg = dword := by
    rw [hxor_preserves JoltISA.amoWordSelectDwordVReg (by decide)]
    exact h_dword
  have hxor_old : js_xor.vregs JoltISA.amoWordSelectOldVReg = old := by
    rw [hxor_preserves JoltISA.amoWordSelectOldVReg (by decide)]
    exact h_old
  obtain ⟨js_and, hand_sail_raw, hand_shift_raw, hand_preserves,
      hand_run⟩ :=
    amo_word_exists_state_after_and_run_vreg_vreg_vreg
      JoltISA.amoWordSelectShiftVReg JoltISA.amoWordSelectShiftVReg JoltISA.amoWordSelectMaskVReg
      js_xor (dword ^^^ shiftedNew) shiftedMask hxor_shift hxor_mask
  have hand_sail : js_and.sail = s := by
    rw [hand_sail_raw, hxor_sail]
  have hand_shift : js_and.vregs JoltISA.amoWordSelectShiftVReg =
      (dword ^^^ shiftedNew) &&& shiftedMask := by
    exact hand_shift_raw
  have hand_dword : js_and.vregs JoltISA.amoWordSelectDwordVReg = dword := by
    rw [hand_preserves JoltISA.amoWordSelectDwordVReg (by decide)]
    exact hxor_dword
  have hand_old : js_and.vregs JoltISA.amoWordSelectOldVReg = old := by
    rw [hand_preserves JoltISA.amoWordSelectOldVReg (by decide)]
    exact hxor_old
  obtain ⟨js_splice, hsplice_sail_raw, hsplice_dword_raw,
      hsplice_preserves, hxor2_run⟩ :=
    JoltISA.exists_state_after_xor_run_vreg_vreg_vreg
      JoltISA.amoWordSelectDwordVReg JoltISA.amoWordSelectDwordVReg
      JoltISA.amoWordSelectShiftVReg js_and dword
      ((dword ^^^ shiftedNew) &&& shiftedMask) hand_dword hand_shift
  have hspliced_value := amo_word_splice_shifted_eq s addr newValue hsetup
  refine ⟨js_splice, ?_, ?_, ?_, ?_⟩
  · rw [hsplice_sail_raw, hand_sail]
  · rw [hsplice_dword_raw]
    exact hspliced_value
  · rw [hsplice_preserves JoltISA.amoWordSelectOldVReg (by decide)]
    exact hand_old
  · intro tail
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_xor hxor_run]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_xor js_and hand_run]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_and js_splice hxor2_run]

/-- The postlude recomputes the enclosing dword base before storing it. -/
theorem amo_word_rust_select_store_base_prefix_run
    (rs1 : regidx) (js : SailJoltState) (s : SailState)
    (addr dwordNew old : BitVec 64)
    (h_sail : js.sail = s)
    (hrs1 : rX_bits rs1 s = .ok addr s)
    (h_dword : js.vregs JoltISA.amoWordSelectDwordVReg = dwordNew)
    (h_old : js.vregs JoltISA.amoWordSelectOldVReg = old) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs JoltISA.amoWordSelectMaskVReg = amoWordBase addr ∧
      js'.vregs JoltISA.amoWordSelectDwordVReg = dwordNew ∧
      js'.vregs JoltISA.amoWordSelectOldVReg = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.ANDI (.vreg JoltISA.amoWordSelectMaskVReg)
            (.xreg rs1) (-8 : BitVec 12)) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  obtain ⟨js', _hrs1, h_sail_raw, h_base_raw, h_preserves, hrun⟩ :=
    JoltISA.exists_state_after_andi_run_vreg_xreg_of_sail_eq
      JoltISA.amoWordSelectMaskVReg rs1 (-8 : BitVec 12) js s addr h_sail hrs1
  refine ⟨js', ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_sail_raw, h_sail]
  · rw [h_base_raw]
    exact amo_word_base_mask addr
  · rw [h_preserves JoltISA.amoWordSelectDwordVReg (by decide)]
    exact h_dword
  · rw [h_preserves JoltISA.amoWordSelectOldVReg (by decide)]
    exact h_old
  · intro tail
    rw [JoltISA.execProgram_instr_run_retire _ _ js js' hrun]

/-- The dword store instruction writes the spliced dword and preserves the
virtual-register file for the final writeback. -/
theorem amo_word_rust_select_sd_spliced_dword_run
    {op : amoop}
    (js : SailJoltState) (s : SailState) (addr dwordNew old : BitVec 64)
    (hcfg : JoltConfig s)
    (h_mem : AmoMemoryContext op 4 (amoWordBase addr) addr s)
    (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
    (h_sail : js.sail = s)
    (h_base : js.vregs JoltISA.amoWordSelectMaskVReg = amoWordBase addr)
    (h_dword : js.vregs JoltISA.amoWordSelectDwordVReg = dwordNew)
    (h_old : js.vregs JoltISA.amoWordSelectOldVReg = old) :
    ∃ js',
      js'.sail = state_after_dword_store s (amoWordBase addr) dwordNew ∧
      js'.vregs JoltISA.amoWordSelectOldVReg = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.SD (.vreg JoltISA.amoWordSelectMaskVReg)
            (.vreg JoltISA.amoWordSelectDwordVReg) (0 : BitVec 12)) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  have hwrite_dword :
      vmem_write_addr (Virtaddr (amoWordBase addr)) 8 dwordNew
        (Store Data) false false false s =
      .ok (Ok true) (state_after_dword_store s (amoWordBase addr) dwordNew) :=
    vmem_write_addr_dword_store_reduces (amoWordBase addr) dwordNew s hcfg
      (amo_word_base_aligned_access addr h_no_ovf).toAlignedAccess
      (AmoMemoryContext.jolt_store_mem h_mem).pmp
      (AmoMemoryContext.jolt_store_mem h_mem).mmio
  have hwrite_current :
      vmem_write_addr (Virtaddr (js.vregs JoltISA.amoWordSelectMaskVReg +
          sign_extend (m := 64) (0 : BitVec 12))) 8
        (js.vregs JoltISA.amoWordSelectDwordVReg)
        (Store Data) false false false js.sail =
      .ok (Ok true) (state_after_dword_store s (amoWordBase addr) dwordNew) := by
    rw [h_sail, h_base, h_dword, amo_word_zero_offset_addr (amoWordBase addr)]
    exact hwrite_dword
  let js' : SailJoltState :=
    { sail := state_after_dword_store s (amoWordBase addr) dwordNew
      vregs := js.vregs }
  have hsd_align :
      (js.vregs JoltISA.amoWordSelectMaskVReg + sign_extend (m := 64) (0 : BitVec 12)) &&&
          (7 : BitVec 64) =
        0 := by
    rw [h_base, amo_word_zero_offset_addr (amoWordBase addr)]
    exact amo_word_base_aligned addr
  have hsd :
      (JoltISA.execInstr
        (.SD (.vreg JoltISA.amoWordSelectMaskVReg)
          (.vreg JoltISA.amoWordSelectDwordVReg) (0 : BitVec 12))).run js =
        .ok RETIRE_SUCCESS js' :=
    JoltISA.execInstr_sd_vreg_run_of_write
      JoltISA.amoWordSelectMaskVReg JoltISA.amoWordSelectDwordVReg (0 : BitVec 12)
      js (state_after_dword_store s (amoWordBase addr) dwordNew) hsd_align hwrite_current
  refine ⟨js', rfl, ?_, ?_⟩
  · exact h_old
  · intro tail
    rw [JoltISA.execProgram_instr_run_retire _ _ js js' hsd]

/-- The final postlude instruction writes the sign-extended old word to `rd`. -/
theorem amo_word_rust_select_writeback_old_run
    (rd : regidx) (js : SailJoltState) (s : SailState)
    (addr : BitVec 64) (result : BitVec 32) (old : BitVec 64)
    (h_sail : js.sail = state_after_word_store s addr result)
    (h_old : js.vregs JoltISA.amoWordSelectOldVReg = old)
    (h_old_word :
      sign_extend (m := 64)
        ((Sail.BitVec.extractLsb old 31 0) : BitVec 32) =
      sign_extend (m := 64) (loaded_word_at s addr)) :
    ∃ js',
      js'.sail = amoWordFinalSailState rd s addr result ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.VirtualSignExtendWord (.xreg rd)
            (.vreg JoltISA.amoWordSelectOldVReg)) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  obtain ⟨writebackState, hwriteback, hwriteback_state⟩ :=
    amo_word_writeback_old_shape rd s addr result
  have hwriteback_current :
      wX_bits rd
        (sign_extend (m := 64)
          ((Sail.BitVec.extractLsb
            (js.vregs JoltISA.amoWordSelectOldVReg) 31 0) : BitVec 32))
        js.sail =
      .ok () writebackState := by
    rw [h_sail, h_old, h_old_word]
    exact hwriteback
  let js' : SailJoltState := { sail := writebackState, vregs := js.vregs }
  have hsext :
      (JoltISA.execInstr
        (.VirtualSignExtendWord (.xreg rd)
          (.vreg JoltISA.amoWordSelectOldVReg))).run js =
        .ok RETIRE_SUCCESS js' :=
    JoltISA.virtual_sign_extend_word_run_xreg_vreg
      rd JoltISA.amoWordSelectOldVReg js writebackState hwriteback_current
  refine ⟨js', ?_, ?_⟩
  · exact hwriteback_state
  · intro tail
    rw [JoltISA.execProgram_instr_run_retire _ _ js js' hsext]

/-- The aligned word-AMO postlude stores the low 32 bits of a virtual-register
new value into the selected word lane and writes the sign-extended old word
into `rd`. -/
theorem amo_word_rust_select_post64_vreg_aligned_run
    {op : amoop} (rs1 rd : regidx)
    (js js_pre : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr newValue : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (h_mem : AmoMemoryContext op 4 (amoWordBase addr) addr js.sail)
    (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (3 : BitVec 64) = 0)
    (hpre_sail : js_pre.sail = js.sail)
    (hpre_new : js_pre.vregs JoltISA.amoWordSelectNewVReg = newValue)
    (hpre_dword :
      js_pre.vregs JoltISA.amoWordSelectDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr))
    (hpre_shift :
      js_pre.vregs JoltISA.amoWordSelectShiftVReg =
        shift_bits_left addr (3 : BitVec 6))
    (hpre_old :
      js_pre.vregs JoltISA.amoWordSelectOldVReg =
        shift_bits_right
          (loaded_dword_at js.sail (amoWordBase addr))
          (Sail.BitVec.extractLsb
            (shift_bits_left addr (3 : BitVec 6)) 5 0)) :
    ∃ jsf : SailJoltState,
      (JoltISA.execProgram
        (JoltISA.amoPost64ProgramWithScratch rs1 rd (.vreg JoltISA.amoWordSelectNewVReg)
          JoltISA.amoWordSelectDwordVReg JoltISA.amoWordSelectShiftVReg
          JoltISA.amoWordSelectMaskVReg JoltISA.amoWordSelectOldVReg
          JoltISA.amoWordSelectInlineTmpVReg)).run js_pre =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail =
        amoWordFinalSailState rd js.sail addr
          (Sail.BitVec.extractLsb newValue 31 0) := by
  let shift64 := shift_bits_left addr (3 : BitVec 6)
  let shift6 := Sail.BitVec.extractLsb shift64 5 0
  let dword := loaded_dword_at js.sail (amoWordBase addr)
  let old := shift_bits_right dword shift6
  let mask32 := (0x00000000FFFFFFFF : BitVec 64)
  let shiftedMask := shift_bits_left mask32 shift6
  let dwordNew := amoWordSplicedDword js.sail addr newValue
  let wordResult : BitVec 32 := Sail.BitVec.extractLsb newValue 31 0
  have hsetup := amo_word_store_setup addr h_no_ovf h_align
  obtain ⟨js_mask32, hmask_sail, hmask_mask, hmask_shift, hmask_dword,
      hmask_old, hmask_new_preserve, hmask_tail⟩ :=
    amo_word_rust_select_mask32_prefix_run js_pre js.sail shift64 dword old
      hpre_sail hpre_shift hpre_dword hpre_old
  have hmask_new : js_mask32.vregs JoltISA.amoWordSelectNewVReg = newValue := by
    rw [hmask_new_preserve]
    exact hpre_new
  obtain ⟨js_shifted_mask, hshift_mask_sail, hshift_mask_mask,
      hshift_mask_shift, hshift_mask_dword, hshift_mask_old,
      hshift_mask_new_preserve, hshift_mask_tail⟩ :=
    amo_word_rust_select_shift_mask_prefix_run js_mask32 js.sail shift64 dword old
      hmask_sail hmask_mask hmask_shift hmask_dword hmask_old
  have hshift_mask_new :
      js_shifted_mask.vregs JoltISA.amoWordSelectNewVReg = newValue := by
    rw [hshift_mask_new_preserve]
    exact hmask_new
  obtain ⟨js_shifted_new, hshift_new_sail, hshift_new_shift,
      hshift_new_mask, hshift_new_dword, hshift_new_old,
      hshift_new_tail⟩ :=
    amo_word_rust_select_shift_new_vreg_prefix_run JoltISA.amoWordSelectNewVReg
      js_shifted_mask js.sail
      newValue shift64 shiftedMask dword old hshift_mask_sail
      hshift_mask_new hshift_mask_mask hshift_mask_shift
      hshift_mask_dword hshift_mask_old (by decide)
  obtain ⟨js_splice, hsplice_sail, hsplice_dword, hsplice_old,
      hsplice_tail⟩ :=
    amo_word_rust_select_splice_block_run js_shifted_new js.sail addr newValue old hsetup
      hshift_new_sail hshift_new_dword hshift_new_shift hshift_new_mask
      hshift_new_old
  obtain ⟨js_store_base, hstore_base_sail, hstore_base, hstore_base_dword,
      hstore_base_old, hstore_base_tail⟩ :=
    amo_word_rust_select_store_base_prefix_run rs1 js_splice js.sail addr dwordNew old
      hsplice_sail hrs1 hsplice_dword hsplice_old
  obtain ⟨js_store, hstore_sail, hstore_old, hstore_tail⟩ :=
    amo_word_rust_select_sd_spliced_dword_run js_store_base js.sail addr dwordNew old
      hcfg h_mem h_no_ovf hstore_base_sail hstore_base hstore_base_dword
      hstore_base_old
  have hword_store :
      state_after_dword_store js.sail (amoWordBase addr) dwordNew =
        state_after_word_store js.sail addr wordResult :=
    amo_word_spliced_dword_store_eq_word_store
      js.sail addr newValue hsetup h_mem.jolt_bytes
  have hstore_sail_word :
      js_store.sail = state_after_word_store js.sail addr wordResult := by
    rw [hstore_sail, hword_store]
  have hold_writeback :
      sign_extend (m := 64)
        ((Sail.BitVec.extractLsb old 31 0) : BitVec 32) =
      sign_extend (m := 64) (loaded_word_at js.sail addr) :=
    amo_word_shifted_old_sign_extend_eq_loaded_word js.sail addr h_align
  obtain ⟨jsf, hwriteback_sail, hwriteback_tail⟩ :=
    amo_word_rust_select_writeback_old_run rd js_store js.sail addr wordResult old
      hstore_sail_word hstore_old hold_writeback
  refine ⟨jsf, ?_, ?_⟩
  · unfold JoltISA.amoPost64ProgramWithScratch
    rw [hmask_tail]
    rw [hshift_mask_tail]
    rw [hshift_new_tail]
    rw [hsplice_tail]
    rw [hstore_base_tail]
    rw [hstore_tail]
    rw [hwriteback_tail]
    rfl
  · exact hwriteback_sail

def amoWordSelectRustExtendProgram
    (extend : JoltISA.Dst → JoltISA.Src → JoltISA.Instr)
    (rs2 : regidx) (tail : JoltISA.Program) : JoltISA.Program :=
  .instr (extend (.vreg JoltISA.amoWordSelectNewVReg) (.xreg rs2)) <|
  .instr (extend (.vreg JoltISA.amoWordSelectMaskVReg) (.vreg JoltISA.amoWordSelectOldVReg)) <|
  tail

/-- The word-select comparison overwrites `amoMaskVReg` with the selected
comparison flag. -/
def amoWordSelectRustCompareProgram
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src) (tail : JoltISA.Program) :
    JoltISA.Program :=
  .instr (cmpInstr (.vreg JoltISA.amoWordSelectMaskVReg) cmpLhs cmpRhs) tail

/-- The word-select tail computes `(rs2 - old) * flag + old` into
`amoNewVReg`. -/
def amoWordSelectRustTailProgram
    (rs2 : regidx) (tail : JoltISA.Program) : JoltISA.Program :=
  .instr (.SUB (.vreg JoltISA.amoWordSelectNewVReg)
    (.xreg rs2) (.vreg JoltISA.amoWordSelectOldVReg)) <|
  .instr (.MUL (.vreg JoltISA.amoWordSelectNewVReg)
    (.vreg JoltISA.amoWordSelectNewVReg) (.vreg JoltISA.amoWordSelectMaskVReg)) <|
  .instr (.ADD (.vreg JoltISA.amoWordSelectNewVReg)
    (.vreg JoltISA.amoWordSelectNewVReg) (.vreg JoltISA.amoWordSelectOldVReg)) <|
  tail

/-- The word-select middle is the extension phase, comparison phase, and
select-tail phase composed around an arbitrary continuation. -/
def amoWordSelectRustMiddleProgram
    (extend : JoltISA.Dst → JoltISA.Src → JoltISA.Instr)
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src) (rs2 : regidx)
    (tail : JoltISA.Program) : JoltISA.Program :=
  amoWordSelectRustExtendProgram extend rs2 <|
  amoWordSelectRustCompareProgram cmpInstr cmpLhs cmpRhs <|
  amoWordSelectRustTailProgram rs2 tail

/-- Shape produced by the extension phase of a word select AMO.

The phase writes the extended `rs2` word into `amoNewVReg`, the extended old
word into `amoMaskVReg`, and preserves the prelude values needed later. -/
structure AmoWordSelectRustExtendStep
    (extend : JoltISA.Dst → JoltISA.Src → JoltISA.Instr)
    (rs2 : regidx)
    (old dword shift rs2Ext oldExt : BitVec 64)
    (js_before js_after : SailJoltState) : Prop where
  run :
    ∀ tail,
      (JoltISA.execProgram
        (amoWordSelectRustExtendProgram extend rs2 tail)).run js_before =
        (JoltISA.execProgram tail).run js_after
  sail : js_after.sail = js_before.sail
  rs2_ext_vreg : js_after.vregs JoltISA.amoWordSelectNewVReg = rs2Ext
  old_ext_vreg : js_after.vregs JoltISA.amoWordSelectMaskVReg = oldExt
  old_vreg : js_after.vregs JoltISA.amoWordSelectOldVReg = old
  dword_vreg : js_after.vregs JoltISA.amoWordSelectDwordVReg = dword
  shift_vreg : js_after.vregs JoltISA.amoWordSelectShiftVReg = shift

/-- Shape produced by the comparison phase of a word select AMO.

The phase overwrites `amoMaskVReg` with the comparison flag and preserves the
prelude values needed by the select tail and postlude. -/
structure AmoWordSelectRustCompareStep
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src)
    (old dword shift flag : BitVec 64)
    (js_before js_after : SailJoltState) : Prop where
  run :
    ∀ tail,
      (JoltISA.execProgram
        (amoWordSelectRustCompareProgram cmpInstr cmpLhs cmpRhs tail)).run
          js_before =
        (JoltISA.execProgram tail).run js_after
  sail : js_after.sail = js_before.sail
  flag_vreg : js_after.vregs JoltISA.amoWordSelectMaskVReg = flag
  old_vreg : js_after.vregs JoltISA.amoWordSelectOldVReg = old
  dword_vreg : js_after.vregs JoltISA.amoWordSelectDwordVReg = dword
  shift_vreg : js_after.vregs JoltISA.amoWordSelectShiftVReg = shift

/-- Shape produced by the select-tail phase of a word select AMO. -/
structure AmoWordSelectRustTailStep
    (rs2 : regidx) (old dword shift result : BitVec 64)
    (js_before js_after : SailJoltState) : Prop where
  run :
    ∀ tail,
      (JoltISA.execProgram
        (amoWordSelectRustTailProgram rs2 tail)).run js_before =
        (JoltISA.execProgram tail).run js_after
  sail : js_after.sail = js_before.sail
  result_vreg : js_after.vregs JoltISA.amoWordSelectNewVReg = result
  old_vreg : js_after.vregs JoltISA.amoWordSelectOldVReg = old
  dword_vreg : js_after.vregs JoltISA.amoWordSelectDwordVReg = dword
  shift_vreg : js_after.vregs JoltISA.amoWordSelectShiftVReg = shift

/-- Shape produced by the full word-select middle block. -/
structure AmoWordSelectRustMiddleStep
    (extend : JoltISA.Dst → JoltISA.Src → JoltISA.Instr)
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src) (rs2 : regidx)
    (old dword shift result : BitVec 64)
    (js_before js_after : SailJoltState) : Prop where
  run :
    ∀ tail,
      (JoltISA.execProgram
        (amoWordSelectRustMiddleProgram extend cmpInstr cmpLhs cmpRhs rs2
          tail)).run js_before =
        (JoltISA.execProgram tail).run js_after
  sail : js_after.sail = js_before.sail
  result_vreg : js_after.vregs JoltISA.amoWordSelectNewVReg = result
  old_vreg : js_after.vregs JoltISA.amoWordSelectOldVReg = old
  dword_vreg : js_after.vregs JoltISA.amoWordSelectDwordVReg = dword
  shift_vreg : js_after.vregs JoltISA.amoWordSelectShiftVReg = shift

theorem amo_word_rust_select_signed_extend_phase_run
    (rs2 : regidx) (js : SailJoltState)
    (rs2Val old dword shift : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hold : js.vregs JoltISA.amoWordSelectOldVReg = old)
    (hdword : js.vregs JoltISA.amoWordSelectDwordVReg = dword)
    (hshift : js.vregs JoltISA.amoWordSelectShiftVReg = shift) :
    ∃ js_afterExt : SailJoltState,
      AmoWordSelectRustExtendStep
        (fun dst src => .VirtualSignExtendWord dst src) rs2
        old dword shift
        (sign_extend (m := 64)
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
        (sign_extend (m := 64)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
        js js_afterExt := by
  let rs2Ext : BitVec 64 :=
    sign_extend (m := 64)
      (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
  let oldExt : BitVec 64 :=
    sign_extend (m := 64)
      (Sail.BitVec.extractLsb old 31 0 : BitVec 32)
  let js_afterRs2 : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.amoWordSelectNewVReg then rs2Ext else js.vregs r }
  let js_afterExt : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.amoWordSelectMaskVReg then oldExt else js_afterRs2.vregs r }
  have hrs2_run :
      (JoltISA.execInstr
        (.VirtualSignExtendWord (.vreg JoltISA.amoWordSelectNewVReg)
          (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js_afterRs2 := by
    exact
      JoltISA.virtual_sign_extend_word_run_vreg_xreg
        JoltISA.amoWordSelectNewVReg rs2 js rs2Val hrs2
  have hold_afterRs2 :
      js_afterRs2.vregs JoltISA.amoWordSelectOldVReg = old := by
    change
      (if JoltISA.amoWordSelectOldVReg = JoltISA.amoWordSelectNewVReg then rs2Ext
        else js.vregs JoltISA.amoWordSelectOldVReg) = old
    rw [if_neg (by decide), hold]
  have hold_run :
      (JoltISA.execInstr
        (.VirtualSignExtendWord (.vreg JoltISA.amoWordSelectMaskVReg)
          (.vreg JoltISA.amoWordSelectOldVReg))).run js_afterRs2 =
        .ok RETIRE_SUCCESS js_afterExt := by
    rw [JoltISA.virtual_sign_extend_word_run_vreg_vreg]
    unfold js_afterExt oldExt
    rw [hold_afterRs2]
  refine ⟨js_afterExt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tail
    unfold amoWordSelectRustExtendProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterRs2 hrs2_run]
    rw [JoltISA.execProgram_instr_run_retire
      _ _ js_afterRs2 js_afterExt hold_run]
  · rfl
  · change
      (if JoltISA.amoWordSelectNewVReg = JoltISA.amoWordSelectMaskVReg then oldExt
        else js_afterRs2.vregs JoltISA.amoWordSelectNewVReg) = rs2Ext
    rw [if_neg (by decide)]
    change
      (if JoltISA.amoWordSelectNewVReg = JoltISA.amoWordSelectNewVReg then rs2Ext
        else js.vregs JoltISA.amoWordSelectNewVReg) = rs2Ext
    rw [if_pos rfl]
  · change
      (if JoltISA.amoWordSelectMaskVReg = JoltISA.amoWordSelectMaskVReg then oldExt
        else js_afterRs2.vregs JoltISA.amoWordSelectMaskVReg) = oldExt
    rw [if_pos rfl]
  · change
      (if JoltISA.amoWordSelectOldVReg = JoltISA.amoWordSelectMaskVReg then oldExt
        else js_afterRs2.vregs JoltISA.amoWordSelectOldVReg) = old
    rw [if_neg (by decide), hold_afterRs2]
  · change
      (if JoltISA.amoWordSelectDwordVReg = JoltISA.amoWordSelectMaskVReg then oldExt
        else js_afterRs2.vregs JoltISA.amoWordSelectDwordVReg) = dword
    rw [if_neg (by decide)]
    change
      (if JoltISA.amoWordSelectDwordVReg = JoltISA.amoWordSelectNewVReg then rs2Ext
        else js.vregs JoltISA.amoWordSelectDwordVReg) = dword
    rw [if_neg (by decide), hdword]
  · change
      (if JoltISA.amoWordSelectShiftVReg = JoltISA.amoWordSelectMaskVReg then oldExt
        else js_afterRs2.vregs JoltISA.amoWordSelectShiftVReg) = shift
    rw [if_neg (by decide)]
    change
      (if JoltISA.amoWordSelectShiftVReg = JoltISA.amoWordSelectNewVReg then rs2Ext
        else js.vregs JoltISA.amoWordSelectShiftVReg) = shift
    rw [if_neg (by decide), hshift]

/-- The unsigned word-select extension phase prepares unsigned comparison
operands for `AMOMINU.W` and `AMOMAXU.W`. -/
theorem amo_word_rust_select_unsigned_extend_phase_run
    (rs2 : regidx) (js : SailJoltState)
    (rs2Val old dword shift : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hold : js.vregs JoltISA.amoWordSelectOldVReg = old)
    (hdword : js.vregs JoltISA.amoWordSelectDwordVReg = dword)
    (hshift : js.vregs JoltISA.amoWordSelectShiftVReg = shift) :
    ∃ js_afterExt : SailJoltState,
      AmoWordSelectRustExtendStep
        (fun dst src => .VirtualZeroExtendWord dst src) rs2
        old dword shift
        (zero_extend (m := 64)
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
        (zero_extend (m := 64)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
        js js_afterExt := by
  let rs2Ext : BitVec 64 :=
    zero_extend (m := 64)
      (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
  let oldExt : BitVec 64 :=
    zero_extend (m := 64)
      (Sail.BitVec.extractLsb old 31 0 : BitVec 32)
  let js_afterRs2 : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.amoWordSelectNewVReg then rs2Ext else js.vregs r }
  let js_afterExt : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.amoWordSelectMaskVReg then oldExt else js_afterRs2.vregs r }
  have hrs2_run :
      (JoltISA.execInstr
        (.VirtualZeroExtendWord (.vreg JoltISA.amoWordSelectNewVReg)
          (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js_afterRs2 := by
    exact
      JoltISA.virtual_zero_extend_word_run_vreg_xreg
        JoltISA.amoWordSelectNewVReg rs2 js rs2Val hrs2
  have hold_afterRs2 :
      js_afterRs2.vregs JoltISA.amoWordSelectOldVReg = old := by
    change
      (if JoltISA.amoWordSelectOldVReg = JoltISA.amoWordSelectNewVReg then rs2Ext
        else js.vregs JoltISA.amoWordSelectOldVReg) = old
    rw [if_neg (by decide), hold]
  have hold_run :
      (JoltISA.execInstr
        (.VirtualZeroExtendWord (.vreg JoltISA.amoWordSelectMaskVReg)
          (.vreg JoltISA.amoWordSelectOldVReg))).run js_afterRs2 =
        .ok RETIRE_SUCCESS js_afterExt := by
    rw [amo_word_virtual_zero_extend_word_run_vreg_vreg]
    unfold js_afterExt oldExt
    rw [hold_afterRs2]
  refine ⟨js_afterExt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tail
    unfold amoWordSelectRustExtendProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterRs2 hrs2_run]
    rw [JoltISA.execProgram_instr_run_retire
      _ _ js_afterRs2 js_afterExt hold_run]
  · rfl
  · change
      (if JoltISA.amoWordSelectNewVReg = JoltISA.amoWordSelectMaskVReg then oldExt
        else js_afterRs2.vregs JoltISA.amoWordSelectNewVReg) = rs2Ext
    rw [if_neg (by decide)]
    change
      (if JoltISA.amoWordSelectNewVReg = JoltISA.amoWordSelectNewVReg then rs2Ext
        else js.vregs JoltISA.amoWordSelectNewVReg) = rs2Ext
    rw [if_pos rfl]
  · change
      (if JoltISA.amoWordSelectMaskVReg = JoltISA.amoWordSelectMaskVReg then oldExt
        else js_afterRs2.vregs JoltISA.amoWordSelectMaskVReg) = oldExt
    rw [if_pos rfl]
  · change
      (if JoltISA.amoWordSelectOldVReg = JoltISA.amoWordSelectMaskVReg then oldExt
        else js_afterRs2.vregs JoltISA.amoWordSelectOldVReg) = old
    rw [if_neg (by decide), hold_afterRs2]
  · change
      (if JoltISA.amoWordSelectDwordVReg = JoltISA.amoWordSelectMaskVReg then oldExt
        else js_afterRs2.vregs JoltISA.amoWordSelectDwordVReg) = dword
    rw [if_neg (by decide)]
    change
      (if JoltISA.amoWordSelectDwordVReg = JoltISA.amoWordSelectNewVReg then rs2Ext
        else js.vregs JoltISA.amoWordSelectDwordVReg) = dword
    rw [if_neg (by decide), hdword]
  · change
      (if JoltISA.amoWordSelectShiftVReg = JoltISA.amoWordSelectMaskVReg then oldExt
        else js_afterRs2.vregs JoltISA.amoWordSelectShiftVReg) = shift
    rw [if_neg (by decide)]
    change
      (if JoltISA.amoWordSelectShiftVReg = JoltISA.amoWordSelectNewVReg then rs2Ext
        else js.vregs JoltISA.amoWordSelectShiftVReg) = shift
    rw [if_neg (by decide), hshift]

/-- A signed word-select comparison phase writes the signed less-than flag
between two prepared virtual operands. -/
theorem amo_word_rust_select_slt_compare_phase_run_vreg_vreg
    (lhs rhs : JoltISA.VReg) (js : SailJoltState)
    (x y old dword shift : BitVec 64)
    (hlhs : js.vregs lhs = x)
    (hrhs : js.vregs rhs = y)
    (hold : js.vregs JoltISA.amoWordSelectOldVReg = old)
    (hdword : js.vregs JoltISA.amoWordSelectDwordVReg = dword)
    (hshift : js.vregs JoltISA.amoWordSelectShiftVReg = shift) :
    ∃ js_afterCmp : SailJoltState,
      AmoWordSelectRustCompareStep
        (fun dst lhs rhs => .SLT dst lhs rhs) (.vreg lhs) (.vreg rhs)
        old dword shift
        (zero_extend (m := 64) (bool_to_bit (zopz0zI_s x y)))
        js js_afterCmp := by
  let flag : BitVec 64 :=
    zero_extend (m := 64) (bool_to_bit (zopz0zI_s x y))
  let js_afterCmp : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.amoWordSelectMaskVReg then flag else js.vregs r }
  have hcmp_run :
      (JoltISA.execInstr
        (.SLT (.vreg JoltISA.amoWordSelectMaskVReg) (.vreg lhs) (.vreg rhs))).run
          js =
        .ok RETIRE_SUCCESS js_afterCmp := by
    rw [amo_word_slt_run_vreg_vreg_vreg JoltISA.amoWordSelectMaskVReg lhs rhs js]
    unfold js_afterCmp flag
    rw [hlhs, hrhs]
  refine ⟨js_afterCmp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tail
    unfold amoWordSelectRustCompareProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterCmp hcmp_run]
  · rfl
  · change
      (if JoltISA.amoWordSelectMaskVReg = JoltISA.amoWordSelectMaskVReg then flag
        else js.vregs JoltISA.amoWordSelectMaskVReg) =
      zero_extend (m := 64) (bool_to_bit (zopz0zI_s x y))
    rw [if_pos rfl]
  · change
      (if JoltISA.amoWordSelectOldVReg = JoltISA.amoWordSelectMaskVReg then flag
        else js.vregs JoltISA.amoWordSelectOldVReg) = old
    rw [if_neg (by decide), hold]
  · change
      (if JoltISA.amoWordSelectDwordVReg = JoltISA.amoWordSelectMaskVReg then flag
        else js.vregs JoltISA.amoWordSelectDwordVReg) = dword
    rw [if_neg (by decide), hdword]
  · change
      (if JoltISA.amoWordSelectShiftVReg = JoltISA.amoWordSelectMaskVReg then flag
        else js.vregs JoltISA.amoWordSelectShiftVReg) = shift
    rw [if_neg (by decide), hshift]

/-- An unsigned word-select comparison phase writes the unsigned less-than flag
between two prepared virtual operands. -/
theorem amo_word_rust_select_sltu_compare_phase_run_vreg_vreg
    (lhs rhs : JoltISA.VReg) (js : SailJoltState)
    (x y old dword shift : BitVec 64)
    (hlhs : js.vregs lhs = x)
    (hrhs : js.vregs rhs = y)
    (hold : js.vregs JoltISA.amoWordSelectOldVReg = old)
    (hdword : js.vregs JoltISA.amoWordSelectDwordVReg = dword)
    (hshift : js.vregs JoltISA.amoWordSelectShiftVReg = shift) :
    ∃ js_afterCmp : SailJoltState,
      AmoWordSelectRustCompareStep
        (fun dst lhs rhs => .SLTU dst lhs rhs) (.vreg lhs) (.vreg rhs)
        old dword shift (jolt_sltu_value x y) js js_afterCmp := by
  let flag : BitVec 64 := jolt_sltu_value x y
  let js_afterCmp : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.amoWordSelectMaskVReg then flag else js.vregs r }
  have hcmp_run :
      (JoltISA.execInstr
        (.SLTU (.vreg JoltISA.amoWordSelectMaskVReg) (.vreg lhs) (.vreg rhs))).run
          js =
        .ok RETIRE_SUCCESS js_afterCmp := by
    rw [amo_word_sltu_run_vreg_vreg_vreg JoltISA.amoWordSelectMaskVReg lhs rhs js]
    unfold js_afterCmp flag
    rw [hlhs, hrhs]
  refine ⟨js_afterCmp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tail
    unfold amoWordSelectRustCompareProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterCmp hcmp_run]
  · rfl
  · change
      (if JoltISA.amoWordSelectMaskVReg = JoltISA.amoWordSelectMaskVReg then flag
        else js.vregs JoltISA.amoWordSelectMaskVReg) = jolt_sltu_value x y
    rw [if_pos rfl]
  · change
      (if JoltISA.amoWordSelectOldVReg = JoltISA.amoWordSelectMaskVReg then flag
        else js.vregs JoltISA.amoWordSelectOldVReg) = old
    rw [if_neg (by decide), hold]
  · change
      (if JoltISA.amoWordSelectDwordVReg = JoltISA.amoWordSelectMaskVReg then flag
        else js.vregs JoltISA.amoWordSelectDwordVReg) = dword
    rw [if_neg (by decide), hdword]
  · change
      (if JoltISA.amoWordSelectShiftVReg = JoltISA.amoWordSelectMaskVReg then flag
        else js.vregs JoltISA.amoWordSelectShiftVReg) = shift
    rw [if_neg (by decide), hshift]

/-- The word-select tail turns the comparison flag into the selected new value
while preserving the prelude registers needed by the postlude. -/
theorem amo_word_rust_select_tail_phase_run
    (rs2 : regidx) (js : SailJoltState)
    (rs2Val old flag dword shift : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hold : js.vregs JoltISA.amoWordSelectOldVReg = old)
    (hflag : js.vregs JoltISA.amoWordSelectMaskVReg = flag)
    (hdword : js.vregs JoltISA.amoWordSelectDwordVReg = dword)
    (hshift : js.vregs JoltISA.amoWordSelectShiftVReg = shift) :
    ∃ js_afterTail : SailJoltState,
      AmoWordSelectRustTailStep rs2 old dword shift
        ((rs2Val - old) * flag + old) js js_afterTail := by
  let delta : BitVec 64 := rs2Val - old
  let scaled : BitVec 64 := delta * flag
  let js_afterSub : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.amoWordSelectNewVReg then delta else js.vregs r }
  let js_afterMul : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.amoWordSelectNewVReg then scaled else js_afterSub.vregs r }
  let js_afterAdd : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.amoWordSelectNewVReg then scaled + old else js_afterMul.vregs r }
  have hsub_new : js_afterSub.vregs JoltISA.amoWordSelectNewVReg = delta := by
    change
      (if JoltISA.amoWordSelectNewVReg = JoltISA.amoWordSelectNewVReg then delta
        else js.vregs JoltISA.amoWordSelectNewVReg) = delta
    rw [if_pos rfl]
  have hsub_flag : js_afterSub.vregs JoltISA.amoWordSelectMaskVReg = flag := by
    change
      (if JoltISA.amoWordSelectMaskVReg = JoltISA.amoWordSelectNewVReg then delta
        else js.vregs JoltISA.amoWordSelectMaskVReg) = flag
    rw [if_neg (by decide), hflag]
  have hsub_old : js_afterSub.vregs JoltISA.amoWordSelectOldVReg = old := by
    change
      (if JoltISA.amoWordSelectOldVReg = JoltISA.amoWordSelectNewVReg then delta
        else js.vregs JoltISA.amoWordSelectOldVReg) = old
    rw [if_neg (by decide), hold]
  have hsub_dword : js_afterSub.vregs JoltISA.amoWordSelectDwordVReg = dword := by
    change
      (if JoltISA.amoWordSelectDwordVReg = JoltISA.amoWordSelectNewVReg then delta
        else js.vregs JoltISA.amoWordSelectDwordVReg) = dword
    rw [if_neg (by decide), hdword]
  have hsub_shift : js_afterSub.vregs JoltISA.amoWordSelectShiftVReg = shift := by
    change
      (if JoltISA.amoWordSelectShiftVReg = JoltISA.amoWordSelectNewVReg then delta
        else js.vregs JoltISA.amoWordSelectShiftVReg) = shift
    rw [if_neg (by decide), hshift]
  have hsub_run :
      (JoltISA.execInstr
        (.SUB (.vreg JoltISA.amoWordSelectNewVReg)
          (.xreg rs2) (.vreg JoltISA.amoWordSelectOldVReg))).run js =
        .ok RETIRE_SUCCESS js_afterSub := by
    rw [JoltISA.sub_run_vreg_xreg_vreg
      JoltISA.amoWordSelectNewVReg rs2 JoltISA.amoWordSelectOldVReg js rs2Val hrs2]
    unfold js_afterSub delta
    rw [hold]
  have hmul_new : js_afterMul.vregs JoltISA.amoWordSelectNewVReg = scaled := by
    change
      (if JoltISA.amoWordSelectNewVReg = JoltISA.amoWordSelectNewVReg then scaled
        else js_afterSub.vregs JoltISA.amoWordSelectNewVReg) = scaled
    rw [if_pos rfl]
  have hmul_old : js_afterMul.vregs JoltISA.amoWordSelectOldVReg = old := by
    change
      (if JoltISA.amoWordSelectOldVReg = JoltISA.amoWordSelectNewVReg then scaled
        else js_afterSub.vregs JoltISA.amoWordSelectOldVReg) = old
    rw [if_neg (by decide), hsub_old]
  have hmul_dword : js_afterMul.vregs JoltISA.amoWordSelectDwordVReg = dword := by
    change
      (if JoltISA.amoWordSelectDwordVReg = JoltISA.amoWordSelectNewVReg then scaled
        else js_afterSub.vregs JoltISA.amoWordSelectDwordVReg) = dword
    rw [if_neg (by decide), hsub_dword]
  have hmul_shift : js_afterMul.vregs JoltISA.amoWordSelectShiftVReg = shift := by
    change
      (if JoltISA.amoWordSelectShiftVReg = JoltISA.amoWordSelectNewVReg then scaled
        else js_afterSub.vregs JoltISA.amoWordSelectShiftVReg) = shift
    rw [if_neg (by decide), hsub_shift]
  have hmul_run :
      (JoltISA.execInstr
        (.MUL (.vreg JoltISA.amoWordSelectNewVReg)
          (.vreg JoltISA.amoWordSelectNewVReg)
          (.vreg JoltISA.amoWordSelectMaskVReg))).run js_afterSub =
        .ok RETIRE_SUCCESS js_afterMul := by
    rw [JoltISA.mul_run_vreg_vreg_vreg
      JoltISA.amoWordSelectNewVReg JoltISA.amoWordSelectNewVReg JoltISA.amoWordSelectMaskVReg
      js_afterSub]
    unfold js_afterMul scaled
    rw [hsub_new, hsub_flag]
  have hadd_result :
      js_afterAdd.vregs JoltISA.amoWordSelectNewVReg =
        (rs2Val - old) * flag + old := by
    change
      (if JoltISA.amoWordSelectNewVReg = JoltISA.amoWordSelectNewVReg then scaled + old
        else js_afterMul.vregs JoltISA.amoWordSelectNewVReg) =
      (rs2Val - old) * flag + old
    rw [if_pos rfl]
  have hadd_old : js_afterAdd.vregs JoltISA.amoWordSelectOldVReg = old := by
    change
      (if JoltISA.amoWordSelectOldVReg = JoltISA.amoWordSelectNewVReg then scaled + old
        else js_afterMul.vregs JoltISA.amoWordSelectOldVReg) = old
    rw [if_neg (by decide), hmul_old]
  have hadd_dword : js_afterAdd.vregs JoltISA.amoWordSelectDwordVReg = dword := by
    change
      (if JoltISA.amoWordSelectDwordVReg = JoltISA.amoWordSelectNewVReg then scaled + old
        else js_afterMul.vregs JoltISA.amoWordSelectDwordVReg) = dword
    rw [if_neg (by decide), hmul_dword]
  have hadd_shift : js_afterAdd.vregs JoltISA.amoWordSelectShiftVReg = shift := by
    change
      (if JoltISA.amoWordSelectShiftVReg = JoltISA.amoWordSelectNewVReg then scaled + old
        else js_afterMul.vregs JoltISA.amoWordSelectShiftVReg) = shift
    rw [if_neg (by decide), hmul_shift]
  have hadd_run :
      (JoltISA.execInstr
        (.ADD (.vreg JoltISA.amoWordSelectNewVReg)
          (.vreg JoltISA.amoWordSelectNewVReg)
          (.vreg JoltISA.amoWordSelectOldVReg))).run js_afterMul =
        .ok RETIRE_SUCCESS js_afterAdd := by
    rw [JoltISA.add_run_vreg_vreg_vreg
      JoltISA.amoWordSelectNewVReg JoltISA.amoWordSelectNewVReg JoltISA.amoWordSelectOldVReg
      js_afterMul]
    unfold js_afterAdd
    rw [hmul_new, hmul_old]
  refine ⟨js_afterAdd, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tail
    unfold amoWordSelectRustTailProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterSub hsub_run]
    rw [JoltISA.execProgram_instr_run_retire
      _ _ js_afterSub js_afterMul hmul_run]
    rw [JoltISA.execProgram_instr_run_retire
      _ _ js_afterMul js_afterAdd hadd_run]
  · rfl
  · exact hadd_result
  · exact hadd_old
  · exact hadd_dword
  · exact hadd_shift
theorem amo_word_rust_select_middle_phase_run
    (extend : JoltISA.Dst → JoltISA.Src → JoltISA.Instr)
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src) (rs2 : regidx)
    (js : SailJoltState)
    (rs2Val old dword shift rs2Ext oldExt flag result : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hext :
      ∃ js_afterExt : SailJoltState,
        AmoWordSelectRustExtendStep extend rs2 old dword shift rs2Ext oldExt
          js js_afterExt)
    (hcompare :
      ∀ js_afterExt : SailJoltState,
        AmoWordSelectRustExtendStep extend rs2 old dword shift rs2Ext oldExt
          js js_afterExt →
        ∃ js_afterCmp : SailJoltState,
          AmoWordSelectRustCompareStep cmpInstr cmpLhs cmpRhs old dword shift
            flag js_afterExt js_afterCmp)
    (hresult : (rs2Val - old) * flag + old = result) :
    ∃ js_afterMiddle : SailJoltState,
      AmoWordSelectRustMiddleStep extend cmpInstr cmpLhs cmpRhs rs2
        old dword shift result js js_afterMiddle := by
  obtain ⟨js_afterExt, hext_step⟩ := hext
  obtain ⟨js_afterCmp, hcmp_step⟩ := hcompare js_afterExt hext_step
  have hrs2_afterCmp :
      rX_bits rs2 js_afterCmp.sail = .ok rs2Val js_afterCmp.sail := by
    rw [hcmp_step.sail, hext_step.sail]
    exact hrs2
  obtain ⟨js_afterTail, htail_step⟩ :=
    amo_word_rust_select_tail_phase_run rs2 js_afterCmp rs2Val old flag dword shift
      hrs2_afterCmp hcmp_step.old_vreg hcmp_step.flag_vreg
      hcmp_step.dword_vreg hcmp_step.shift_vreg
  refine ⟨js_afterTail, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tail
    unfold amoWordSelectRustMiddleProgram
    rw [hext_step.run
      (amoWordSelectRustCompareProgram cmpInstr cmpLhs cmpRhs
        (amoWordSelectRustTailProgram rs2 tail))]
    rw [hcmp_step.run (amoWordSelectRustTailProgram rs2 tail)]
    rw [htail_step.run tail]
  · rw [htail_step.sail, hcmp_step.sail, hext_step.sail]
  · rw [htail_step.result_vreg, hresult]
  · exact htail_step.old_vreg
  · exact htail_step.dword_vreg
  · exact htail_step.shift_vreg

/-- `AMOMIN.W`'s select middle chooses the full `rs2` scratch value exactly
when the low words satisfy signed `<`. -/
theorem amo_word_rust_select_min_middle_run
    (rs2 : regidx) (js_pre : SailJoltState)
    (rs2Val old dword shift : BitVec 64)
    (hrs2 : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail)
    (hold : js_pre.vregs JoltISA.amoWordSelectOldVReg = old)
    (hdword : js_pre.vregs JoltISA.amoWordSelectDwordVReg = dword)
    (hshift : js_pre.vregs JoltISA.amoWordSelectShiftVReg = shift) :
    ∃ js_afterMiddle : SailJoltState,
      AmoWordSelectRustMiddleStep
        (fun dst src => .VirtualSignExtendWord dst src)
        (fun dst lhs rhs => .SLT dst lhs rhs)
        (.vreg JoltISA.amoWordSelectNewVReg) (.vreg JoltISA.amoWordSelectMaskVReg) rs2
        old dword shift
        (if (zopz0zI_s
            (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
            (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
          rs2Val
        else
          old)
        js_pre js_afterMiddle := by
  exact
    amo_word_rust_select_middle_phase_run
      (fun dst src => .VirtualSignExtendWord dst src)
      (fun dst lhs rhs => .SLT dst lhs rhs)
      (.vreg JoltISA.amoWordSelectNewVReg) (.vreg JoltISA.amoWordSelectMaskVReg) rs2
      js_pre rs2Val old dword shift
      (sign_extend (m := 64)
        (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
      (sign_extend (m := 64)
        (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
      (zero_extend (m := 64)
        (bool_to_bit
          (zopz0zI_s
            (sign_extend (m := 64)
              (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
            (sign_extend (m := 64)
              (Sail.BitVec.extractLsb old 31 0 : BitVec 32)))))
      (if (zopz0zI_s
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
        rs2Val
      else
        old)
      hrs2
      (amo_word_rust_select_signed_extend_phase_run rs2 js_pre rs2Val old dword
        shift hrs2 hold hdword hshift)
      (fun js_afterExt hext_step =>
        amo_word_rust_select_slt_compare_phase_run_vreg_vreg
          JoltISA.amoWordSelectNewVReg JoltISA.amoWordSelectMaskVReg js_afterExt
          (sign_extend (m := 64)
            (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
          (sign_extend (m := 64)
            (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
          old dword shift hext_step.rs2_ext_vreg hext_step.old_ext_vreg
          hext_step.old_vreg hext_step.dword_vreg hext_step.shift_vreg)
      (amo_word_select_value_of_slt_sext old rs2Val)

/-- `AMOMAX.W`'s select middle chooses the full `rs2` scratch value exactly
when the low words satisfy signed `>`. -/
theorem amo_word_rust_select_max_middle_run
    (rs2 : regidx) (js_pre : SailJoltState)
    (rs2Val old dword shift : BitVec 64)
    (hrs2 : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail)
    (hold : js_pre.vregs JoltISA.amoWordSelectOldVReg = old)
    (hdword : js_pre.vregs JoltISA.amoWordSelectDwordVReg = dword)
    (hshift : js_pre.vregs JoltISA.amoWordSelectShiftVReg = shift) :
    ∃ js_afterMiddle : SailJoltState,
      AmoWordSelectRustMiddleStep
        (fun dst src => .VirtualSignExtendWord dst src)
        (fun dst lhs rhs => .SLT dst lhs rhs)
        (.vreg JoltISA.amoWordSelectMaskVReg) (.vreg JoltISA.amoWordSelectNewVReg) rs2
        old dword shift
        (if (zopz0zK_s
            (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
            (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
          rs2Val
        else
          old)
        js_pre js_afterMiddle := by
  exact
    amo_word_rust_select_middle_phase_run
      (fun dst src => .VirtualSignExtendWord dst src)
      (fun dst lhs rhs => .SLT dst lhs rhs)
      (.vreg JoltISA.amoWordSelectMaskVReg) (.vreg JoltISA.amoWordSelectNewVReg) rs2
      js_pre rs2Val old dword shift
      (sign_extend (m := 64)
        (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
      (sign_extend (m := 64)
        (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
      (zero_extend (m := 64)
        (bool_to_bit
          (zopz0zI_s
            (sign_extend (m := 64)
              (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
            (sign_extend (m := 64)
              (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)))))
      (if (zopz0zK_s
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
        rs2Val
      else
        old)
      hrs2
      (amo_word_rust_select_signed_extend_phase_run rs2 js_pre rs2Val old dword
        shift hrs2 hold hdword hshift)
      (fun js_afterExt hext_step =>
        amo_word_rust_select_slt_compare_phase_run_vreg_vreg
          JoltISA.amoWordSelectMaskVReg JoltISA.amoWordSelectNewVReg js_afterExt
          (sign_extend (m := 64)
            (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
          (sign_extend (m := 64)
            (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
          old dword shift hext_step.old_ext_vreg hext_step.rs2_ext_vreg
          hext_step.old_vreg hext_step.dword_vreg hext_step.shift_vreg)
      (amo_word_select_value_of_sgt_sext old rs2Val)

/-- `AMOMINU.W`'s select middle chooses the full `rs2` scratch value exactly
when the low words satisfy unsigned `<`. -/
theorem amo_word_rust_select_minu_middle_run
    (rs2 : regidx) (js_pre : SailJoltState)
    (rs2Val old dword shift : BitVec 64)
    (hrs2 : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail)
    (hold : js_pre.vregs JoltISA.amoWordSelectOldVReg = old)
    (hdword : js_pre.vregs JoltISA.amoWordSelectDwordVReg = dword)
    (hshift : js_pre.vregs JoltISA.amoWordSelectShiftVReg = shift) :
    ∃ js_afterMiddle : SailJoltState,
      AmoWordSelectRustMiddleStep
        (fun dst src => .VirtualZeroExtendWord dst src)
        (fun dst lhs rhs => .SLTU dst lhs rhs)
        (.vreg JoltISA.amoWordSelectNewVReg) (.vreg JoltISA.amoWordSelectMaskVReg) rs2
        old dword shift
        (if (zopz0zI_u
            (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
            (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
          rs2Val
        else
          old)
        js_pre js_afterMiddle := by
  exact
    amo_word_rust_select_middle_phase_run
      (fun dst src => .VirtualZeroExtendWord dst src)
      (fun dst lhs rhs => .SLTU dst lhs rhs)
      (.vreg JoltISA.amoWordSelectNewVReg) (.vreg JoltISA.amoWordSelectMaskVReg) rs2
      js_pre rs2Val old dword shift
      (zero_extend (m := 64)
        (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
      (zero_extend (m := 64)
        (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
      (jolt_sltu_value
        (zero_extend (m := 64)
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
        (zero_extend (m := 64)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32)))
      (if (zopz0zI_u
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
        rs2Val
      else
        old)
      hrs2
      (amo_word_rust_select_unsigned_extend_phase_run rs2 js_pre rs2Val old dword
        shift hrs2 hold hdword hshift)
      (fun js_afterExt hext_step =>
        amo_word_rust_select_sltu_compare_phase_run_vreg_vreg
          JoltISA.amoWordSelectNewVReg JoltISA.amoWordSelectMaskVReg js_afterExt
          (zero_extend (m := 64)
            (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
          (zero_extend (m := 64)
            (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
          old dword shift hext_step.rs2_ext_vreg hext_step.old_ext_vreg
          hext_step.old_vreg hext_step.dword_vreg hext_step.shift_vreg)
      (amo_word_select_value_of_sltu_zext old rs2Val)

/-- `AMOMAXU.W`'s select middle chooses the full `rs2` scratch value exactly
when the low words satisfy unsigned `>`. -/
theorem amo_word_rust_select_maxu_middle_run
    (rs2 : regidx) (js_pre : SailJoltState)
    (rs2Val old dword shift : BitVec 64)
    (hrs2 : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail)
    (hold : js_pre.vregs JoltISA.amoWordSelectOldVReg = old)
    (hdword : js_pre.vregs JoltISA.amoWordSelectDwordVReg = dword)
    (hshift : js_pre.vregs JoltISA.amoWordSelectShiftVReg = shift) :
    ∃ js_afterMiddle : SailJoltState,
      AmoWordSelectRustMiddleStep
        (fun dst src => .VirtualZeroExtendWord dst src)
        (fun dst lhs rhs => .SLTU dst lhs rhs)
        (.vreg JoltISA.amoWordSelectMaskVReg) (.vreg JoltISA.amoWordSelectNewVReg) rs2
        old dword shift
        (if (zopz0zK_u
            (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
            (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
          rs2Val
        else
          old)
        js_pre js_afterMiddle := by
  exact
    amo_word_rust_select_middle_phase_run
      (fun dst src => .VirtualZeroExtendWord dst src)
      (fun dst lhs rhs => .SLTU dst lhs rhs)
      (.vreg JoltISA.amoWordSelectMaskVReg) (.vreg JoltISA.amoWordSelectNewVReg) rs2
      js_pre rs2Val old dword shift
      (zero_extend (m := 64)
        (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
      (zero_extend (m := 64)
        (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
      (jolt_sltu_value
        (zero_extend (m := 64)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
        (zero_extend (m := 64)
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)))
      (if (zopz0zK_u
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
        rs2Val
      else
        old)
      hrs2
      (amo_word_rust_select_unsigned_extend_phase_run rs2 js_pre rs2Val old dword
        shift hrs2 hold hdword hshift)
      (fun js_afterExt hext_step =>
        amo_word_rust_select_sltu_compare_phase_run_vreg_vreg
          JoltISA.amoWordSelectMaskVReg JoltISA.amoWordSelectNewVReg js_afterExt
          (zero_extend (m := 64)
            (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
          (zero_extend (m := 64)
            (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
          old dword shift hext_step.old_ext_vreg hext_step.rs2_ext_vreg
          hext_step.old_vreg hext_step.dword_vreg hext_step.shift_vreg)
      (amo_word_select_value_of_sgtu_zext old rs2Val)

/-- After the common word prelude, the `AMOMIN.W` middle block is ready for the
shared word-select program helper. -/
theorem amo_word_rust_select_min_middle_after_pre
    (rs2 : regidx) (js : SailJoltState) (addr rs2Val : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail) :
    ∀ js_pre : SailJoltState,
      js_pre.sail = js.sail →
      js_pre.vregs JoltISA.amoWordSelectDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr) →
      js_pre.vregs JoltISA.amoWordSelectShiftVReg =
        shift_bits_left addr (3 : BitVec 6) →
      js_pre.vregs JoltISA.amoWordSelectOldVReg =
        amoWordShiftedOld js.sail addr →
      ∃ js_afterMiddle : SailJoltState,
        AmoWordSelectRustMiddleStep
          (fun dst src => .VirtualSignExtendWord dst src)
          (fun dst lhs rhs => .SLT dst lhs rhs)
          (.vreg JoltISA.amoWordSelectNewVReg) (.vreg JoltISA.amoWordSelectMaskVReg) rs2
          (amoWordShiftedOld js.sail addr)
          (loaded_dword_at js.sail (amoWordBase addr))
          (shift_bits_left addr (3 : BitVec 6))
          (if (zopz0zI_s
              (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
              (Sail.BitVec.extractLsb (amoWordShiftedOld js.sail addr) 31 0 :
                BitVec 32) : Bool) then
            rs2Val
          else
            amoWordShiftedOld js.sail addr)
          js_pre js_afterMiddle := by
  intro js_pre hpre_sail hpre_dword hpre_shift hpre_old
  have hrs2_pre : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail := by
    rw [hpre_sail]
    exact hrs2
  exact
    amo_word_rust_select_min_middle_run rs2 js_pre rs2Val
      (amoWordShiftedOld js.sail addr)
      (loaded_dword_at js.sail (amoWordBase addr))
      (shift_bits_left addr (3 : BitVec 6))
      hrs2_pre hpre_old hpre_dword hpre_shift

/-- After the common word prelude, the `AMOMAX.W` middle block is ready for the
shared word-select program helper. -/
theorem amo_word_rust_select_max_middle_after_pre
    (rs2 : regidx) (js : SailJoltState) (addr rs2Val : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail) :
    ∀ js_pre : SailJoltState,
      js_pre.sail = js.sail →
      js_pre.vregs JoltISA.amoWordSelectDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr) →
      js_pre.vregs JoltISA.amoWordSelectShiftVReg =
        shift_bits_left addr (3 : BitVec 6) →
      js_pre.vregs JoltISA.amoWordSelectOldVReg =
        amoWordShiftedOld js.sail addr →
      ∃ js_afterMiddle : SailJoltState,
        AmoWordSelectRustMiddleStep
          (fun dst src => .VirtualSignExtendWord dst src)
          (fun dst lhs rhs => .SLT dst lhs rhs)
          (.vreg JoltISA.amoWordSelectMaskVReg) (.vreg JoltISA.amoWordSelectNewVReg) rs2
          (amoWordShiftedOld js.sail addr)
          (loaded_dword_at js.sail (amoWordBase addr))
          (shift_bits_left addr (3 : BitVec 6))
          (if (zopz0zK_s
              (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
              (Sail.BitVec.extractLsb (amoWordShiftedOld js.sail addr) 31 0 :
                BitVec 32) : Bool) then
            rs2Val
          else
            amoWordShiftedOld js.sail addr)
          js_pre js_afterMiddle := by
  intro js_pre hpre_sail hpre_dword hpre_shift hpre_old
  have hrs2_pre : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail := by
    rw [hpre_sail]
    exact hrs2
  exact
    amo_word_rust_select_max_middle_run rs2 js_pre rs2Val
      (amoWordShiftedOld js.sail addr)
      (loaded_dword_at js.sail (amoWordBase addr))
      (shift_bits_left addr (3 : BitVec 6))
      hrs2_pre hpre_old hpre_dword hpre_shift

/-- After the common word prelude, the `AMOMINU.W` middle block is ready for
the shared word-select program helper. -/
theorem amo_word_rust_select_minu_middle_after_pre
    (rs2 : regidx) (js : SailJoltState) (addr rs2Val : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail) :
    ∀ js_pre : SailJoltState,
      js_pre.sail = js.sail →
      js_pre.vregs JoltISA.amoWordSelectDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr) →
      js_pre.vregs JoltISA.amoWordSelectShiftVReg =
        shift_bits_left addr (3 : BitVec 6) →
      js_pre.vregs JoltISA.amoWordSelectOldVReg =
        amoWordShiftedOld js.sail addr →
      ∃ js_afterMiddle : SailJoltState,
        AmoWordSelectRustMiddleStep
          (fun dst src => .VirtualZeroExtendWord dst src)
          (fun dst lhs rhs => .SLTU dst lhs rhs)
          (.vreg JoltISA.amoWordSelectNewVReg) (.vreg JoltISA.amoWordSelectMaskVReg) rs2
          (amoWordShiftedOld js.sail addr)
          (loaded_dword_at js.sail (amoWordBase addr))
          (shift_bits_left addr (3 : BitVec 6))
          (if (zopz0zI_u
              (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
              (Sail.BitVec.extractLsb (amoWordShiftedOld js.sail addr) 31 0 :
                BitVec 32) : Bool) then
            rs2Val
          else
            amoWordShiftedOld js.sail addr)
          js_pre js_afterMiddle := by
  intro js_pre hpre_sail hpre_dword hpre_shift hpre_old
  have hrs2_pre : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail := by
    rw [hpre_sail]
    exact hrs2
  exact
    amo_word_rust_select_minu_middle_run rs2 js_pre rs2Val
      (amoWordShiftedOld js.sail addr)
      (loaded_dword_at js.sail (amoWordBase addr))
      (shift_bits_left addr (3 : BitVec 6))
      hrs2_pre hpre_old hpre_dword hpre_shift

/-- After the common word prelude, the `AMOMAXU.W` middle block is ready for
the shared word-select program helper. -/
theorem amo_word_rust_select_maxu_middle_after_pre
    (rs2 : regidx) (js : SailJoltState) (addr rs2Val : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail) :
    ∀ js_pre : SailJoltState,
      js_pre.sail = js.sail →
      js_pre.vregs JoltISA.amoWordSelectDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr) →
      js_pre.vregs JoltISA.amoWordSelectShiftVReg =
        shift_bits_left addr (3 : BitVec 6) →
      js_pre.vregs JoltISA.amoWordSelectOldVReg =
        amoWordShiftedOld js.sail addr →
      ∃ js_afterMiddle : SailJoltState,
        AmoWordSelectRustMiddleStep
          (fun dst src => .VirtualZeroExtendWord dst src)
          (fun dst lhs rhs => .SLTU dst lhs rhs)
          (.vreg JoltISA.amoWordSelectMaskVReg) (.vreg JoltISA.amoWordSelectNewVReg) rs2
          (amoWordShiftedOld js.sail addr)
          (loaded_dword_at js.sail (amoWordBase addr))
          (shift_bits_left addr (3 : BitVec 6))
          (if (zopz0zK_u
              (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
              (Sail.BitVec.extractLsb (amoWordShiftedOld js.sail addr) 31 0 :
                BitVec 32) : Bool) then
            rs2Val
          else
            amoWordShiftedOld js.sail addr)
          js_pre js_afterMiddle := by
  intro js_pre hpre_sail hpre_dword hpre_shift hpre_old
  have hrs2_pre : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail := by
    rw [hpre_sail]
    exact hrs2
  exact
    amo_word_rust_select_maxu_middle_run rs2 js_pre rs2Val
      (amoWordShiftedOld js.sail addr)
      (loaded_dword_at js.sail (amoWordBase addr))
      (shift_bits_left addr (3 : BitVec 6))
      hrs2_pre hpre_old hpre_dword hpre_shift
theorem amo_word_rust_select_program_concrete_aligned
    (op : amoop)
    (extend : JoltISA.Dst → JoltISA.Src → JoltISA.Instr)
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src)
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr result64 : BitVec 64) (result : BitVec 32)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (h_mem : AmoMemoryContext op 4 (amoWordBase addr) addr js.sail)
    (h_align : addr &&& (3 : BitVec 64) = 0)
    (hresult : (Sail.BitVec.extractLsb result64 31 0 : BitVec 32) = result)
    (hmiddle :
      ∀ js_pre : SailJoltState,
        js_pre.sail = js.sail →
        js_pre.vregs JoltISA.amoWordSelectDwordVReg =
          loaded_dword_at js.sail (amoWordBase addr) →
        js_pre.vregs JoltISA.amoWordSelectShiftVReg =
          shift_bits_left addr (3 : BitVec 6) →
        js_pre.vregs JoltISA.amoWordSelectOldVReg =
          amoWordShiftedOld js.sail addr →
        ∃ js_afterMiddle : SailJoltState,
          AmoWordSelectRustMiddleStep extend cmpInstr cmpLhs cmpRhs rs2
            (amoWordShiftedOld js.sail addr)
            (loaded_dword_at js.sail (amoWordBase addr))
            (shift_bits_left addr (3 : BitVec 6))
            result64 js_pre js_afterMiddle) :
    ∃ jsf : SailJoltState,
      (JoltISA.execProgram
        (JoltISA.amoWordSelectRustProgram extend cmpInstr cmpLhs cmpRhs
          rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail = amoWordFinalSailState rd js.sail addr result := by
  let post : JoltISA.Program :=
    amoWordSelectRustMiddleProgram extend cmpInstr cmpLhs cmpRhs rs2
      (JoltISA.amoPost64ProgramWithScratch rs1 rd (.vreg JoltISA.amoWordSelectNewVReg)
        JoltISA.amoWordSelectDwordVReg JoltISA.amoWordSelectShiftVReg
        JoltISA.amoWordSelectMaskVReg JoltISA.amoWordSelectOldVReg
        JoltISA.amoWordSelectInlineTmpVReg)
  have h_no_ovf := amo_word_base_no_ovf addr
  obtain ⟨js_pre, hpre_run, hpre_sail, hpre_dword, hpre_shift, hpre_old⟩ :=
    amo_word_rust_select_pre64_aligned_run post rs1 js hcfg addr hrs1 h_mem
      h_no_ovf h_align
  have hpre_old_named :
      js_pre.vregs JoltISA.amoWordSelectOldVReg = amoWordShiftedOld js.sail addr := by
    exact hpre_old
  obtain ⟨js_afterMiddle, hmiddle_step⟩ :=
    hmiddle js_pre hpre_sail hpre_dword hpre_shift hpre_old_named
  have hmiddle_sail : js_afterMiddle.sail = js.sail := by
    rw [hmiddle_step.sail, hpre_sail]
  obtain ⟨jsf, hpost_run, hpost_sail⟩ :=
    amo_word_rust_select_post64_vreg_aligned_run rs1 rd
      js js_afterMiddle hcfg addr result64 hrs1 h_mem h_no_ovf h_align
      hmiddle_sail hmiddle_step.result_vreg
      hmiddle_step.dword_vreg hmiddle_step.shift_vreg hmiddle_step.old_vreg
  refine ⟨jsf, ?_, ?_⟩
  · unfold JoltISA.amoWordSelectRustProgram
    change
      (JoltISA.execProgram
        (JoltISA.amoPre64ProgramWithScratch rs1 JoltISA.amoWordSelectOldVReg
          JoltISA.amoWordSelectDwordVReg JoltISA.amoWordSelectShiftVReg
          JoltISA.amoWordSelectNewVReg post)).run js =
        .ok RETIRE_SUCCESS jsf
    rw [hpre_run]
    rw [hmiddle_step.run
      (JoltISA.amoPost64ProgramWithScratch rs1 rd (.vreg JoltISA.amoWordSelectNewVReg)
        JoltISA.amoWordSelectDwordVReg JoltISA.amoWordSelectShiftVReg
        JoltISA.amoWordSelectMaskVReg JoltISA.amoWordSelectOldVReg
        JoltISA.amoWordSelectInlineTmpVReg)]
    exact hpost_run
  · rw [hpost_sail, hresult]

/-- Shared misaligned concrete execution for word AMO select expansions. -/
theorem amo_word_rust_select_program_concrete_misaligned
    (extend : JoltISA.Dst → JoltISA.Src → JoltISA.Instr)
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src)
    (rs2 rs1 rd : regidx) (js : SailJoltState) (addr : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (h_align : addr &&& (3 : BitVec 64) ≠ 0) :
    (JoltISA.execProgram
      (JoltISA.amoWordSelectRustProgram extend cmpInstr cmpLhs cmpRhs
        rs2 rs1 rd)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr addr, ExceptionType.E_SAMO_Addr_Align ())) js := by
  unfold JoltISA.amoWordSelectRustProgram
  unfold JoltISA.amoPre64ProgramWithScratch
  exact amo_word_assert_prefix_misaligned_run rs1 _ js addr hrs1 h_align

/-- Shared aligned public branch for word AMO select expansions. -/
theorem amo_word_rust_select_program_eq_sail_aligned
    (op : amoop)
    (extend : JoltISA.Dst → JoltISA.Src → JoltISA.Instr)
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src)
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val result64 : BitVec 64) (result : BitVec 32)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryContext op 4 (amoWordBase addr) addr js.sail)
    (h_align : addr &&& (3 : BitVec 64) = 0)
    (hnot_cas : (op == amoop.AMOCAS) = false)
    (hresult_extract :
      (Sail.BitVec.extractLsb result64 31 0 : BitVec 32) = result)
    (hmiddle :
      ∀ js_pre : SailJoltState,
        js_pre.sail = js.sail →
        js_pre.vregs JoltISA.amoWordSelectDwordVReg =
          loaded_dword_at js.sail (amoWordBase addr) →
        js_pre.vregs JoltISA.amoWordSelectShiftVReg =
          shift_bits_left addr (3 : BitVec 6) →
        js_pre.vregs JoltISA.amoWordSelectOldVReg =
          amoWordShiftedOld js.sail addr →
        ∃ js_afterMiddle : SailJoltState,
          AmoWordSelectRustMiddleStep extend cmpInstr cmpLhs cmpRhs rs2
            (amoWordShiftedOld js.sail addr)
            (loaded_dword_at js.sail (amoWordBase addr))
            (shift_bits_left addr (3 : BitVec 6))
            result64 js_pre js_afterMiddle)
    (hsail_result :
      amoWordSailResult op
        (show BitVec (4 * 8) from
          trunc (m := (((4 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
        (BitVec.setWidth (4 * 8) (loaded_word_at js.sail addr)) =
      result) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoWordSelectRustProgram extend cmpInstr cmpLhs cmpRhs
        rs2 rs1 rd)).run js) =
      (execute_AMO op false false rs2 rs1 4 rd).run js.sail := by
  rcases amo_word_rust_select_program_concrete_aligned
      op extend cmpInstr cmpLhs cmpRhs rs2 rs1 rd js hcfg addr result64
      result hrs1 h_mem h_align hresult_extract hmiddle with
    ⟨jsf, hjolt, hjolt_sail⟩
  have hsail :=
    execute_AMO_word_non_cas_aligned
      op rs2 rs1 rd js hcfg addr rs2Val result
      hrs1 hrs2 hrd h_mem h_align hnot_cas hsail_result
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail, hsail]

/-- Shared misaligned public branch for word AMO select expansions. -/
theorem amo_word_rust_select_program_eq_sail_misaligned
    (op : amoop)
    (extend : JoltISA.Dst → JoltISA.Src → JoltISA.Instr)
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src)
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_align : addr &&& (3 : BitVec 64) ≠ 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoWordSelectRustProgram extend cmpInstr cmpLhs cmpRhs
        rs2 rs1 rd)).run js) =
      (execute_AMO op false false rs2 rs1 4 rd).run js.sail := by
  have hjolt :=
    amo_word_rust_select_program_concrete_misaligned
      extend cmpInstr cmpLhs cmpRhs rs2 rs1 rd js addr hrs1 h_align
  have hsail :=
    execute_AMO_word_misaligned
      op rs2 rs1 rd js hcfg addr rs2Val hrs1 hrs2 h_align
  rw [hjolt]
  simp only [projectResult, project]
  symm
  exact hsail

/-- Shared full theorem for word AMO select expansions. -/
theorem amo_word_rust_select_program_eq_sail
    (op : amoop)
    (extend : JoltISA.Dst → JoltISA.Src → JoltISA.Instr)
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src)
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val result64 : BitVec 64) (result : BitVec 32)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryContext op 4 (amoWordBase addr) addr js.sail)
    (hnot_cas : (op == amoop.AMOCAS) = false)
    (hresult_extract :
      addr &&& (3 : BitVec 64) = 0 →
        (Sail.BitVec.extractLsb result64 31 0 : BitVec 32) = result)
    (hmiddle :
      ∀ js_pre : SailJoltState,
        js_pre.sail = js.sail →
        js_pre.vregs JoltISA.amoWordSelectDwordVReg =
          loaded_dword_at js.sail (amoWordBase addr) →
        js_pre.vregs JoltISA.amoWordSelectShiftVReg =
          shift_bits_left addr (3 : BitVec 6) →
        js_pre.vregs JoltISA.amoWordSelectOldVReg =
          amoWordShiftedOld js.sail addr →
        ∃ js_afterMiddle : SailJoltState,
          AmoWordSelectRustMiddleStep extend cmpInstr cmpLhs cmpRhs rs2
            (amoWordShiftedOld js.sail addr)
            (loaded_dword_at js.sail (amoWordBase addr))
            (shift_bits_left addr (3 : BitVec 6))
            result64 js_pre js_afterMiddle)
    (hsail_result :
      amoWordSailResult op
        (show BitVec (4 * 8) from
          trunc (m := (((4 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
        (BitVec.setWidth (4 * 8) (loaded_word_at js.sail addr)) =
      result) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoWordSelectRustProgram extend cmpInstr cmpLhs cmpRhs
        rs2 rs1 rd)).run js) =
      (execute_AMO op false false rs2 rs1 4 rd).run js.sail := by
  by_cases h_align : addr &&& (3 : BitVec 64) = 0
  · exact
      amo_word_rust_select_program_eq_sail_aligned
        op extend cmpInstr cmpLhs cmpRhs rs2 rs1 rd js hcfg addr rs2Val
        result64 result hrs1 hrs2 hrd h_mem h_align hnot_cas
        (hresult_extract h_align) hmiddle hsail_result
  · exact
      amo_word_rust_select_program_eq_sail_misaligned
        op extend cmpInstr cmpLhs cmpRhs rs2 rs1 rd js hcfg addr rs2Val
        hrs1 hrs2 h_align

end AtomicFamily

end
