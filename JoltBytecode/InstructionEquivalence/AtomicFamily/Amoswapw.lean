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

/-- Rust-shaped `AMOSWAP.W` prelude with the allocator order `v_mask`, `v_dword`, `v_shift`, `v_rd`. -/
theorem amo_word_swap_pre64_aligned_run
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
        (JoltISA.amoPre64ProgramWithScratch rs1 JoltISA.amoWordSwapOldVReg
          JoltISA.amoWordSwapDwordVReg JoltISA.amoWordSwapShiftVReg
          JoltISA.amoWordSwapInlineTmpVReg tail)).run js =
        (JoltISA.execProgram tail).run js_pre ∧
      js_pre.sail = js.sail ∧
      js_pre.vregs JoltISA.amoWordSwapDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr) ∧
      js_pre.vregs JoltISA.amoWordSwapShiftVReg =
        shift_bits_left addr (3 : BitVec 6) ∧
      js_pre.vregs JoltISA.amoWordSwapOldVReg =
        shift_bits_right
          (loaded_dword_at js.sail (amoWordBase addr))
          (Sail.BitVec.extractLsb
            (shift_bits_left addr (3 : BitVec 6)) 5 0) := by
  have hassert :=
    amo_word_virtual_assert_aligned_run rs1 js addr hrs1 h_align
  obtain ⟨js_base, _hrs1_base, hbase_sail, hbase_shift_raw,
      _hbase_preserves, hbase_run⟩ :=
    JoltISA.exists_state_after_andi_run_vreg_xreg_of_sail_eq
      JoltISA.amoWordSwapShiftVReg rs1 (-8 : BitVec 12) js js.sail addr rfl hrs1 (by unfold WritableVReg; decide)
  have hbase_shift :
      js_base.vregs JoltISA.amoWordSwapShiftVReg = amoWordBase addr := by
    rw [hbase_shift_raw]
    exact amo_word_base_mask addr
  have hcfg_base : JoltConfig js_base.sail := by
    rw [hbase_sail]
    exact hcfg
  have hld :
      (JoltISA.execInstr
        (.LD (.vreg JoltISA.amoWordSwapDwordVReg)
          (.vreg JoltISA.amoWordSwapShiftVReg) (0 : BitVec 12))).run js_base =
        .ok RETIRE_SUCCESS
          { sail := js_base.sail
            vregs := fun r =>
              if r = JoltISA.amoWordSwapDwordVReg then
                loaded_dword_at js_base.sail (amoWordBase addr)
              else js_base.vregs r } := by
    exact
      vreg_LD_run_of_aligned_dword_phys
        JoltISA.amoWordSwapDwordVReg JoltISA.amoWordSwapShiftVReg js_base
        (amoWordBase addr) hbase_shift
        hcfg_base.cur_privilege hcfg_base.mstatus_mprv
        (amo_word_base_aligned_access addr h_no_ovf)
        (by rw [hbase_sail]; exact AmoMemoryContext.jolt_load_mem h_mem)
        (by unfold WritableVReg; decide)
  let js_load : SailJoltState :=
    { sail := js_base.sail
      vregs := fun r =>
        if r = JoltISA.amoWordSwapDwordVReg then
          loaded_dword_at js_base.sail (amoWordBase addr)
        else js_base.vregs r }
  have hld_named :
      (JoltISA.execInstr
        (.LD (.vreg JoltISA.amoWordSwapDwordVReg)
          (.vreg JoltISA.amoWordSwapShiftVReg) (0 : BitVec 12))).run js_base =
        .ok RETIRE_SUCCESS js_load := by
    exact hld
  have hload_sail : js_load.sail = js.sail := by
    exact hbase_sail
  have hload_dword :
      js_load.vregs JoltISA.amoWordSwapDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr) := by
    change
      (if JoltISA.amoWordSwapDwordVReg = JoltISA.amoWordSwapDwordVReg then
          loaded_dword_at js_base.sail (amoWordBase addr)
        else js_base.vregs JoltISA.amoWordSwapDwordVReg) =
        loaded_dword_at js.sail (amoWordBase addr)
    rw [if_pos rfl, hbase_sail]
  have hload_shift :
      js_load.vregs JoltISA.amoWordSwapShiftVReg = amoWordBase addr := by
    change
      (if JoltISA.amoWordSwapShiftVReg = JoltISA.amoWordSwapDwordVReg then
          loaded_dword_at js_base.sail (amoWordBase addr)
        else js_base.vregs JoltISA.amoWordSwapShiftVReg) =
        amoWordBase addr
    rw [if_neg (by decide)]
    exact hbase_shift
  have hrs1_load :
      rX_bits rs1 js_load.sail = .ok addr js_load.sail := by
    rw [hload_sail]
    exact hrs1
  have hmuli :
      (JoltISA.execInstr
        (.VirtualMULI (.vreg JoltISA.amoWordSwapShiftVReg)
          (.xreg rs1) (8 : BitVec 64))).run js_load =
      .ok RETIRE_SUCCESS
        { sail := js_load.sail
          vregs := fun r =>
            if r = JoltISA.amoWordSwapShiftVReg then
              jolt_virtual_muli_value addr (8 : BitVec 64)
            else js_load.vregs r } :=
    amo_word_virtual_muli_run_vreg_xreg
      JoltISA.amoWordSwapShiftVReg rs1 (8 : BitVec 64) js_load addr hrs1_load
      (by unfold WritableVReg; decide)
  let js_shift : SailJoltState :=
    { sail := js_load.sail
      vregs := fun r =>
        if r = JoltISA.amoWordSwapShiftVReg then
          jolt_virtual_muli_value addr (8 : BitVec 64)
        else js_load.vregs r }
  have hmuli_named :
      (JoltISA.execInstr
        (.VirtualMULI (.vreg JoltISA.amoWordSwapShiftVReg)
          (.xreg rs1) (8 : BitVec 64))).run js_load =
      .ok RETIRE_SUCCESS js_shift := by
    exact hmuli
  have hshift_sail : js_shift.sail = js.sail := by
    exact hload_sail
  have hshift_dword :
      js_shift.vregs JoltISA.amoWordSwapDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr) := by
    change
      (if JoltISA.amoWordSwapDwordVReg = JoltISA.amoWordSwapShiftVReg then
          jolt_virtual_muli_value addr (8 : BitVec 64)
        else js_load.vregs JoltISA.amoWordSwapDwordVReg) =
        loaded_dword_at js.sail (amoWordBase addr)
    rw [if_neg (by decide)]
    exact hload_dword
  have hshift_shift :
      js_shift.vregs JoltISA.amoWordSwapShiftVReg =
        shift_bits_left addr (3 : BitVec 6) := by
    change
      (if JoltISA.amoWordSwapShiftVReg = JoltISA.amoWordSwapShiftVReg then
          jolt_virtual_muli_value addr (8 : BitVec 64)
        else js_load.vregs JoltISA.amoWordSwapShiftVReg) =
        shift_bits_left addr (3 : BitVec 6)
    rw [if_pos rfl]
    exact JoltISA.virtual_muli_eight_eq_shift_left_three addr
  have hbitmask :
      (JoltISA.execInstr
        (.VirtualShiftRightBitmask (.vreg JoltISA.amoWordSwapInlineTmpVReg)
          (.vreg JoltISA.amoWordSwapShiftVReg))).run js_shift =
      .ok RETIRE_SUCCESS
        { sail := js_shift.sail
          vregs := fun r =>
            if r = JoltISA.amoWordSwapInlineTmpVReg then
              jolt_virtual_shift_right_bitmask_value
                (js_shift.vregs JoltISA.amoWordSwapShiftVReg)
            else js_shift.vregs r } :=
    JoltISA.virtual_shift_right_bitmask_run_vreg_vreg
      JoltISA.amoWordSwapInlineTmpVReg JoltISA.amoWordSwapShiftVReg js_shift
      (by unfold WritableVReg; decide)
  let js_bitmask : SailJoltState :=
    { sail := js_shift.sail
      vregs := fun r =>
        if r = JoltISA.amoWordSwapInlineTmpVReg then
          jolt_virtual_shift_right_bitmask_value
            (js_shift.vregs JoltISA.amoWordSwapShiftVReg)
        else js_shift.vregs r }
  have hbitmask_named :
      (JoltISA.execInstr
        (.VirtualShiftRightBitmask (.vreg JoltISA.amoWordSwapInlineTmpVReg)
          (.vreg JoltISA.amoWordSwapShiftVReg))).run js_shift =
      .ok RETIRE_SUCCESS js_bitmask := by
    exact hbitmask
  have hbitmask_sail : js_bitmask.sail = js.sail := by
    exact hshift_sail
  have hbitmask_dword :
      js_bitmask.vregs JoltISA.amoWordSwapDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr) := by
    change
      (if JoltISA.amoWordSwapDwordVReg = JoltISA.amoWordSwapInlineTmpVReg then
          jolt_virtual_shift_right_bitmask_value
            (js_shift.vregs JoltISA.amoWordSwapShiftVReg)
        else js_shift.vregs JoltISA.amoWordSwapDwordVReg) =
        loaded_dword_at js.sail (amoWordBase addr)
    rw [if_neg (by decide)]
    exact hshift_dword
  have hbitmask_shift :
      js_bitmask.vregs JoltISA.amoWordSwapShiftVReg =
        shift_bits_left addr (3 : BitVec 6) := by
    change
      (if JoltISA.amoWordSwapShiftVReg = JoltISA.amoWordSwapInlineTmpVReg then
          jolt_virtual_shift_right_bitmask_value
            (js_shift.vregs JoltISA.amoWordSwapShiftVReg)
        else js_shift.vregs JoltISA.amoWordSwapShiftVReg) =
        shift_bits_left addr (3 : BitVec 6)
    rw [if_neg (by decide)]
    exact hshift_shift
  have hbitmask_tmp :
      js_bitmask.vregs JoltISA.amoWordSwapInlineTmpVReg =
        jolt_virtual_shift_right_bitmask_value
          (shift_bits_left addr (3 : BitVec 6)) := by
    change
      (if JoltISA.amoWordSwapInlineTmpVReg = JoltISA.amoWordSwapInlineTmpVReg then
          jolt_virtual_shift_right_bitmask_value
            (js_shift.vregs JoltISA.amoWordSwapShiftVReg)
        else js_shift.vregs JoltISA.amoWordSwapInlineTmpVReg) =
        jolt_virtual_shift_right_bitmask_value
          (shift_bits_left addr (3 : BitVec 6))
    rw [if_pos rfl, hshift_shift]
  have hsrl :
      (JoltISA.execInstr
        (.VirtualSRL (.vreg JoltISA.amoWordSwapOldVReg)
          (.vreg JoltISA.amoWordSwapDwordVReg)
          (.vreg JoltISA.amoWordSwapInlineTmpVReg))).run js_bitmask =
      .ok RETIRE_SUCCESS
        { sail := js_bitmask.sail
          vregs := fun r =>
            if r = JoltISA.amoWordSwapOldVReg then
              jolt_virtual_srl_value
                (js_bitmask.vregs JoltISA.amoWordSwapDwordVReg)
                (js_bitmask.vregs JoltISA.amoWordSwapInlineTmpVReg)
            else js_bitmask.vregs r } :=
    JoltISA.virtual_srl_run_vreg_vreg_vreg
      JoltISA.amoWordSwapOldVReg JoltISA.amoWordSwapDwordVReg
      JoltISA.amoWordSwapInlineTmpVReg js_bitmask
      (by unfold WritableVReg; decide)
  let js_pre : SailJoltState :=
    { sail := js_bitmask.sail
      vregs := fun r =>
        if r = JoltISA.amoWordSwapOldVReg then
          jolt_virtual_srl_value
            (js_bitmask.vregs JoltISA.amoWordSwapDwordVReg)
            (js_bitmask.vregs JoltISA.amoWordSwapInlineTmpVReg)
        else js_bitmask.vregs r }
  have hsrl_named :
      (JoltISA.execInstr
        (.VirtualSRL (.vreg JoltISA.amoWordSwapOldVReg)
          (.vreg JoltISA.amoWordSwapDwordVReg)
          (.vreg JoltISA.amoWordSwapInlineTmpVReg))).run js_bitmask =
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
      (if JoltISA.amoWordSwapDwordVReg = JoltISA.amoWordSwapOldVReg then
          jolt_virtual_srl_value
            (js_bitmask.vregs JoltISA.amoWordSwapDwordVReg)
            (js_bitmask.vregs JoltISA.amoWordSwapInlineTmpVReg)
        else js_bitmask.vregs JoltISA.amoWordSwapDwordVReg) =
        loaded_dword_at js.sail (amoWordBase addr)
    rw [if_neg (by decide)]
    exact hbitmask_dword
  · change
      (if JoltISA.amoWordSwapShiftVReg = JoltISA.amoWordSwapOldVReg then
          jolt_virtual_srl_value
            (js_bitmask.vregs JoltISA.amoWordSwapDwordVReg)
            (js_bitmask.vregs JoltISA.amoWordSwapInlineTmpVReg)
        else js_bitmask.vregs JoltISA.amoWordSwapShiftVReg) =
        shift_bits_left addr (3 : BitVec 6)
    rw [if_neg (by decide)]
    exact hbitmask_shift
  · change
      (if JoltISA.amoWordSwapOldVReg = JoltISA.amoWordSwapOldVReg then
          jolt_virtual_srl_value
            (js_bitmask.vregs JoltISA.amoWordSwapDwordVReg)
            (js_bitmask.vregs JoltISA.amoWordSwapInlineTmpVReg)
        else js_bitmask.vregs JoltISA.amoWordSwapOldVReg) =
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
theorem amo_word_swap_mask32_prefix_run
    (js : SailJoltState) (s : SailState) (shift64 dword old : BitVec 64)
    (h_sail : js.sail = s)
    (h_shift : js.vregs JoltISA.amoWordSwapShiftVReg = shift64)
    (h_dword : js.vregs JoltISA.amoWordSwapDwordVReg = dword)
    (h_old : js.vregs JoltISA.amoWordSwapOldVReg = old) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs JoltISA.amoWordSwapMaskVReg =
        (0x00000000FFFFFFFF : BitVec 64) ∧
      js'.vregs JoltISA.amoWordSwapShiftVReg = shift64 ∧
      js'.vregs JoltISA.amoWordSwapDwordVReg = dword ∧
      js'.vregs JoltISA.amoWordSwapOldVReg = old ∧
      js'.vregs JoltISA.amoNewVReg = js.vregs JoltISA.amoNewVReg ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.ORI (.vreg JoltISA.amoWordSwapMaskVReg)
            (.xreg (regidx.Regidx 0)) (-1 : BitVec 12)) <|
           .instr (.VirtualSRLI (.vreg JoltISA.amoWordSwapMaskVReg)
            (.vreg JoltISA.amoWordSwapMaskVReg)
            (JoltISA.srliBitmask (32 : BitVec 6))) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  obtain ⟨js_ones, _hx0, hones_sail_raw, hones_mask_raw,
      hones_preserves, hones_run⟩ :=
    JoltISA.exists_state_after_ori_run_vreg_xreg_of_sail_eq
      JoltISA.amoWordSwapMaskVReg (regidx.Regidx 0) (-1 : BitVec 12)
      js s (0#64) h_sail (amo_word_read_x0_eq_zero s) (by unfold WritableVReg; decide)
  have hones_sail : js_ones.sail = s := by
    rw [hones_sail_raw, h_sail]
  have hones_mask : js_ones.vregs JoltISA.amoWordSwapMaskVReg = (-1 : BitVec 64) := by
    rw [hones_mask_raw]
    exact amo_word_seed_mask_value
  have hones_shift : js_ones.vregs JoltISA.amoWordSwapShiftVReg = shift64 := by
    rw [hones_preserves JoltISA.amoWordSwapShiftVReg (by decide)]
    exact h_shift
  have hones_dword : js_ones.vregs JoltISA.amoWordSwapDwordVReg = dword := by
    rw [hones_preserves JoltISA.amoWordSwapDwordVReg (by decide)]
    exact h_dword
  have hones_old : js_ones.vregs JoltISA.amoWordSwapOldVReg = old := by
    rw [hones_preserves JoltISA.amoWordSwapOldVReg (by decide)]
    exact h_old
  have hones_new :
      js_ones.vregs JoltISA.amoNewVReg = js.vregs JoltISA.amoNewVReg := by
    rw [hones_preserves JoltISA.amoNewVReg (by decide)]
  obtain ⟨js_mask, hmask_sail_raw, hmask_raw, hmask_preserves,
      hmask_tail⟩ :=
    JoltISA.exists_state_after_srli_block_run_vreg_vreg
      JoltISA.amoWordSwapMaskVReg JoltISA.amoWordSwapMaskVReg (32 : BitVec 6) js_ones
      (by unfold WritableVReg; decide)
  refine ⟨js_mask, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmask_sail_raw, hones_sail]
  · rw [hmask_raw, hones_mask]
    exact amo_word_low_word_mask_value
  · rw [hmask_preserves JoltISA.amoWordSwapShiftVReg (by decide)]
    exact hones_shift
  · rw [hmask_preserves JoltISA.amoWordSwapDwordVReg (by decide)]
    exact hones_dword
  · rw [hmask_preserves JoltISA.amoWordSwapOldVReg (by decide)]
    exact hones_old
  · rw [hmask_preserves JoltISA.amoNewVReg (by decide)]
    exact hones_new
  · intro tail
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_ones hones_run]
    have htail := hmask_tail tail
    unfold JoltISA.srliBlock at htail
    exact htail

/-- The postlude's mask-shift block turns the low-word mask into the selected
word-lane mask. -/
theorem amo_word_swap_shift_mask_prefix_run
    (js : SailJoltState) (s : SailState) (shift64 dword old : BitVec 64)
    (h_sail : js.sail = s)
    (h_mask : js.vregs JoltISA.amoWordSwapMaskVReg =
      (0x00000000FFFFFFFF : BitVec 64))
    (h_shift : js.vregs JoltISA.amoWordSwapShiftVReg = shift64)
    (h_dword : js.vregs JoltISA.amoWordSwapDwordVReg = dword)
    (h_old : js.vregs JoltISA.amoWordSwapOldVReg = old) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs JoltISA.amoWordSwapMaskVReg =
        shift_bits_left (0x00000000FFFFFFFF : BitVec 64)
          (Sail.BitVec.extractLsb shift64 5 0) ∧
      js'.vregs JoltISA.amoWordSwapShiftVReg = shift64 ∧
      js'.vregs JoltISA.amoWordSwapDwordVReg = dword ∧
      js'.vregs JoltISA.amoWordSwapOldVReg = old ∧
      js'.vregs JoltISA.amoNewVReg = js.vregs JoltISA.amoNewVReg ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.VirtualPow2 (.vreg JoltISA.amoWordSwapInlineTmpVReg)
            (.vreg JoltISA.amoWordSwapShiftVReg)) <|
           .instr (.MUL (.vreg JoltISA.amoWordSwapMaskVReg)
            (.vreg JoltISA.amoWordSwapMaskVReg)
            (.vreg JoltISA.amoWordSwapInlineTmpVReg)) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  obtain ⟨js', h_sail_raw, h_mask_raw, h_preserves, htail⟩ :=
    JoltISA.exists_state_after_sll_block_run_vreg_vreg_vreg
      JoltISA.amoWordSwapMaskVReg JoltISA.amoWordSwapMaskVReg
      JoltISA.amoWordSwapShiftVReg JoltISA.amoWordSwapInlineTmpVReg js (by decide) (by unfold WritableVReg; decide) (by unfold WritableVReg; decide)
  refine ⟨js', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_sail_raw, h_sail]
  · rw [h_mask_raw, h_mask, h_shift]
  · rw [h_preserves JoltISA.amoWordSwapShiftVReg (by decide) (by decide)]
    exact h_shift
  · rw [h_preserves JoltISA.amoWordSwapDwordVReg (by decide) (by decide)]
    exact h_dword
  · rw [h_preserves JoltISA.amoWordSwapOldVReg (by decide) (by decide)]
    exact h_old
  · rw [h_preserves JoltISA.amoNewVReg (by decide) (by decide)]
  · intro tail
    have h := htail tail
    unfold JoltISA.sllBlock at h
    exact h

/-- The postlude shifts the new word value from `rs2` into the selected dword
lane while preserving the prepared mask and old word. -/
theorem amo_word_swap_shift_new_prefix_run
    (rs2 : regidx) (js : SailJoltState) (s : SailState)
    (rs2Val shift64 shiftedMask dword old : BitVec 64)
    (h_sail : js.sail = s)
    (hrs2 : rX_bits rs2 s = .ok rs2Val s)
    (h_mask : js.vregs JoltISA.amoWordSwapMaskVReg = shiftedMask)
    (h_shift : js.vregs JoltISA.amoWordSwapShiftVReg = shift64)
    (h_dword : js.vregs JoltISA.amoWordSwapDwordVReg = dword)
    (h_old : js.vregs JoltISA.amoWordSwapOldVReg = old) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs JoltISA.amoWordSwapShiftVReg =
        shift_bits_left rs2Val (Sail.BitVec.extractLsb shift64 5 0) ∧
      js'.vregs JoltISA.amoWordSwapMaskVReg = shiftedMask ∧
      js'.vregs JoltISA.amoWordSwapDwordVReg = dword ∧
      js'.vregs JoltISA.amoWordSwapOldVReg = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.VirtualPow2 (.vreg JoltISA.amoWordSwapInlineTmpVReg)
            (.vreg JoltISA.amoWordSwapShiftVReg)) <|
           .instr (.MUL (.vreg JoltISA.amoWordSwapShiftVReg)
            (.xreg rs2) (.vreg JoltISA.amoWordSwapInlineTmpVReg)) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  have hrs2_current : rX_bits rs2 js.sail = .ok rs2Val js.sail := by
    rw [h_sail]
    exact hrs2
  obtain ⟨js', _hrs2, h_sail_raw, h_shift_raw, h_preserves, htail⟩ :=
    JoltISA.exists_state_after_sll_block_run_vreg_xreg_vreg
      JoltISA.amoWordSwapShiftVReg rs2 JoltISA.amoWordSwapShiftVReg
      JoltISA.amoWordSwapInlineTmpVReg js rs2Val hrs2_current (by unfold WritableVReg; decide) (by unfold WritableVReg; decide)
  refine ⟨js', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_sail_raw, h_sail]
  · rw [h_shift_raw, h_shift]
  · rw [h_preserves JoltISA.amoWordSwapMaskVReg (by decide) (by decide)]
    exact h_mask
  · rw [h_preserves JoltISA.amoWordSwapDwordVReg (by decide) (by decide)]
    exact h_dword
  · rw [h_preserves JoltISA.amoWordSwapOldVReg (by decide) (by decide)]
    exact h_old
  · intro tail
    have h := htail tail
    unfold JoltISA.sllBlock at h
    exact h

/-- The postlude shifts a virtual-register new word value into the selected
dword lane while preserving the prepared mask and old word. -/
theorem amo_word_swap_shift_new_vreg_prefix_run
    (new : JoltISA.VReg) (js : SailJoltState) (s : SailState)
    (newValue shift64 shiftedMask dword old : BitVec 64)
    (h_sail : js.sail = s)
    (h_new : js.vregs new = newValue)
    (h_mask : js.vregs JoltISA.amoWordSwapMaskVReg = shiftedMask)
    (h_shift : js.vregs JoltISA.amoWordSwapShiftVReg = shift64)
    (h_dword : js.vregs JoltISA.amoWordSwapDwordVReg = dword)
    (h_old : js.vregs JoltISA.amoWordSwapOldVReg = old)
    (hnew_ne_tmp : new ≠ JoltISA.amoWordSwapInlineTmpVReg) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs JoltISA.amoWordSwapShiftVReg =
        shift_bits_left newValue (Sail.BitVec.extractLsb shift64 5 0) ∧
      js'.vregs JoltISA.amoWordSwapMaskVReg = shiftedMask ∧
      js'.vregs JoltISA.amoWordSwapDwordVReg = dword ∧
      js'.vregs JoltISA.amoWordSwapOldVReg = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.VirtualPow2 (.vreg JoltISA.amoWordSwapInlineTmpVReg)
            (.vreg JoltISA.amoWordSwapShiftVReg)) <|
           .instr (.MUL (.vreg JoltISA.amoWordSwapShiftVReg)
            (.vreg new) (.vreg JoltISA.amoWordSwapInlineTmpVReg)) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  obtain ⟨js', h_sail_raw, h_shift_raw, h_preserves, htail⟩ :=
    JoltISA.exists_state_after_sll_block_run_vreg_vreg_vreg
      JoltISA.amoWordSwapShiftVReg new JoltISA.amoWordSwapShiftVReg
      JoltISA.amoWordSwapInlineTmpVReg js hnew_ne_tmp (by unfold WritableVReg; decide) (by unfold WritableVReg; decide)
  refine ⟨js', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_sail_raw, h_sail]
  · rw [h_shift_raw, h_new, h_shift]
  · rw [h_preserves JoltISA.amoWordSwapMaskVReg (by decide) (by decide)]
    exact h_mask
  · rw [h_preserves JoltISA.amoWordSwapDwordVReg (by decide) (by decide)]
    exact h_dword
  · rw [h_preserves JoltISA.amoWordSwapOldVReg (by decide) (by decide)]
    exact h_old
  · intro tail
    have h := htail tail
    unfold JoltISA.sllBlock at h
    exact h

/-- The XOR/AND/XOR postlude block splices the shifted new word into the loaded
dword and preserves the shifted old word. -/
theorem amo_word_swap_splice_block_run
    (js : SailJoltState) (s : SailState) (addr newValue old : BitVec 64)
    (hsetup : StoreSplice.WordStoreSetup addr (amoWordBase addr))
    (h_sail : js.sail = s)
    (h_dword :
      js.vregs JoltISA.amoWordSwapDwordVReg =
        loaded_dword_at s (amoWordBase addr))
    (h_shift :
      js.vregs JoltISA.amoWordSwapShiftVReg =
        shift_bits_left newValue
          (Sail.BitVec.extractLsb
            (shift_bits_left addr (3 : BitVec 6)) 5 0))
    (h_mask :
      js.vregs JoltISA.amoWordSwapMaskVReg =
        shift_bits_left (0x00000000FFFFFFFF : BitVec 64)
          (Sail.BitVec.extractLsb
            (shift_bits_left addr (3 : BitVec 6)) 5 0))
    (h_old : js.vregs JoltISA.amoWordSwapOldVReg = old) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs JoltISA.amoWordSwapDwordVReg =
        amoWordSplicedDword s addr newValue ∧
      js'.vregs JoltISA.amoWordSwapOldVReg = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.XOR (.vreg JoltISA.amoWordSwapShiftVReg)
            (.vreg JoltISA.amoWordSwapDwordVReg)
            (.vreg JoltISA.amoWordSwapShiftVReg)) <|
           .instr (.AND (.vreg JoltISA.amoWordSwapShiftVReg)
            (.vreg JoltISA.amoWordSwapShiftVReg)
            (.vreg JoltISA.amoWordSwapMaskVReg)) <|
           .instr (.XOR (.vreg JoltISA.amoWordSwapDwordVReg)
            (.vreg JoltISA.amoWordSwapDwordVReg)
            (.vreg JoltISA.amoWordSwapShiftVReg)) tail)).run js =
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
      JoltISA.amoWordSwapShiftVReg JoltISA.amoWordSwapDwordVReg
      JoltISA.amoWordSwapShiftVReg js dword shiftedNew h_dword h_shift (by unfold WritableVReg; decide)
  have hxor_sail : js_xor.sail = s := by
    rw [hxor_sail_raw, h_sail]
  have hxor_shift : js_xor.vregs JoltISA.amoWordSwapShiftVReg = dword ^^^ shiftedNew := by
    exact hxor_shift_raw
  have hxor_mask : js_xor.vregs JoltISA.amoWordSwapMaskVReg = shiftedMask := by
    rw [hxor_preserves JoltISA.amoWordSwapMaskVReg (by decide)]
    exact h_mask
  have hxor_dword : js_xor.vregs JoltISA.amoWordSwapDwordVReg = dword := by
    rw [hxor_preserves JoltISA.amoWordSwapDwordVReg (by decide)]
    exact h_dword
  have hxor_old : js_xor.vregs JoltISA.amoWordSwapOldVReg = old := by
    rw [hxor_preserves JoltISA.amoWordSwapOldVReg (by decide)]
    exact h_old
  obtain ⟨js_and, hand_sail_raw, hand_shift_raw, hand_preserves,
      hand_run⟩ :=
    amo_word_exists_state_after_and_run_vreg_vreg_vreg
      JoltISA.amoWordSwapShiftVReg JoltISA.amoWordSwapShiftVReg JoltISA.amoWordSwapMaskVReg
      js_xor (dword ^^^ shiftedNew) shiftedMask hxor_shift hxor_mask
      (by unfold WritableVReg; decide)
  have hand_sail : js_and.sail = s := by
    rw [hand_sail_raw, hxor_sail]
  have hand_shift : js_and.vregs JoltISA.amoWordSwapShiftVReg =
      (dword ^^^ shiftedNew) &&& shiftedMask := by
    exact hand_shift_raw
  have hand_dword : js_and.vregs JoltISA.amoWordSwapDwordVReg = dword := by
    rw [hand_preserves JoltISA.amoWordSwapDwordVReg (by decide)]
    exact hxor_dword
  have hand_old : js_and.vregs JoltISA.amoWordSwapOldVReg = old := by
    rw [hand_preserves JoltISA.amoWordSwapOldVReg (by decide)]
    exact hxor_old
  obtain ⟨js_splice, hsplice_sail_raw, hsplice_dword_raw,
      hsplice_preserves, hxor2_run⟩ :=
    JoltISA.exists_state_after_xor_run_vreg_vreg_vreg
      JoltISA.amoWordSwapDwordVReg JoltISA.amoWordSwapDwordVReg
      JoltISA.amoWordSwapShiftVReg js_and dword
      ((dword ^^^ shiftedNew) &&& shiftedMask) hand_dword hand_shift (by unfold WritableVReg; decide)
  have hspliced_value := amo_word_splice_shifted_eq s addr newValue hsetup
  refine ⟨js_splice, ?_, ?_, ?_, ?_⟩
  · rw [hsplice_sail_raw, hand_sail]
  · rw [hsplice_dword_raw]
    exact hspliced_value
  · rw [hsplice_preserves JoltISA.amoWordSwapOldVReg (by decide)]
    exact hand_old
  · intro tail
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_xor hxor_run]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_xor js_and hand_run]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_and js_splice hxor2_run]

/-- The postlude recomputes the enclosing dword base before storing it. -/
theorem amo_word_swap_store_base_prefix_run
    (rs1 : regidx) (js : SailJoltState) (s : SailState)
    (addr dwordNew old : BitVec 64)
    (h_sail : js.sail = s)
    (hrs1 : rX_bits rs1 s = .ok addr s)
    (h_dword : js.vregs JoltISA.amoWordSwapDwordVReg = dwordNew)
    (h_old : js.vregs JoltISA.amoWordSwapOldVReg = old) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs JoltISA.amoWordSwapMaskVReg = amoWordBase addr ∧
      js'.vregs JoltISA.amoWordSwapDwordVReg = dwordNew ∧
      js'.vregs JoltISA.amoWordSwapOldVReg = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.ANDI (.vreg JoltISA.amoWordSwapMaskVReg)
            (.xreg rs1) (-8 : BitVec 12)) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  obtain ⟨js', _hrs1, h_sail_raw, h_base_raw, h_preserves, hrun⟩ :=
    JoltISA.exists_state_after_andi_run_vreg_xreg_of_sail_eq
      JoltISA.amoWordSwapMaskVReg rs1 (-8 : BitVec 12) js s addr h_sail hrs1 (by unfold WritableVReg; decide)
  refine ⟨js', ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_sail_raw, h_sail]
  · rw [h_base_raw]
    exact amo_word_base_mask addr
  · rw [h_preserves JoltISA.amoWordSwapDwordVReg (by decide)]
    exact h_dword
  · rw [h_preserves JoltISA.amoWordSwapOldVReg (by decide)]
    exact h_old
  · intro tail
    rw [JoltISA.execProgram_instr_run_retire _ _ js js' hrun]

/-- The dword store instruction writes the spliced dword and preserves the
virtual-register file for the final writeback. -/
theorem amo_word_swap_sd_spliced_dword_run
    {op : amoop}
    (js : SailJoltState) (s : SailState) (addr dwordNew old : BitVec 64)
    (hcfg : JoltConfig s)
    (h_mem : AmoMemoryContext op 4 (amoWordBase addr) addr s)
    (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
    (h_sail : js.sail = s)
    (h_base : js.vregs JoltISA.amoWordSwapMaskVReg = amoWordBase addr)
    (h_dword : js.vregs JoltISA.amoWordSwapDwordVReg = dwordNew)
    (h_old : js.vregs JoltISA.amoWordSwapOldVReg = old) :
    ∃ js',
      js'.sail = state_after_dword_store s (amoWordBase addr) dwordNew ∧
      js'.vregs JoltISA.amoWordSwapOldVReg = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.SD (.vreg JoltISA.amoWordSwapMaskVReg)
            (.vreg JoltISA.amoWordSwapDwordVReg) (0 : BitVec 12)) tail)).run js =
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
      vmem_write_addr (Virtaddr (js.vregs JoltISA.amoWordSwapMaskVReg +
          sign_extend (m := 64) (0 : BitVec 12))) 8
        (js.vregs JoltISA.amoWordSwapDwordVReg)
        (Store Data) false false false js.sail =
      .ok (Ok true) (state_after_dword_store s (amoWordBase addr) dwordNew) := by
    rw [h_sail, h_base, h_dword, amo_word_zero_offset_addr (amoWordBase addr)]
    exact hwrite_dword
  let js' : SailJoltState :=
    { sail := state_after_dword_store s (amoWordBase addr) dwordNew
      vregs := js.vregs }
  have hsd_align :
      (js.vregs JoltISA.amoWordSwapMaskVReg + sign_extend (m := 64) (0 : BitVec 12)) &&&
          (7 : BitVec 64) =
        0 := by
    rw [h_base, amo_word_zero_offset_addr (amoWordBase addr)]
    exact amo_word_base_aligned addr
  have hsd :
      (JoltISA.execInstr
        (.SD (.vreg JoltISA.amoWordSwapMaskVReg)
          (.vreg JoltISA.amoWordSwapDwordVReg) (0 : BitVec 12))).run js =
        .ok RETIRE_SUCCESS js' :=
    JoltISA.execInstr_sd_vreg_run_of_write
      JoltISA.amoWordSwapMaskVReg JoltISA.amoWordSwapDwordVReg (0 : BitVec 12)
      js (state_after_dword_store s (amoWordBase addr) dwordNew) hsd_align hwrite_current
  refine ⟨js', rfl, ?_, ?_⟩
  · exact h_old
  · intro tail
    rw [JoltISA.execProgram_instr_run_retire _ _ js js' hsd]

/-- The final postlude instruction writes the sign-extended old word to `rd`. -/
theorem amo_word_swap_writeback_old_run
    (rd : regidx) (js : SailJoltState) (s : SailState)
    (addr : BitVec 64) (result : BitVec 32) (old : BitVec 64)
    (h_sail : js.sail = state_after_word_store s addr result)
    (h_old : js.vregs JoltISA.amoWordSwapOldVReg = old)
    (h_old_word :
      sign_extend (m := 64)
        ((Sail.BitVec.extractLsb old 31 0) : BitVec 32) =
      sign_extend (m := 64) (loaded_word_at s addr)) :
    ∃ js',
      js'.sail = amoWordFinalSailState rd s addr result ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.VirtualSignExtendWord (.xreg rd)
            (.vreg JoltISA.amoWordSwapOldVReg)) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  obtain ⟨writebackState, hwriteback, hwriteback_state⟩ :=
    amo_word_writeback_old_shape rd s addr result
  have hwriteback_current :
      wX_bits rd
        (sign_extend (m := 64)
          ((Sail.BitVec.extractLsb
            (js.vregs JoltISA.amoWordSwapOldVReg) 31 0) : BitVec 32))
        js.sail =
      .ok () writebackState := by
    rw [h_sail, h_old, h_old_word]
    exact hwriteback
  let js' : SailJoltState := { sail := writebackState, vregs := js.vregs }
  have hsext :
      (JoltISA.execInstr
        (.VirtualSignExtendWord (.xreg rd)
          (.vreg JoltISA.amoWordSwapOldVReg))).run js =
        .ok RETIRE_SUCCESS js' :=
    JoltISA.virtual_sign_extend_word_run_xreg_vreg
      rd JoltISA.amoWordSwapOldVReg js writebackState hwriteback_current
  refine ⟨js', ?_, ?_⟩
  · exact hwriteback_state
  · intro tail
    rw [JoltISA.execProgram_instr_run_retire _ _ js js' hsext]
theorem amo_word_swap_post64_amoswap_aligned_run
    (rs2 rs1 rd : regidx) (js js_pre : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_mem : AmoMemoryContext amoop.AMOSWAP 4 (amoWordBase addr) addr js.sail)
    (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (3 : BitVec 64) = 0)
    (hpre_sail : js_pre.sail = js.sail)
    (hpre_dword :
      js_pre.vregs JoltISA.amoWordSwapDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr))
    (hpre_shift :
      js_pre.vregs JoltISA.amoWordSwapShiftVReg =
        shift_bits_left addr (3 : BitVec 6))
    (hpre_old :
      js_pre.vregs JoltISA.amoWordSwapOldVReg =
        shift_bits_right
          (loaded_dword_at js.sail (amoWordBase addr))
          (Sail.BitVec.extractLsb
            (shift_bits_left addr (3 : BitVec 6)) 5 0)) :
    ∃ jsf : SailJoltState,
      (JoltISA.execProgram
        (JoltISA.amoPost64ProgramWithScratch rs1 rd (.xreg rs2)
          JoltISA.amoWordSwapDwordVReg JoltISA.amoWordSwapShiftVReg
          JoltISA.amoWordSwapMaskVReg JoltISA.amoWordSwapOldVReg
          JoltISA.amoWordSwapInlineTmpVReg)).run js_pre =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail =
        amoWordFinalSailState rd js.sail addr
          (Sail.BitVec.extractLsb rs2Val 31 0) := by
  let shift64 := shift_bits_left addr (3 : BitVec 6)
  let shift6 := Sail.BitVec.extractLsb shift64 5 0
  let dword := loaded_dword_at js.sail (amoWordBase addr)
  let old := shift_bits_right dword shift6
  let mask32 := (0x00000000FFFFFFFF : BitVec 64)
  let shiftedMask := shift_bits_left mask32 shift6
  let shiftedNew := shift_bits_left rs2Val shift6
  let dwordNew := amoWordSplicedDword js.sail addr rs2Val
  let wordResult : BitVec 32 := Sail.BitVec.extractLsb rs2Val 31 0
  have hsetup := amo_word_store_setup addr h_no_ovf h_align
  obtain ⟨js_mask32, hmask_sail, hmask_mask, hmask_shift, hmask_dword,
      hmask_old, _hmask_new, hmask_tail⟩ :=
    amo_word_swap_mask32_prefix_run js_pre js.sail shift64 dword old
      hpre_sail hpre_shift hpre_dword hpre_old
  obtain ⟨js_shifted_mask, hshift_mask_sail, hshift_mask_mask,
      hshift_mask_shift, hshift_mask_dword, hshift_mask_old,
      _hshift_mask_new, hshift_mask_tail⟩ :=
    amo_word_swap_shift_mask_prefix_run js_mask32 js.sail shift64 dword old
      hmask_sail hmask_mask hmask_shift hmask_dword hmask_old
  obtain ⟨js_shifted_new, hshift_new_sail, hshift_new_shift,
      hshift_new_mask, hshift_new_dword, hshift_new_old,
      hshift_new_tail⟩ :=
    amo_word_swap_shift_new_prefix_run rs2 js_shifted_mask js.sail rs2Val
      shift64 shiftedMask dword old hshift_mask_sail hrs2 hshift_mask_mask
      hshift_mask_shift hshift_mask_dword hshift_mask_old
  obtain ⟨js_splice, hsplice_sail, hsplice_dword, hsplice_old,
      hsplice_tail⟩ :=
    amo_word_swap_splice_block_run js_shifted_new js.sail addr rs2Val old hsetup
      hshift_new_sail hshift_new_dword hshift_new_shift hshift_new_mask
      hshift_new_old
  obtain ⟨js_store_base, hstore_base_sail, hstore_base, hstore_base_dword,
      hstore_base_old, hstore_base_tail⟩ :=
    amo_word_swap_store_base_prefix_run rs1 js_splice js.sail addr dwordNew old
      hsplice_sail hrs1 hsplice_dword hsplice_old
  obtain ⟨js_store, hstore_sail, hstore_old, hstore_tail⟩ :=
    amo_word_swap_sd_spliced_dword_run js_store_base js.sail addr dwordNew old
      hcfg h_mem h_no_ovf hstore_base_sail hstore_base hstore_base_dword
      hstore_base_old
  have hword_store :
      state_after_dword_store js.sail (amoWordBase addr) dwordNew =
        state_after_word_store js.sail addr wordResult :=
    amo_word_spliced_dword_store_eq_word_store
      js.sail addr rs2Val hsetup h_mem.jolt_bytes
  have hstore_sail_word :
      js_store.sail = state_after_word_store js.sail addr wordResult := by
    rw [hstore_sail, hword_store]
  have hold_writeback :
      sign_extend (m := 64)
        ((Sail.BitVec.extractLsb old 31 0) : BitVec 32) =
      sign_extend (m := 64) (loaded_word_at js.sail addr) :=
    amo_word_shifted_old_sign_extend_eq_loaded_word js.sail addr h_align
  obtain ⟨jsf, hwriteback_sail, hwriteback_tail⟩ :=
    amo_word_swap_writeback_old_run rd js_store js.sail addr wordResult old
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
    (h_mem : AmoMemoryContext amoop.AMOSWAP 4
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
    JoltISA.amoPost64ProgramWithScratch rs1 rd (.xreg rs2)
      JoltISA.amoWordSwapDwordVReg JoltISA.amoWordSwapShiftVReg
      JoltISA.amoWordSwapMaskVReg JoltISA.amoWordSwapOldVReg
      JoltISA.amoWordSwapInlineTmpVReg
  obtain ⟨js_pre, hpre_run, hpre_sail, hpre_dword, hpre_shift, hpre_old⟩ :=
    amo_word_swap_pre64_aligned_run post rs1 js hcfg addr hrs1 h_mem
      h_no_ovf h_align
  obtain ⟨jsf, hpost_run, hpost_sail⟩ :=
    amo_word_swap_post64_amoswap_aligned_run rs2 rs1 rd js js_pre hcfg
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
  change sign_extend (m := 32) (trunc (m := 32) rs2Val) =
    (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
  rw [amo_word_sign_extend_4x8_eq_self]
  unfold trunc Sail.BitVec.truncate BitVec.truncate Sail.BitVec.extractLsb BitVec.extractLsb
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi32_bool : (i <b 32) = true := by
    simpa only [Nat.blt_eq, decide_eq_true_eq] using hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', Nat.zero_add,
    hi32_bool, Bool.true_and]

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
    (h_mem : AmoMemoryContext amoop.AMOSWAP 4
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
    (h_mem : AmoMemoryContext amoop.AMOSWAP 4
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
  unfold JoltISA.amoPre64ProgramWithScratch
  exact amo_word_assert_prefix_misaligned_run rs1 _ js addr hrs1 h_align

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

/-- Internal memory-context theorem for `AMOSWAP.W`.

The theorem exposes the same alignment split as the load/store families:
aligned addresses use the full memory context, while misaligned addresses
stop at both interpreters' leading alignment check. -/
theorem amoswapwProgram_eq_sail_of_memory_context
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryContext amoop.AMOSWAP 4
      (amoWordBase addr) addr js.sail) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoswapwProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOSWAP false false rs2 rs1 4 rd).run js.sail := by
  by_cases h_align : addr &&& (3 : BitVec 64) = 0
  · exact amoswapwProgram_eq_sail_aligned
      rs2 rs1 rd js hcfg addr rs2Val hrs1 hrs2 hrd h_mem h_align
  · exact amoswapwProgram_eq_sail_misaligned
      rs2 rs1 rd js hcfg addr rs2Val hrs1 hrs2 h_align

/-- Main public theorem for `AMOSWAP.W`.

The theorem takes one primitive-only atomic bundle. The aligned branch derives
exact memory context from the enclosing dword window; the misaligned branch
stops before memory context is needed. -/
private theorem amoswapwProgram_project_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoWordProgramEqSailAssumptions amoop.AMOSWAP rs2 rs1 rd js) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoswapwProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOSWAP false false rs2 rs1 4 rd).run js.sail := by
  let addr := h.rs1_val
  let rs2Val := h.rs2_val
  by_cases h_align : addr &&& (3 : BitVec 64) = 0
  · have h_mem_base :
        AmoMemoryContext amoop.AMOSWAP 4 (amoWordAssumptionBase addr) addr js.sail := by
      simpa [addr] using h.memoryContext (by simpa [addr] using h_align)
    have h_mem : AmoMemoryContext amoop.AMOSWAP 4 (amoWordBase addr) addr js.sail := by
      simpa [amoWordBase, amoWordAssumptionBase] using h_mem_base
    exact amoswapwProgram_eq_sail_aligned
      rs2 rs1 rd js h.cfg addr rs2Val
      h.rs1_read h.rs2_read h.rd_readable.exists_value
      h_mem h_align
  · exact amoswapwProgram_eq_sail_misaligned
      rs2 rs1 rd js h.cfg addr rs2Val
      h.rs1_read h.rs2_read h_align

/-- Main public theorem for `AMOSWAP.W`. -/
def amoswapwProgramEqSailStatement
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (_h : AmoWordProgramEqSailAssumptions amoop.AMOSWAP rs2 rs1 rd js) : Prop :=
  ProgramMatchesSailWithProtectedFrame js
    ((JoltISA.execProgram (JoltISA.amoswapwProgram rs2 rs1 rd)).run js)
    ((execute_AMO amoop.AMOSWAP false false rs2 rs1 4 rd).run js.sail)

theorem amoswapwProgram_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoWordProgramEqSailAssumptions amoop.AMOSWAP rs2 rs1 rd js) :
    amoswapwProgramEqSailStatement rs2 rs1 rd js h := by
  apply programMatchesSailWithProtectedFrame_of_projectResult_eq
  · exact amoswapwProgram_project_eq_sail rs2 rs1 rd js h
  · simp [JoltISA.amoswapwProgram,
      JoltISA.amoPre64ProgramWithScratch,
      JoltISA.amoPost64ProgramWithScratch,
      JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg,
      JoltISA.DstWritesNoProtectedVReg,
      JoltISA.amoWordSwapMaskVReg, JoltISA.amoWordSwapDwordVReg,
      JoltISA.amoWordSwapShiftVReg, JoltISA.amoWordSwapOldVReg,
      JoltISA.amoWordSwapInlineTmpVReg]

end AtomicFamily

end
