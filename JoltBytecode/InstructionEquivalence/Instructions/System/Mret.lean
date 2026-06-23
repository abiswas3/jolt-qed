import JoltBytecode.InstructionEquivalence.Instructions.System.Common
import Mathlib.Tactic.IntervalCases

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace System

/-!
# MRET system expansion

Rust's MRET expansion is a single `JALR scratch, mepc, 0`. The link value is
discarded in the instruction-local scratch virtual register, while the return
target comes from the reserved virtual `mepc` register.

The raw Sail `execute_MRET` path performs the full architectural xret CSR
postlude. Jolt's Rust implementation intentionally omits those CSR mutations in
the M-mode-only ZeroOS envelope. The exact assumptions for that postlude should
be discovered by the proof, so this file starts only with the concrete reads
and control-flow facts already visible from the two execution paths.
-/

/-- Concrete Jolt state after Rust's one-row MRET expansion. The scratch write is
not part of `systemProject`, but keeping it in the model matches the emitted
`JALR` row exactly. -/
def mretAfterJalr (js : SailJoltState) (nextPC : BitVec 64) : SailJoltState :=
  joltSetVReg { js with sail := setNextPCState js.sail (mretReturnTarget js) }
    JoltISA.systemScratchVReg nextPC

/-- Sail MRET postlude after restoring `MIE := MPIE`. -/
def mretMstatusAfterMie (mstatus : BitVec 64) : BitVec 64 :=
  Sail.BitVec.updateSubrange mstatus 3 3 (_get_Mstatus_MPIE mstatus)

/-- Sail MRET postlude after setting `MPIE := 1`. -/
def mretMstatusAfterMpie (mstatus : BitVec 64) : BitVec 64 :=
  Sail.BitVec.updateSubrange (mretMstatusAfterMie mstatus) 7 7 1#1

/-- Sail MRET postlude after resetting `MPP` to the configured base privilege. -/
def mretMstatusAfterMpp (mstatus : BitVec 64) (basePriv : Privilege) :
    BitVec 64 :=
  Sail.BitVec.updateSubrange (mretMstatusAfterMpie mstatus) 12 11
    (privLevel_to_bits basePriv)

private theorem updateSubrange_extractLsb_self {w : Nat} (x : BitVec w)
    (hi lo : Nat) (hlo : lo ≤ hi) :
    Sail.BitVec.updateSubrange x hi lo (Sail.BitVec.extractLsb x hi lo) = x := by
  change Sail.BitVec.updateSubrange' x lo (hi - lo + 1)
      (Sail.BitVec.extractLsb x hi lo) = x
  apply BitVec.eq_of_getLsbD_eq
  intro i hiw
  unfold Sail.BitVec.updateSubrange' Sail.BitVec.extractLsb
  rw [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft]
  by_cases hltlo : i < lo
  · simp [hiw, hltlo]
  · by_cases hlehi : i ≤ hi
    · have hsubw : i - lo < w := by omega
      have hsubadd : lo + (i - lo) = i := by omega
      have hsub_len : i - lo < hi - lo + 1 := by omega
      simp [hiw, hltlo, hsubw, hsubadd, hsub_len]
    · have hsub_len : ¬ i - lo < hi - lo + 1 := by omega
      have hnot_span : ¬ i ≤ hi - lo + lo := by omega
      simp [hiw, hltlo, hsub_len, hnot_span]

private theorem clear_low_two_eq_update_zero_of_bit1_zero (x : BitVec 64)
    (hbit1 : x.getLsbD 1 = false) :
    Sail.BitVec.updateSubrange x 1 0 (0#2 : BitVec 2) =
      BitVec.update x 0 0#1 := by
  have hbit1_elem : x[1] = false := by
    simpa [BitVec.getLsbD_eq_getElem] using hbit1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  unfold Sail.BitVec.update Sail.BitVec.updateSubrange Sail.BitVec.updateSubrange'
  rw [BitVec.getLsbD_or, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp [hbit1_elem]

/-- MRET's return target already has bit 0 cleared by the JALR rule. -/
theorem mretReturnTarget_bit0_zero (js : SailJoltState) :
    BitVec.access (mretReturnTarget js) 0 = 0#1 := by
  unfold mretReturnTarget
  unfold Sail.BitVec.access Sail.BitVec.update Sail.BitVec.updateSubrange'
  rw [getElem!_pos (h := by decide)]
  simp

/-- JALR with immediate zero computes the MRET return target. -/
theorem mretJalrTarget_zero_imm (js : SailJoltState) :
    BitVec.update
        (js.vregs JoltISA.mepcVReg + sign_extend (m := 64) (0 : BitVec 12))
        0 0#1 =
      mretReturnTarget js := by
  rw [addi_zero_value]
  rfl

/-- Jumping to MRET's projected return target succeeds and writes `nextPC`. -/
theorem jump_to_mretReturnTarget_run
    (js : SailJoltState) (misa : BitVec 64)
    (hmisa : js.sail.regs.get? Register.misa =
      some (misa : RegisterType Register.misa))
    (hfetch : BitVec.access (mretReturnTarget js) 1 = 0#1) :
    jump_to (mretReturnTarget js) js.sail =
      .ok RETIRE_SUCCESS (setNextPCState js.sail (mretReturnTarget js)) := by
  have hExtC := currentlyEnabled_Ext_C_run js.sail misa hmisa
  have hassert : (0#1 == 0#1) = true := by
    decide
  have hbit1 : bool_bit_backwards 0#1 = false := by
    decide
  unfold jump_to ext_control_check_pc SailME.run PreSail.PreSailME.run
  unfold currentlyEnabled hartSupports
  unfold set_next_pc setNextPCState sail_branch_announce redirect_callback
  unfold Sail.assert PreSail.assert Sail.writeReg PreSail.writeReg
  simp only [hassert, hbit1, hExtC, mretReturnTarget_bit0_zero, hfetch, bit_to_bool,
    if_true, if_false, Bool.false_and, Bool.false_eq_true, bind, EStateM.bind,
    pure, EStateM.pure, EStateM.map, Functor.map, ExceptT.run, ExceptT.mk,
    ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift,
    MonadLift.monadLift, monadLift, liftM, modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet]

/-- Concrete MRET row: `JALR scratch, mepc, 0` writes `nextPC` and jumps to the
cleared virtual `mepc` target. -/
theorem mret_jalr_run
    (js : SailJoltState) (nextPC misa : BitVec 64)
    (hnextPC : js.sail.regs.get? Register.nextPC =
      some (nextPC : RegisterType Register.nextPC))
    (hmisa : js.sail.regs.get? Register.misa =
      some (misa : RegisterType Register.misa))
    (hfetch : BitVec.access (mretReturnTarget js) 1 = 0#1) :
    (JoltISA.execInstr
      (.JALR (.vreg JoltISA.systemScratchVReg)
        (.vreg JoltISA.mepcVReg) (0 : BitVec 12))).run js =
      .ok RETIRE_SUCCESS (mretAfterJalr js nextPC) := by
  have hJump := jump_to_mretReturnTarget_run js misa hmisa hfetch
  rw [RETIRE_SUCCESS] at hJump
  unfold JoltISA.execInstr JoltISA.readSrc JoltISA.writeDst readVReg writeVReg
  unfold liftSail get_next_pc
  unfold Sail.readReg PreSail.readReg
  unfold mretAfterJalr setNextPCState joltSetVReg vregWrite
  unfold RETIRE_SUCCESS
  simp only [hnextPC, hJump, mretJalrTarget_zero_imm, bind, EStateM.bind,
    pure, EStateM.pure, EStateM.run, get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet]
  unfold setNextPCState
  rfl

/-- The full Rust-faithful MRET Jolt program reaches the concrete final Jolt
state described by the row lemma. -/
theorem mretProgram_run
    (js : SailJoltState) (nextPC misa : BitVec 64)
    (hnextPC : js.sail.regs.get? Register.nextPC =
      some (nextPC : RegisterType Register.nextPC))
    (hmisa : js.sail.regs.get? Register.misa =
      some (misa : RegisterType Register.misa))
    (hfetch : BitVec.access (mretReturnTarget js) 1 = 0#1) :
    (JoltISA.execProgram JoltISA.mretProgram).run js =
      .ok RETIRE_SUCCESS (mretAfterJalr js nextPC) := by
  unfold JoltISA.mretProgram
  rw [JoltISA.execProgram_instr_run_retire _ _ js (mretAfterJalr js nextPC)
    (mret_jalr_run js nextPC misa hnextPC hmisa hfetch)]
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure]

/-- The final MRET scratch write is invisible to `systemProject`. -/
theorem systemProject_mretAfterJalr
    (js : SailJoltState) (nextPC : BitVec 64) :
    systemProject (mretAfterJalr js nextPC) =
      systemProject
        { js with sail := setNextPCState js.sail (mretReturnTarget js) } := by
  unfold systemProject mretAfterJalr joltSetVReg vregWrite
  simp only
  repeat first
    | rw [if_neg (by decide)]

/-- If `MIE` already equals `MPIE`, the first MRET mstatus write is
state-neutral. -/
theorem mretMstatus_mie_write_eq_self
    (mstatus : BitVec 64)
    (h_mie_mpie : _get_Mstatus_MIE mstatus = _get_Mstatus_MPIE mstatus) :
    Sail.BitVec.updateSubrange mstatus 3 3 (_get_Mstatus_MPIE mstatus) =
      mstatus := by
  rw [← h_mie_mpie]
  unfold _get_Mstatus_MIE
  exact updateSubrange_extractLsb_self mstatus 3 3 (by omega)

/-- If `MPIE` is already one, the second MRET mstatus write is state-neutral. -/
theorem mretMstatus_mpie_write_eq_self
    (mstatus : BitVec 64)
    (h_mpie_one : _get_Mstatus_MPIE mstatus = 1#1) :
    Sail.BitVec.updateSubrange mstatus 7 7 1#1 = mstatus := by
  rw [← h_mpie_one]
  unfold _get_Mstatus_MPIE
  exact updateSubrange_extractLsb_self mstatus 7 7 (by omega)

/-- If `MPP` is already Machine, resetting it to Machine is state-neutral. -/
theorem mretMstatus_mpp_machine_write_eq_self
    (mstatus : BitVec 64)
    (h_mpp_machine :
      _get_Mstatus_MPP mstatus = privLevel_to_bits Privilege.Machine) :
    Sail.BitVec.updateSubrange mstatus 12 11
        (privLevel_to_bits Privilege.Machine) =
      mstatus := by
  have hPrivBits :
      privLevel_to_bits Privilege.Machine = (0b11 : BitVec 2) := by
    decide
  rw [hPrivBits] at h_mpp_machine ⊢
  rw [← h_mpp_machine]
  unfold _get_Mstatus_MPP
  exact updateSubrange_extractLsb_self mstatus 12 11 (by omega)

/-- Under the machine-only MRET envelope, Sail's architectural `mstatus`
postlude leaves the projected Jolt `mstatus` value unchanged. -/
theorem mretMstatusAfterMpp_machine_eq_self
    (mstatus : BitVec 64)
    (h_mie_mpie : _get_Mstatus_MIE mstatus = _get_Mstatus_MPIE mstatus)
    (h_mpie_one : _get_Mstatus_MPIE mstatus = 1#1)
    (h_mpp_machine :
      _get_Mstatus_MPP mstatus = privLevel_to_bits Privilege.Machine) :
    mretMstatusAfterMpp mstatus Privilege.Machine = mstatus := by
  unfold mretMstatusAfterMpp mretMstatusAfterMpie mretMstatusAfterMie
  rw [mretMstatus_mie_write_eq_self mstatus h_mie_mpie]
  rw [mretMstatus_mpie_write_eq_self mstatus h_mpie_one]
  exact mretMstatus_mpp_machine_write_eq_self mstatus h_mpp_machine

/-- The MRET `MIE`/`MPIE` updates do not change the `MPP` field used to select
the return privilege. -/
theorem mretMstatusAfterMpie_mpp_machine
    (mstatus : BitVec 64)
    (h_mpp_machine :
      _get_Mstatus_MPP mstatus = privLevel_to_bits Privilege.Machine) :
    _get_Mstatus_MPP (mretMstatusAfterMpie mstatus) =
      privLevel_to_bits Privilege.Machine := by
  have hPrivBits :
      privLevel_to_bits Privilege.Machine = (0b11 : BitVec 2) := by
    decide
  rw [hPrivBits] at h_mpp_machine ⊢
  unfold _get_Mstatus_MPP at h_mpp_machine
  have h11 : mstatus[11] = true := by
    have h := congrArg (fun z : BitVec 2 => z.getLsbD 0) h_mpp_machine
    simpa [Sail.BitVec.extractLsb, BitVec.getLsbD_eq_getElem] using h
  have h12 : mstatus[12] = true := by
    have h := congrArg (fun z : BitVec 2 => z.getLsbD 1) h_mpp_machine
    simpa [Sail.BitVec.extractLsb, BitVec.getLsbD_eq_getElem] using h
  unfold mretMstatusAfterMpie mretMstatusAfterMie
  unfold _get_Mstatus_MPP _get_Mstatus_MPIE
  unfold Sail.BitVec.updateSubrange Sail.BitVec.updateSubrange'
  unfold Sail.BitVec.extractLsb at h_mpp_machine ⊢
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp at h_mpp_machine ⊢
  · exact h11
  · exact h12

/-- The return privilege selected by the projected MRET `mstatus` is Machine. -/
theorem privLevel_of_mretMstatusAfterMpie_machine_run
    (s : SailState) (mstatus : BitVec 64)
    (h_mpp_machine :
      _get_Mstatus_MPP mstatus = privLevel_to_bits Privilege.Machine) :
    (privLevel_bits_forwards
        (_get_Mstatus_MPP (mretMstatusAfterMpie mstatus), 0#1)) s =
      .ok Privilege.Machine s := by
  have hBits := mretMstatusAfterMpie_mpp_machine mstatus h_mpp_machine
  have hPrivBits :
      privLevel_to_bits Privilege.Machine = (0b11 : BitVec 2) := by
    decide
  rw [hPrivBits] at hBits
  unfold privLevel_bits_forwards
  simp only [hBits]
  rfl

/-- The projected `mstatus.MPP = Machine` field decodes to Machine privilege. -/
theorem privLevel_bits_forwards_mstatus_machine_run
    (s : SailState) (mstatus : BitVec 64)
    (h_mpp_machine :
      _get_Mstatus_MPP mstatus = privLevel_to_bits Privilege.Machine) :
    (privLevel_bits_forwards (_get_Mstatus_MPP mstatus, 0#1)) s =
      .ok Privilege.Machine s := by
  have hPrivBits :
      privLevel_to_bits Privilege.Machine = (0b11 : BitVec 2) := by
    decide
  rw [hPrivBits] at h_mpp_machine
  unfold privLevel_bits_forwards
  simp only [h_mpp_machine]
  rfl

/-- With `misa.U = 0`, generated Sail reports user mode disabled. -/
theorem currentlyEnabled_Ext_U_disabled_run
    (s : SailState) (misa : BitVec 64)
    (hmisa : s.regs.get? Register.misa =
      some (misa : RegisterType Register.misa))
    (hmisa_u : _get_Misa_U misa = 0#1) :
    currentlyEnabled extension.Ext_U s = .ok false s := by
  have hZicsr := currentlyEnabled_Ext_Zicsr_run s
  have hHartU : hartSupports extension.Ext_U = true := by
    rw [hartSupports]
  have hUDisabled : (0#1 == (1#1 : BitVec 1)) = false := by
    decide
  unfold currentlyEnabled Sail.readReg PreSail.readReg
  simp only [hmisa, hZicsr, hmisa_u, hHartU, hUDisabled, Bool.false_and,
    Bool.and_false, bind, EStateM.bind, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get]

/-- Clearing raw `mepc`'s low two bits agrees with MRET's JALR target when the
JALR target is fetch aligned. -/
theorem mretMepc_clear_low_two_eq_returnTarget
    (js : SailJoltState)
    (hfetch : BitVec.access (mretReturnTarget js) 1 = 0#1) :
    Sail.BitVec.updateSubrange (js.vregs JoltISA.mepcVReg) 1 0
        (zeros (n := (1 -i (0 -i 1)))) =
      mretReturnTarget js := by
  unfold mretReturnTarget at hfetch ⊢
  change Sail.BitVec.updateSubrange (js.vregs JoltISA.mepcVReg) 1 0
      (0#2 : BitVec 2) =
    BitVec.update (js.vregs JoltISA.mepcVReg) 0 0#1
  unfold Sail.BitVec.access at hfetch
  unfold Sail.BitVec.update Sail.BitVec.updateSubrange' at hfetch
  rw [getElem!_pos (h := by decide)] at hfetch
  have hbit1 : (js.vregs JoltISA.mepcVReg).getLsbD 1 = false := by
    cases hx : (js.vregs JoltISA.mepcVReg)[1] <;>
      simp [hx, BitVec.getLsbD_eq_getElem] at hfetch ⊢
  exact clear_low_two_eq_update_zero_of_bit1_zero
    (js.vregs JoltISA.mepcVReg) hbit1

/-- Sail `align_pc` returns the same target as the MRET `JALR` row. -/
theorem align_pc_mretReturnTarget_run
    (js : SailJoltState) (misa : BitVec 64)
    (hmisa : js.sail.regs.get? Register.misa =
      some (misa : RegisterType Register.misa))
    (hfetch : BitVec.access (mretReturnTarget js) 1 = 0#1) :
    (align_pc (js.vregs JoltISA.mepcVReg)).run (systemProject js) =
      .ok (mretReturnTarget js) (systemProject js) := by
  have hMisa := systemProject_misa_read js misa hmisa
  have hExtC := currentlyEnabled_Ext_C_run (systemProject js) misa hMisa
  have hClearLow := mretMepc_clear_low_two_eq_returnTarget js hfetch
  have hHartC : hartSupports extension.Ext_C = true := by
    repeat rw [hartSupports]
    decide
  have hHartZca : hartSupports extension.Ext_Zca = true := by
    rw [hartSupports]
  unfold align_pc currentlyEnabled
  simp only [hExtC, hHartC, hHartZca, Bool.true_and, Bool.not_true,
    Bool.or_false, LeanRV64D.Functions.not, bind, EStateM.bind, EStateM.run,
    pure, EStateM.pure]
  by_cases hCompressed : (_get_Misa_C misa == 1#1) = true
  · rw [if_pos hCompressed]
    rfl
  · rw [if_neg hCompressed]
    rw [hClearLow]
    rfl

/-- Sail's MRET xret-target helper reads projected `mepc` and aligns it to the
same target as Jolt's `JALR`. -/
theorem prepare_xret_target_machine_mret_run
    (js : SailJoltState) (misa : BitVec 64)
    (hmisa : js.sail.regs.get? Register.misa =
      some (misa : RegisterType Register.misa))
    (hfetch : BitVec.access (mretReturnTarget js) 1 = 0#1) :
    prepare_xret_target Privilege.Machine (systemProject js) =
      .ok (mretReturnTarget js) (systemProject js) := by
  have hMepc := systemProject_mepc_read js
  have hAlign := align_pc_mretReturnTarget_run js misa hmisa hfetch
  unfold prepare_xret_target get_xepc Sail.readReg PreSail.readReg
  simp only [hMepc, bind, EStateM.bind, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get]
  exact hAlign

/-- `systemProject` preserves the `mseccfg` read used by Zicfilp MRET
bookkeeping. -/
theorem systemProject_mseccfg_read
    (js : SailJoltState) (mseccfg : BitVec 64)
    (hmseccfg : js.sail.regs.get? Register.mseccfg =
      some (mseccfg : RegisterType Register.mseccfg)) :
    (systemProject js).regs.get? Register.mseccfg =
      some (mseccfg : RegisterType Register.mseccfg) := by
  rw [systemProject_get_unmodified]
  exact hmseccfg
  all_goals decide

/-- If projected `mstatus.MPELP` is already zero, Zicfilp's MRET restore write
to that field is state-neutral. -/
theorem mretMstatus_mpelp_write_eq_self
    (mstatus : BitVec 64)
    (h_mpelp_zero : _get_Mstatus_MPELP mstatus = 0#1) :
    Sail.BitVec.updateSubrange mstatus 41 41
        (landing_pad_bits_backwards landing_pad_expectation.NO_LP_EXPECTED) =
      mstatus := by
  unfold landing_pad_bits_backwards
  rw [← h_mpelp_zero]
  unfold _get_Mstatus_MPELP
  exact updateSubrange_extractLsb_self mstatus 41 41 (by omega)

/-- For the MRET envelope, Sail's Zicfilp xret hook is state-neutral:
`mstatus.MPELP` and `elp` are already zero. -/
theorem zicfilp_restore_elp_mret_machine_run
    (js : SailJoltState) (mseccfg : BitVec 64)
    (hmseccfg : js.sail.regs.get? Register.mseccfg =
      some (mseccfg : RegisterType Register.mseccfg))
    (help : js.sail.regs.get? Register.elp =
      some (0#1 : RegisterType Register.elp))
    (h_mpelp_zero :
      _get_Mstatus_MPELP (js.vregs JoltISA.mstatusVReg) = 0#1) :
    zicfilp_restore_elp_on_xret xRET_type.mRET Privilege.Machine
        (systemProject js) =
      .ok () (systemProject js) := by
  have hMstatusRead := systemProject_mstatus_read js
  have hMseccfgRead := systemProject_mseccfg_read js mseccfg hmseccfg
  have hElpRead := systemProject_elp_read js help
  have hMpelpWrite := mretMstatus_mpelp_write_eq_self
    (js.vregs JoltISA.mstatusVReg) h_mpelp_zero
  have hMpelpWriteZero : Sail.BitVec.updateSubrange
      (js.vregs JoltISA.mstatusVReg) 41 41 0#1 =
        js.vregs JoltISA.mstatusVReg := by
    simpa [landing_pad_bits_backwards] using hMpelpWrite
  have hMstatusInsert : (systemProject js).regs.insert Register.mstatus
      (js.vregs JoltISA.mstatusVReg) = (systemProject js).regs := by
    exact extDHashMap_insert_eq_self_of_get? (systemProject js).regs
      Register.mstatus (js.vregs JoltISA.mstatusVReg) hMstatusRead
  have hElpInsert : (systemProject js).regs.insert Register.elp
      (0#1 : RegisterType Register.elp) = (systemProject js).regs := by
    exact extDHashMap_insert_eq_self_of_get? (systemProject js).regs
      Register.elp (0#1) hElpRead
  unfold zicfilp_restore_elp_on_xret get_xLPE
  unfold Sail.readReg PreSail.readReg Sail.writeReg PreSail.writeReg
  simp only [hMstatusRead, hMpelpWriteZero, hMstatusInsert, hMseccfgRead,
    h_mpelp_zero, landing_pad_bits_backwards,
    bind, EStateM.bind, pure, EStateM.pure, get, getThe, MonadStateOf.get,
    EStateM.get, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  by_cases hLpe : bool_bit_backwards (_get_Seccfg_MLPE mseccfg) = true
  · rw [if_pos hLpe]
    simp only [EStateM.pure]
    rw [hElpInsert]
  · rw [if_neg hLpe]
    simp only [EStateM.pure]
    rw [hElpInsert]

/-- Sail's machine-mode MRET exception handler is state-neutral except for
returning the aligned projected `mepc` target. -/
theorem exception_handler_machine_mret_run
    (js : SailJoltState) (pc misa mseccfg : BitVec 64)
    (hmisa : js.sail.regs.get? Register.misa =
      some (misa : RegisterType Register.misa))
    (hmisa_u : _get_Misa_U misa = 0#1)
    (hmseccfg : js.sail.regs.get? Register.mseccfg =
      some (mseccfg : RegisterType Register.mseccfg))
    (help : js.sail.regs.get? Register.elp =
      some (0#1 : RegisterType Register.elp))
    (hpriv : js.sail.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (h_mie_mpie :
      _get_Mstatus_MIE (js.vregs JoltISA.mstatusVReg) =
        _get_Mstatus_MPIE (js.vregs JoltISA.mstatusVReg))
    (h_mpie_one :
      _get_Mstatus_MPIE (js.vregs JoltISA.mstatusVReg) = 1#1)
    (h_mpp_machine :
      _get_Mstatus_MPP (js.vregs JoltISA.mstatusVReg) =
        privLevel_to_bits Privilege.Machine)
    (h_mpelp_zero :
      _get_Mstatus_MPELP (js.vregs JoltISA.mstatusVReg) = 0#1)
    (hfetch : BitVec.access (mretReturnTarget js) 1 = 0#1) :
    exception_handler Privilege.Machine (ctl_result.CTL_MRET ()) pc
        (systemProject js) =
      .ok (mretReturnTarget js) (systemProject js) := by
  have hCurPriv := systemProject_cur_privilege_read js hpriv
  have hMstatusRead := systemProject_mstatus_read js
  have hMisa := systemProject_misa_read js misa hmisa
  have hMieWrite := mretMstatus_mie_write_eq_self
    (js.vregs JoltISA.mstatusVReg) h_mie_mpie
  have hMpieWrite := mretMstatus_mpie_write_eq_self
    (js.vregs JoltISA.mstatusVReg) h_mpie_one
  have hMppWrite := mretMstatus_mpp_machine_write_eq_self
    (js.vregs JoltISA.mstatusVReg) h_mpp_machine
  have hMstatusInsert : (systemProject js).regs.insert Register.mstatus
      (js.vregs JoltISA.mstatusVReg) = (systemProject js).regs := by
    exact extDHashMap_insert_eq_self_of_get? (systemProject js).regs
      Register.mstatus (js.vregs JoltISA.mstatusVReg) hMstatusRead
  have hCurPrivInsert : (systemProject js).regs.insert Register.cur_privilege
      (Privilege.Machine : RegisterType Register.cur_privilege) =
        (systemProject js).regs := by
    exact extDHashMap_insert_eq_self_of_get? (systemProject js).regs
      Register.cur_privilege Privilege.Machine hCurPriv
  have hReturnPriv := privLevel_bits_forwards_mstatus_machine_run
    (systemProject js) (js.vregs JoltISA.mstatusVReg) h_mpp_machine
  have hExtU := currentlyEnabled_Ext_U_disabled_run
    (systemProject js) misa hMisa hmisa_u
  have hBneMachine : bne Privilege.Machine Privilege.Machine = false := by
    rfl
  have hHartZicfilp : hartSupports extension.Ext_Zicfilp = true := by
    rw [hartSupports]
  have hZicfilp := zicfilp_restore_elp_mret_machine_run
    js mseccfg hmseccfg help h_mpelp_zero
  have hLongCsr := long_csr_write_callback_mstatus_run
    (systemProject js) (js.vregs JoltISA.mstatusVReg)
  have hPrintException : get_config_print_exception () = false := rfl
  have hPrepare := prepare_xret_target_machine_mret_run js misa hmisa hfetch
  unfold exception_handler
  unfold Sail.readReg PreSail.readReg Sail.writeReg PreSail.writeReg
  simp only [hCurPriv, hMstatusRead, hMieWrite, hMstatusInsert,
    hMpieWrite, hReturnPriv, hCurPrivInsert, hExtU, hMppWrite,
    hBneMachine, hHartZicfilp, if_true, if_false, hZicfilp, hLongCsr,
    hPrintException, hPrepare, bind, EStateM.bind, pure, EStateM.pure,
    Bool.false_eq_true, get, getThe, MonadStateOf.get, EStateM.get, modify,
    modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- Raw Sail `execute_MRET` reaches the same projected control-flow state as
Rust/Jolt MRET under the machine-only MRET envelope. -/
theorem execute_MRET_machine_run
    (js : SailJoltState) (pc misa mseccfg : BitVec 64)
    (hpc : js.sail.regs.get? Register.PC =
      some (pc : RegisterType Register.PC))
    (hmisa : js.sail.regs.get? Register.misa =
      some (misa : RegisterType Register.misa))
    (hmisa_u : _get_Misa_U misa = 0#1)
    (hmseccfg : js.sail.regs.get? Register.mseccfg =
      some (mseccfg : RegisterType Register.mseccfg))
    (help : js.sail.regs.get? Register.elp =
      some (0#1 : RegisterType Register.elp))
    (hpriv : js.sail.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (h_mie_mpie :
      _get_Mstatus_MIE (js.vregs JoltISA.mstatusVReg) =
        _get_Mstatus_MPIE (js.vregs JoltISA.mstatusVReg))
    (h_mpie_one :
      _get_Mstatus_MPIE (js.vregs JoltISA.mstatusVReg) = 1#1)
    (h_mpp_machine :
      _get_Mstatus_MPP (js.vregs JoltISA.mstatusVReg) =
        privLevel_to_bits Privilege.Machine)
    (h_mpelp_zero :
      _get_Mstatus_MPELP (js.vregs JoltISA.mstatusVReg) = 0#1)
    (hfetch : BitVec.access (mretReturnTarget js) 1 = 0#1) :
    (execute_MRET ()).run (systemProject js) =
      .ok RETIRE_SUCCESS
        (systemProject
          { js with sail := setNextPCState js.sail (mretReturnTarget js) }) := by
  have hPc := systemProject_pc_read js pc hpc
  have hCurPriv := systemProject_cur_privilege_read js hpriv
  have hException := exception_handler_machine_mret_run
    js pc misa mseccfg hmisa hmisa_u hmseccfg help hpriv h_mie_mpie
      h_mpie_one h_mpp_machine h_mpelp_zero hfetch
  have hSetNext := set_next_pc_systemProject_run js (mretReturnTarget js)
  change (set_next_pc (mretReturnTarget js)) (systemProject js) =
    .ok ()
      (systemProject
        { js with sail := setNextPCState js.sail (mretReturnTarget js) }) at hSetNext
  have hBneMachine : bne Privilege.Machine Privilege.Machine = false := by
    rfl
  have hXretPriv : LeanRV64D.Functions.not
      (ext_check_xret_priv Privilege.Machine) = false := by
    unfold LeanRV64D.Functions.not ext_check_xret_priv
    rfl
  unfold execute_MRET Sail.readReg PreSail.readReg
  simp only [hCurPriv, hPc, hBneMachine, hXretPriv, if_false, hException,
    hSetNext, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    Bool.false_eq_true, get, getThe, MonadStateOf.get, EStateM.get]

end System

end
