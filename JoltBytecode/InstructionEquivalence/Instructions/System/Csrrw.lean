import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.Instructions.System.Common

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace System

private theorem check_CSR_mtvec_machine_run
    (js : SailJoltState) (access : CSRAccessType) :
    check_CSR JoltISA.SystemCSR.mtvec.address Privilege.Machine access
        (systemProject js) =
      .ok true (systemProject js) := by
  cases access <;>
    unfold check_CSR check_CSR_priv check_CSR_access is_CSR_accessible
      stateen_allows_CSR_access privLevel_to_CSR_privbits csrPriv csrAccess
      JoltISA.SystemCSR.address zopz0zKzJ_u <;>
    simp [bind, EStateM.bind, pure, EStateM.pure]
  · decide
  · decide
  · decide

private theorem write_CSR_mtvec_direct_run
    (js : SailJoltState) (value : BitVec 64)
    (h_direct : MtvecWriteDirectMode value) :
    write_CSR JoltISA.SystemCSR.mtvec.address value (systemProject js) =
      .ok (Ok value)
        { systemProject js with
          regs := (systemProject js).regs.insert Register.mtvec value } := by
  change (EStateM.bind (set_mtvec value) (fun x => pure (Ok x))) (systemProject js) =
    .ok (Ok value)
      { systemProject js with
        regs := (systemProject js).regs.insert Register.mtvec value }
  unfold set_mtvec Sail.readReg PreSail.readReg Sail.writeReg PreSail.writeReg
  simp only [systemProject_mtvec_read js, bind, EStateM.bind, pure,
    EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, modify,
    modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  unfold legalize_tvec Mk_Mtvec
  rw [h_direct.mode_eq]
  unfold trapVectorMode_of_bits
  simp only [pure, EStateM.pure, Std.ExtDHashMap.get?_insert_self]

private theorem csr_id_write_callback_mtvec_run
    (s : SailState) (value : BitVec 64) :
    csr_id_write_callback JoltISA.SystemCSR.mtvec.address value s =
      .ok () s := by
  change (EStateM.bind (pure "mtvec")
      (fun name => pure (csr_full_write_callback name 0x305#12 value))) s =
    .ok () s
  unfold csr_full_write_callback
  simp only [pure, EStateM.pure, EStateM.bind]

theorem csrrwProgram_eq_sail_projected
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rs1 rd : regidx)
    (h_sys : CsrrwSystemAssumptions js csr rs1 rd) :
    systemProjectResult
        ((JoltISA.execProgram (JoltISA.csrrwProgram csr rs1 rd)).run js) =
      (execute_CSRReg (JoltISA.SystemCSR.address csr) rs1 rd csrop.CSRRW).run
        (systemProject js) := by
  cases csr
  · -- `mstatus`
    sorry
  · -- `mtvec`
    -- Re-expressing assumptions
    have hSourceSail : rX_bits rs1 (systemProject js) = .ok h_sys.rs1_val (systemProject js) := by 
      exact systemProject_rX_bits js rs1 h_sys.rs1_val h_sys.source_read
    have hCurPrivProject :
        (systemProject js).regs.get? Register.cur_privilege =
          some (Privilege.Machine : RegisterType Register.cur_privilege) := by 
      exact systemProject_cur_privilege_read js h_sys.cur_privilege_machine.value

    -- THE RHS 
    simp only [EStateM.run, execute_CSRReg, bind, EStateM.bind]
    simp only [hSourceSail]
    simp only [doCSR]
    simp only [bind, EStateM.bind]
    unfold Sail.readReg PreSail.readReg
    simp only [bind, EStateM.bind, pure, get, getThe, MonadStateOf.get, EStateM.get]
    simp only [EStateM.pure, hCurPrivProject]

    -- Intermediate step, TODO: better comments
    have hCheck : check_CSR JoltISA.SystemCSR.mtvec.address Privilege.Machine
            (csr_access_type csrop.CSRRW (rd == zreg) (rs1 == zreg))
            (systemProject js) =
          .ok true (systemProject js) := by
      exact check_CSR_mtvec_machine_run js (csr_access_type csrop.CSRRW (rd == zreg) (rs1 == zreg))
    simp only [hCheck]
    simp only [LeanRV64D.Functions.not]
    simp only [Bool.not_true, Bool.false_eq_true, if_false]
    simp only [EStateM.bind, EStateM.get]
    -- need match (systemProject js).res.get ? Register.cur_privilege = some s as we know it's machine from assumptions
    simp only [hCurPrivProject, EStateM.pure]
    -- We know the else block will be taken 
    -- how do we force it take it
    simp only [ext_check_CSR, Bool.not_true, Bool.false_eq_true, if_false, EStateM.bind]
    cases hRd : rd == zreg
    · simp only [csr_access_type]
      have hReadAccess :
          (CSRAccessType.CSRReadWrite != CSRAccessType.CSRWrite) = true := by decide
      simp only [hReadAccess, if_true]
      -- I should be able to read CSR from assumptions right? So i can cut through this to another if else
      have hReadMtvec :
          read_CSR JoltISA.SystemCSR.mtvec.address (systemProject js) =
            .ok (js.vregs JoltISA.trapHandlerVReg) (systemProject js) := by
        change (get_mtvec ()) (systemProject js) =
          .ok (js.vregs JoltISA.trapHandlerVReg) (systemProject js)
        unfold get_mtvec Sail.readReg PreSail.readReg
        simp only [systemProject_mtvec_read js, bind, EStateM.bind, pure,
          EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get]
      simp only [hReadMtvec]
      have hWriteAccess :
          (CSRAccessType.CSRReadWrite != CSRAccessType.CSRRead) = true := by decide
      simp only [hWriteAccess, if_true, EStateM.bind]
      -- next we need that   match write_CSR JoltISA.SystemCSR.mtvec.address h_sys.rs1_val (systemProject js) is ok
      let sAfterMtvecWrite : SailState := { systemProject js with regs := (systemProject js).regs.insert Register.mtvec h_sys.rs1_val }
      have hWriteMtvec : write_CSR JoltISA.SystemCSR.mtvec.address h_sys.rs1_val (systemProject js) = .ok (Ok h_sys.rs1_val) sAfterMtvecWrite := by
        exact write_CSR_mtvec_direct_run js h_sys.rs1_val (h_sys.mtvec_write_direct rfl)
      simp only [hWriteMtvec, EStateM.bind]
      -- one more write
      have hWriteCallback :
          csr_id_write_callback JoltISA.SystemCSR.mtvec.address h_sys.rs1_val sAfterMtvecWrite =
            .ok () sAfterMtvecWrite := by
        exact csr_id_write_callback_mtvec_run sAfterMtvecWrite h_sys.rs1_val
      simp only [hWriteCallback]
      rw [wX_bits_stateAfterWrite rd (js.vregs JoltISA.trapHandlerVReg) sAfterMtvecWrite]
      simp only [EStateM.pure]
      -- LHS 
      sorry 
    · simp only [csr_access_type]
      have hReadAccess : ¬ ((CSRAccessType.CSRWrite != CSRAccessType.CSRWrite) = true) := by decide
      simp only [hReadAccess, Bool.false_eq_true, if_false, EStateM.pure]
      sorry 
  · -- `mscratch`
    sorry
  · -- `mepc`
    sorry
  · -- `mcause`
    sorry
  · -- `mtval`
    sorry

end System

end
