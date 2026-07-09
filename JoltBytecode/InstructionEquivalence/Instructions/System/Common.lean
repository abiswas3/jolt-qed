import JoltBytecode.Assumptions
import JoltBytecode.JoltISA.Expansions.System
import JoltBytecode.InstructionEquivalence.ProofSupport.BundleLemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.ADDI
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.VirtualMULI

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Shared system-instruction proof surface

System instructions are the first place where the Rust Jolt expansion keeps
architectural machine CSR state in persistent virtual registers.  The plain
`projectResult` used by ordinary ALU and memory proofs drops those virtual
registers, so it is the wrong projection for ECALL/MRET/CSR proofs.

The definitions here make that bridge explicit: `systemProject` overlays the
Jolt virtual CSR registers onto the corresponding generated Sail CSR registers.
The Sail side is still computed by Sail helpers such as `exception_handler`,
`set_next_pc`, `tvec_addr`, `_get_Mstatus_*`, and `_update_Mstatus_*`.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace System

/-- Jolt's ZeroOS machine-mode trap-entry value for `mstatus`.

Rust ECALL writes this as `3 << 11`, i.e. `MPP = Machine`, with `MIE = 0` and
`MPIE = 0` in the M-mode-only model. -/
def zeroOSMstatus : BitVec 64 :=
  BitVec.ofNat 64 0x1800

/-- Machine-mode ECALL cause, expressed through the Sail exception encoder. -/
def ecallMachineCause : BitVec 64 :=
  zero_extend (m := 64) (exceptionType_bits_forwards (ExceptionType.E_M_EnvCall ()))

/-- Sail's machine-trap update to `mstatus`, specialized to machine-mode ECALL.

This mirrors the generated Sail `trap_handler` machine branch:
save `MIE` into `MPIE`, clear `MIE`, and write `MPP = Machine`. -/
def sailMachineTrapMstatus (mstatus : BitVec 64) : BitVec 64 :=
  Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange
      (Sail.BitVec.updateSubrange mstatus 7 7 (_get_Mstatus_MIE mstatus))
      3 3 0#1)
    12 11 (privLevel_to_bits Privilege.Machine)

/-- Jolt's `JALR` trap target: read the trap-handler virtual register and clear
bit 0, exactly as Sail/Jolt `JALR` does. -/
def ecallTrapTarget (js : SailJoltState) : BitVec 64 :=
  BitVec.update (js.vregs JoltISA.trapHandlerVReg) 0 0#1

/-- Jolt's concrete MRET return target: `JALR` reads virtual `mepc` and clears
bit 0. -/
def mretReturnTarget (js : SailJoltState) : BitVec 64 :=
  BitVec.update (js.vregs JoltISA.mepcVReg) 0 0#1

/-- Overlay Jolt's persistent virtual CSR registers onto the generated Sail CSR
register keys.

This is only a proof projection: the Rust-faithful Jolt programs still write
Jolt virtual registers, and the Sail specification still reads/writes generated
Sail registers. -/
def systemProject (js : SailJoltState) : SailState :=
  { js.sail with
    regs :=
      ((((((js.sail.regs
        |>.insert Register.mtvec (js.vregs JoltISA.trapHandlerVReg))
        |>.insert Register.mscratch (js.vregs JoltISA.mscratchVReg))
        |>.insert Register.mepc (js.vregs JoltISA.mepcVReg))
        |>.insert Register.mcause (js.vregs JoltISA.mcauseVReg))
        |>.insert Register.mtval (js.vregs JoltISA.mtvalVReg))
        |>.insert Register.mstatus (js.vregs JoltISA.mstatusVReg)) }

/-- Project a Jolt run result through `systemProject`, preserving the result
value and error shape while materializing virtual CSRs in the Sail state. -/
def systemProjectResult
    (r : EStateM.Result (Error exception) SailJoltState α) :
    EStateM.Result (Error exception) SailState α :=
  match r with
  | .ok a js' => .ok a (systemProject js')
  | .error e js' => .error e (systemProject js')

/-- Re-inserting a dependent-map value that is already present leaves the map
unchanged. -/
theorem extDHashMap_insert_eq_self_of_get? {α : Type} [BEq α] [Hashable α]
    [LawfulBEq α] {β : α → Type} (m : Std.ExtDHashMap α β) (k : α)
    (v : β k) (h : m.get? k = some v) :
    m.insert k v = m := by
  apply Std.ExtDHashMap.ext_get?
  intro a
  rw [Std.ExtDHashMap.get?_insert]
  split
  · rename_i hbeq
    have heq : k = a := LawfulBEq.eq_of_beq hbeq
    cases heq
    rw [h]
    rw [cast_eq]
  · rfl

/-- If the linked CSR virtual registers agree with the generated Sail CSR
registers, materializing those virtual registers is the same state as the plain
projection. This is the global linked-register invariant made explicit. -/
theorem systemProject_eq_project_of_compatible
    (js : SailJoltState)
    (h : LinkedCSRs js) :
    systemProject js = project js := by
  have hMstatus := h.1
  have hMtvec := h.2.1
  have hMscratch := h.2.2.1
  have hMepc := h.2.2.2.1
  have hMcause := h.2.2.2.2.1
  have hMtval := h.2.2.2.2.2
  unfold systemProject project
  simp only
  congr
  rw [extDHashMap_insert_eq_self_of_get? js.sail.regs Register.mtvec
    (js.vregs JoltISA.trapHandlerVReg) hMtvec.value_eq]
  rw [extDHashMap_insert_eq_self_of_get? js.sail.regs Register.mscratch
    (js.vregs JoltISA.mscratchVReg) hMscratch.value_eq]
  rw [extDHashMap_insert_eq_self_of_get? js.sail.regs Register.mepc
    (js.vregs JoltISA.mepcVReg) hMepc.value_eq]
  rw [extDHashMap_insert_eq_self_of_get? js.sail.regs Register.mcause
    (js.vregs JoltISA.mcauseVReg) hMcause.value_eq]
  rw [extDHashMap_insert_eq_self_of_get? js.sail.regs Register.mtval
    (js.vregs JoltISA.mtvalVReg) hMtval.value_eq]
  rw [extDHashMap_insert_eq_self_of_get? js.sail.regs Register.mstatus
    (js.vregs JoltISA.mstatusVReg) hMstatus.value_eq]

/-- Reading after inserting a different key returns the old read. -/
theorem extDHashMap_get?_insert_of_ne {α : Type} [BEq α] [Hashable α]
    [LawfulBEq α] {β : α → Type} (m : Std.ExtDHashMap α β)
    {written read : α} (v : β written) (h : written ≠ read) :
    (m.insert written v).get? read = m.get? read := by
  rw [Std.ExtDHashMap.get?_insert]
  have hfalse : (written == read) = false := beq_false_of_ne h
  simp only [hfalse, Bool.false_eq_true]
  rw [dif_neg (by intro hf; cases hf)]

/-- Two writes to one dependent-map key do not affect reads from a different
key. -/
theorem extDHashMap_get?_insert_twice_of_ne {α : Type} [BEq α] [Hashable α]
    [LawfulBEq α] {β : α → Type} (m : Std.ExtDHashMap α β)
    {written read : α} (v1 v2 : β written) (h : written ≠ read) :
    ((m.insert written v1).insert written v2).get? read = m.get? read := by
  rw [extDHashMap_get?_insert_of_ne (h := h)]
  rw [extDHashMap_get?_insert_of_ne (h := h)]

/-- A later write to the same dependent-map key overwrites the earlier write. -/
theorem extDHashMap_insert_insert_same {α : Type} [BEq α] [Hashable α]
    [LawfulBEq α] {β : α → Type} (m : Std.ExtDHashMap α β)
    (k : α) (v1 v2 : β k) :
    (m.insert k v1).insert k v2 = m.insert k v2 := by
  apply Std.ExtDHashMap.ext_get?
  intro a
  by_cases ha : a = k
  · subst a
    rw [Std.ExtDHashMap.get?_insert_self]
    rw [Std.ExtDHashMap.get?_insert_self]
  · rw [extDHashMap_get?_insert_of_ne (h := by intro hk; exact ha hk.symm)]
    rw [extDHashMap_get?_insert_of_ne (h := by intro hk; exact ha hk.symm)]
    rw [extDHashMap_get?_insert_of_ne (h := by intro hk; exact ha hk.symm)]

/-- Inserts at distinct dependent-map keys commute. -/
theorem extDHashMap_insert_comm_of_ne {α : Type} [BEq α] [Hashable α]
    [LawfulBEq α] {β : α → Type} (m : Std.ExtDHashMap α β)
    {k1 k2 : α} (v1 : β k1) (v2 : β k2) (h : k1 ≠ k2) :
    (m.insert k1 v1).insert k2 v2 =
      (m.insert k2 v2).insert k1 v1 := by
  apply Std.ExtDHashMap.ext_get?
  intro a
  by_cases ha1 : a = k1
  · subst a
    rw [extDHashMap_get?_insert_of_ne (h := h.symm)]
    rw [Std.ExtDHashMap.get?_insert_self]
    rw [Std.ExtDHashMap.get?_insert_self]
  · by_cases ha2 : a = k2
    · subst a
      rw [Std.ExtDHashMap.get?_insert_self]
      rw [extDHashMap_get?_insert_of_ne (h := h)]
      rw [Std.ExtDHashMap.get?_insert_self]
    · rw [extDHashMap_get?_insert_of_ne (h := by intro hk; exact ha2 hk.symm)]
      rw [extDHashMap_get?_insert_of_ne (h := by intro hk; exact ha1 hk.symm)]
      rw [extDHashMap_get?_insert_of_ne (h := by intro hk; exact ha1 hk.symm)]
      rw [extDHashMap_get?_insert_of_ne (h := by intro hk; exact ha2 hk.symm)]

/-- A successful generated Sail register read from a populated key is a pure
read of the current state. -/
theorem sail_readReg_run
    (s : SailState) (reg : Register) (value : RegisterType reg)
    (h : s.regs.get? reg = some value) :
    (Sail.readReg reg : SailM (RegisterType reg)) s = .ok value s := by
  unfold Sail.readReg PreSail.readReg
  simp only [h, bind, EStateM.bind, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get]

/-- A generated Sail register write only inserts the new register value. -/
theorem sail_writeReg_run
    (s : SailState) (reg : Register) (value : RegisterType reg) :
    (Sail.writeReg reg value : SailM Unit) s =
      .ok () { s with regs := s.regs.insert reg value } := by
  unfold Sail.writeReg PreSail.writeReg
  simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- Reading a non-overlaid register through `systemProject` reads the original
Sail register map. -/
theorem systemProject_get_unmodified
    (js : SailJoltState) (reg : Register)
    (hmstatus : (Register.mstatus == reg) = false)
    (hmtval : (Register.mtval == reg) = false)
    (hmcause : (Register.mcause == reg) = false)
    (hmepc : (Register.mepc == reg) = false)
    (hmscratch : (Register.mscratch == reg) = false)
    (hmtvec : (Register.mtvec == reg) = false) :
    (systemProject js).regs.get? reg = js.sail.regs.get? reg := by
  unfold systemProject
  simp only [Std.ExtDHashMap.get?_insert, hmstatus, hmtval, hmcause, hmepc,
    hmscratch, hmtvec, Bool.false_eq_true]
  repeat rw [dif_neg (by intro h; cases h)]

/-- `systemProject` preserves architectural integer-register reads: it overlays
only machine CSR registers, never `x0`-`x31`. -/
theorem systemProject_rX_bits
    (js : SailJoltState) (rs : regidx) (value : BitVec 64)
    (h_read : rX_bits rs js.sail = .ok value js.sail) :
    rX_bits rs (systemProject js) = .ok value (systemProject js) := by
  unfold rX_bits rX regval_from_reg at h_read ⊢
  simp only [Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, Int.toNat_natCast,
    bind, EStateM.bind, pure, EStateM.pure] at h_read ⊢
  obtain ⟨i⟩ := rs
  have hi : i.toNat < 32 := i.isLt
  have hcases : i.toNat = 0 ∨ i.toNat = 1 ∨ i.toNat = 2 ∨ i.toNat = 3 ∨
      i.toNat = 4 ∨ i.toNat = 5 ∨ i.toNat = 6 ∨ i.toNat = 7 ∨
      i.toNat = 8 ∨ i.toNat = 9 ∨ i.toNat = 10 ∨ i.toNat = 11 ∨
      i.toNat = 12 ∨ i.toNat = 13 ∨ i.toNat = 14 ∨ i.toNat = 15 ∨
      i.toNat = 16 ∨ i.toNat = 17 ∨ i.toNat = 18 ∨ i.toNat = 19 ∨
      i.toNat = 20 ∨ i.toNat = 21 ∨ i.toNat = 22 ∨ i.toNat = 23 ∨
      i.toNat = 24 ∨ i.toNat = 25 ∨ i.toNat = 26 ∨ i.toNat = 27 ∨
      i.toNat = 28 ∨ i.toNat = 29 ∨ i.toNat = 30 ∨ i.toNat = 31 := by
    omega
  rcases hcases with hidx | hidx | hidx | hidx | hidx | hidx | hidx | hidx |
      hidx | hidx | hidx | hidx | hidx | hidx | hidx | hidx |
      hidx | hidx | hidx | hidx | hidx | hidx | hidx | hidx |
      hidx | hidx | hidx | hidx | hidx | hidx | hidx | hidx
  · simp only [hidx] at h_read ⊢
    cases h_read
    rfl
  all_goals
    simp only [hidx] at h_read ⊢
    unfold Sail.readReg PreSail.readReg at h_read ⊢
    simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get,
      EStateM.get, pure] at h_read ⊢
    rw [systemProject_get_unmodified]
    · generalize hget : js.sail.regs.get? _ = lookup at h_read ⊢
      cases lookup with
      | none =>
          simp only [throw, throwThe, MonadExceptOf.throw,
            EStateM.throw] at h_read
          cases h_read
      | some regVal =>
          simp only at h_read ⊢
          cases h_read
          rfl
    all_goals decide

/-- `systemProject` preserves the architectural `PC` read. -/
theorem systemProject_pc_read
    (js : SailJoltState) (pc : BitVec 64)
    (hpc : js.sail.regs.get? Register.PC =
      some (pc : RegisterType Register.PC)) :
    (systemProject js).regs.get? Register.PC =
      some (pc : RegisterType Register.PC) := by
  rw [systemProject_get_unmodified]
  exact hpc
  all_goals decide

/-- `systemProject` preserves the architectural `nextPC` read. -/
theorem systemProject_nextPC_read
    (js : SailJoltState) (nextPC : BitVec 64)
    (hnextPC : js.sail.regs.get? Register.nextPC =
      some (nextPC : RegisterType Register.nextPC)) :
    (systemProject js).regs.get? Register.nextPC =
      some (nextPC : RegisterType Register.nextPC) := by
  rw [systemProject_get_unmodified]
  exact hnextPC
  all_goals decide

/-- `systemProject` preserves the machine-mode privilege read. -/
theorem systemProject_cur_privilege_read
    (js : SailJoltState)
    (hpriv : js.sail.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege)) :
    (systemProject js).regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege) := by
  rw [systemProject_get_unmodified]
  exact hpriv
  all_goals decide

/-- `systemProject` preserves the `medeleg` read used by Sail delegation. -/
theorem systemProject_medeleg_read
    (js : SailJoltState) (medeleg : BitVec 64)
    (hmedeleg : js.sail.regs.get? Register.medeleg =
      some (medeleg : RegisterType Register.medeleg)) :
    (systemProject js).regs.get? Register.medeleg =
      some (medeleg : RegisterType Register.medeleg) := by
  rw [systemProject_get_unmodified]
  exact hmedeleg
  all_goals decide

/-- `systemProject` preserves the `misa` read used by Sail extension checks. -/
theorem systemProject_misa_read
    (js : SailJoltState) (misa : BitVec 64)
    (hmisa : js.sail.regs.get? Register.misa =
      some (misa : RegisterType Register.misa)) :
    (systemProject js).regs.get? Register.misa =
      some (misa : RegisterType Register.misa) := by
  rw [systemProject_get_unmodified]
  exact hmisa
  all_goals decide

/-- `systemProject` preserves the `elp = 0` read used by Zicfilp trap
bookkeeping. -/
theorem systemProject_elp_read
    (js : SailJoltState)
    (help : js.sail.regs.get? Register.elp =
      some (0#1 : RegisterType Register.elp)) :
    (systemProject js).regs.get? Register.elp =
      some (0#1 : RegisterType Register.elp) := by
  rw [systemProject_get_unmodified]
  exact help
  all_goals decide

/-- `systemProject` materializes virtual `mstatus` at the Sail `mstatus` key. -/
theorem systemProject_mstatus_read
    (js : SailJoltState) :
    (systemProject js).regs.get? Register.mstatus =
      some (js.vregs JoltISA.mstatusVReg : RegisterType Register.mstatus) := by
  unfold systemProject
  simp only [Std.ExtDHashMap.get?_insert_self]

/-- `systemProject` materializes virtual `mtvec` at the Sail `mtvec` key. -/
theorem systemProject_mtvec_read
    (js : SailJoltState) :
    (systemProject js).regs.get? Register.mtvec =
      some (js.vregs JoltISA.trapHandlerVReg : RegisterType Register.mtvec) := by
  unfold systemProject
  rw [extDHashMap_get?_insert_of_ne (h := by decide)]
  rw [extDHashMap_get?_insert_of_ne (h := by decide)]
  rw [extDHashMap_get?_insert_of_ne (h := by decide)]
  rw [extDHashMap_get?_insert_of_ne (h := by decide)]
  rw [extDHashMap_get?_insert_of_ne (h := by decide)]
  rw [Std.ExtDHashMap.get?_insert_self]

/-- `systemProject` materializes virtual `mscratch` at the Sail `mscratch` key. -/
theorem systemProject_mscratch_read
    (js : SailJoltState) :
    (systemProject js).regs.get? Register.mscratch =
      some (js.vregs JoltISA.mscratchVReg : RegisterType Register.mscratch) := by
  unfold systemProject
  rw [extDHashMap_get?_insert_of_ne (h := by decide)]
  rw [extDHashMap_get?_insert_of_ne (h := by decide)]
  rw [extDHashMap_get?_insert_of_ne (h := by decide)]
  rw [extDHashMap_get?_insert_of_ne (h := by decide)]
  rw [Std.ExtDHashMap.get?_insert_self]

/-- `systemProject` materializes virtual `mepc` at the Sail `mepc` key. -/
theorem systemProject_mepc_read
    (js : SailJoltState) :
    (systemProject js).regs.get? Register.mepc =
      some (js.vregs JoltISA.mepcVReg : RegisterType Register.mepc) := by
  unfold systemProject
  rw [extDHashMap_get?_insert_of_ne (h := by decide)]
  rw [extDHashMap_get?_insert_of_ne (h := by decide)]
  rw [extDHashMap_get?_insert_of_ne (h := by decide)]
  rw [Std.ExtDHashMap.get?_insert_self]

/-- `systemProject` materializes virtual `mcause` at the Sail `mcause` key. -/
theorem systemProject_mcause_read
    (js : SailJoltState) :
    (systemProject js).regs.get? Register.mcause =
      some (js.vregs JoltISA.mcauseVReg : RegisterType Register.mcause) := by
  unfold systemProject
  rw [extDHashMap_get?_insert_of_ne (h := by decide)]
  rw [extDHashMap_get?_insert_of_ne (h := by decide)]
  rw [Std.ExtDHashMap.get?_insert_self]

/-- `systemProject` materializes virtual `mtval` at the Sail `mtval` key. -/
theorem systemProject_mtval_read
    (js : SailJoltState) :
    (systemProject js).regs.get? Register.mtval =
      some (js.vregs JoltISA.mtvalVReg : RegisterType Register.mtval) := by
  unfold systemProject
  rw [extDHashMap_get?_insert_of_ne (h := by decide)]
  rw [Std.ExtDHashMap.get?_insert_self]

private theorem mstatus_mpelp_zero_update_eq_self
    (mstatus : BitVec 64) (h41 : mstatus.getLsbD 41 = false) :
    Sail.BitVec.updateSubrange mstatus 41 41 0#1 = mstatus := by
  unfold Sail.BitVec.updateSubrange Sail.BitVec.updateSubrange'
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.zeroExtend_eq_setWidth, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, BitVec.getLsbD_ofNat]
  by_cases hidx : i = 41
  · subst i
    simpa [BitVec.getLsbD_eq_getElem] using h41
  · by_cases hlt : i < 41
    · have hsub : i - 41 = 0 := by omega
      simp [hlt, hsub, hi]
    · have hsub_not_lt : ¬i - 41 < 1 := by omega
      simp [hlt, hsub_not_lt, hi]

/-- If the machine-trap mstatus update already equals Jolt's ZeroOS value, then
Zicfilp's `mstatus[41] := 0` write is redundant. -/
theorem ecall_mstatus_zicfilp_write_eq_self
    (mstatus : BitVec 64)
    (h : sailMachineTrapMstatus mstatus = zeroOSMstatus) :
    Sail.BitVec.updateSubrange mstatus 41 41 0#1 = mstatus := by
  have h41 : mstatus.getLsbD 41 = false := by
    have hbit := congrArg (fun x : BitVec 64 => x.getLsbD 41) h
    unfold sailMachineTrapMstatus zeroOSMstatus at hbit
    unfold Sail.BitVec.updateSubrange Sail.BitVec.updateSubrange' at hbit
    simp only [BitVec.zeroExtend_eq_setWidth, BitVec.getLsbD_or,
      BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, BitVec.getLsbD_ofNat]
      at hbit
    norm_num at hbit
    exact hbit
  exact mstatus_mpelp_zero_update_eq_self mstatus h41

/-- For the ECALL envelope, Sail's Zicfilp trap hook is state-neutral:
`mstatus[41]` and `elp` are already zero. -/
theorem zicfilp_preserve_elp_machine_ecall_run
    (js : SailJoltState)
    (help : js.sail.regs.get? Register.elp =
      some (0#1 : RegisterType Register.elp))
    (hmstatus : sailMachineTrapMstatus (js.vregs JoltISA.mstatusVReg) =
      zeroOSMstatus) :
    zicfilp_preserve_elp_on_trap Privilege.Machine (systemProject js) =
      .ok () (systemProject js) := by
  have hMstatusRead := systemProject_mstatus_read js
  have hElpRead := systemProject_elp_read js help
  have hMstatusSame := ecall_mstatus_zicfilp_write_eq_self
    (js.vregs JoltISA.mstatusVReg) hmstatus
  have hMinsert : (systemProject js).regs.insert Register.mstatus
      (js.vregs JoltISA.mstatusVReg) = (systemProject js).regs := by
    exact extDHashMap_insert_eq_self_of_get? (systemProject js).regs
      Register.mstatus (js.vregs JoltISA.mstatusVReg) hMstatusRead
  have hElpInsert : (systemProject js).regs.insert Register.elp
      (0#1 : RegisterType Register.elp) = (systemProject js).regs := by
    exact extDHashMap_insert_eq_self_of_get? (systemProject js).regs
      Register.elp (0#1) hElpRead
  unfold zicfilp_preserve_elp_on_trap reset_elp
  unfold Sail.readReg PreSail.readReg Sail.writeReg PreSail.writeReg
  simp only [hMstatusRead, hElpRead, hMstatusSame, hMinsert, hElpInsert,
    landing_pad_bits_backwards, bind, EStateM.bind, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- Sail's two `mcause` writes for machine ECALL produce the same cause value
that the Rust/Jolt row writes to virtual `mcause`. -/
theorem ecall_mcause_machine_write_value (old : BitVec 64) :
    Sail.BitVec.updateSubrange
        (Sail.BitVec.updateSubrange old (64 -i 1) (64 -i 1)
          (bool_to_bit
            (trapCause_is_interrupt
              (TrapCause.Exception (ExceptionType.E_M_EnvCall ())))))
        (64 -i 2) 0
        (zero_extend (m := (64 -i 1))
          (trapCause_bits_forwards
            (TrapCause.Exception (ExceptionType.E_M_EnvCall ())))) =
      ecallMachineCause := by
  have hcause63 : zero_extend (m := (64 -i 1))
      (trapCause_bits_forwards
        (TrapCause.Exception (ExceptionType.E_M_EnvCall ()))) = 11#63 := by
    decide
  have hcause64 : ecallMachineCause = 11#64 := by
    decide
  rw [hcause63, hcause64]
  unfold trapCause_is_interrupt bool_to_bit bool_bit_forwards
  unfold Sail.BitVec.updateSubrange Sail.BitVec.updateSubrange'
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;>
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_allOnes, BitVec.getLsbD_ofNat, Bool.true_and, Bool.false_and,
      Bool.true_or, Bool.false_or, Bool.not_true, Bool.not_false] <;>
    norm_num <;>
    decide

/-- Machine ECALL has no trap-value payload, so Sail writes zero to `mtval`. -/
theorem ecall_tval_none :
    tval none = (0#64 : BitVec 64) := by
  rfl

/-!
## Concrete ECALL phases

The ECALL proof follows the same shape as the load/store/atomic families: each
Rust row gets a concrete state description, and the theorem only composes those
row lemmas.
-/

/-- Replace one Jolt virtual register in a register-file function. -/
def vregWrite (vregs : BitVec 7 → BitVec 64) (vr : JoltISA.VReg)
    (value : BitVec 64) : BitVec 7 → BitVec 64 :=
  fun r => if r = vr then value else vregs r

/-- Replace one Jolt virtual register in the full Jolt state. -/
def joltSetVReg (js : SailJoltState) (vr : JoltISA.VReg)
    (value : BitVec 64) : SailJoltState :=
  { js with vregs := vregWrite js.vregs vr value }

/-- Final state for the CSRRW write-only `csrw csr, rs1` case. -/
def csrrwAfterCsrWrite
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rs1Val : BitVec 64) :
    SailJoltState :=
  joltSetVReg js (JoltISA.SystemCSR.vreg csr) rs1Val

/-- Final CSRRW state after `rd` receives the old CSR value and the virtual CSR
receives `rs1`. -/
def csrrwAfterReadWrite
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rd : regidx)
    (oldCsr rs1Val : BitVec 64) : SailJoltState :=
  joltSetVReg { js with sail := stateAfterWrite js.sail rd oldCsr }
    (JoltISA.SystemCSR.vreg csr) rs1Val

/-- Final CSRRW state for the `rd = rs1` branch: the source is preserved in
scratch, the old CSR is written to `rd`, then the preserved value is restored
to the CSR virtual register. -/
def csrrwAfterSameReg
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rd : regidx)
    (oldCsr rs1Val : BitVec 64) : SailJoltState :=
  joltSetVReg
    { joltSetVReg js JoltISA.systemScratchVReg rs1Val with
      sail := stateAfterWrite js.sail rd oldCsr }
    (JoltISA.SystemCSR.vreg csr) rs1Val

/-- The concrete final Jolt state selected by Rust's CSRRW expansion branches. -/
def csrrwJoltFinal
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rs1 rd : regidx)
    (rs1Val : BitVec 64) : SailJoltState :=
  if JoltISA.isX0 rd then
    csrrwAfterCsrWrite js csr rs1Val
  else if JoltISA.sameXReg rd rs1 then
    csrrwAfterSameReg js csr rd
      (js.vregs (JoltISA.SystemCSR.vreg csr)) rs1Val
  else
    csrrwAfterReadWrite js csr rd
      (js.vregs (JoltISA.SystemCSR.vreg csr)) rs1Val

/-- Sail state after writing `nextPC`; used by Jolt `JALR` and Sail trap entry. -/
def setNextPCState (s : SailState) (target : BitVec 64) : SailState :=
  { s with regs := s.regs.insert Register.nextPC target }

/-- Projecting after a Sail `nextPC` write is the same as writing `nextPC`
after projecting Jolt's virtual CSR registers. -/
theorem systemProject_setNextPCState
    (js : SailJoltState) (target : BitVec 64) :
    systemProject { js with sail := setNextPCState js.sail target } =
      { systemProject js with
        regs := (systemProject js).regs.insert Register.nextPC target } := by
  unfold systemProject setNextPCState
  simp only
  congr 1
  calc
    (((((((js.sail.regs.insert Register.nextPC target).insert Register.mtvec
                    (js.vregs JoltISA.trapHandlerVReg)).insert Register.mscratch
                  (js.vregs JoltISA.mscratchVReg)).insert Register.mepc
                (js.vregs JoltISA.mepcVReg)).insert Register.mcause
              (js.vregs JoltISA.mcauseVReg)).insert Register.mtval
            (js.vregs JoltISA.mtvalVReg)).insert Register.mstatus
          (js.vregs JoltISA.mstatusVReg))
        = (((((((js.sail.regs.insert Register.mtvec
                    (js.vregs JoltISA.trapHandlerVReg)).insert Register.nextPC target).insert Register.mscratch
                  (js.vregs JoltISA.mscratchVReg)).insert Register.mepc
                (js.vregs JoltISA.mepcVReg)).insert Register.mcause
              (js.vregs JoltISA.mcauseVReg)).insert Register.mtval
            (js.vregs JoltISA.mtvalVReg)).insert Register.mstatus
          (js.vregs JoltISA.mstatusVReg)) := by
          rw [extDHashMap_insert_comm_of_ne
            (m := js.sail.regs)
            (k1 := Register.nextPC) (k2 := Register.mtvec)
            (v1 := target) (v2 := js.vregs JoltISA.trapHandlerVReg)
            (h := by decide)]
    _ = (((((((js.sail.regs.insert Register.mtvec
                    (js.vregs JoltISA.trapHandlerVReg)).insert Register.mscratch
                  (js.vregs JoltISA.mscratchVReg)).insert Register.nextPC target).insert Register.mepc
                (js.vregs JoltISA.mepcVReg)).insert Register.mcause
              (js.vregs JoltISA.mcauseVReg)).insert Register.mtval
            (js.vregs JoltISA.mtvalVReg)).insert Register.mstatus
          (js.vregs JoltISA.mstatusVReg)) := by
          rw [extDHashMap_insert_comm_of_ne
            (m := (js.sail.regs.insert Register.mtvec
              (js.vregs JoltISA.trapHandlerVReg)))
            (k1 := Register.nextPC) (k2 := Register.mscratch)
            (v1 := target) (v2 := js.vregs JoltISA.mscratchVReg)
            (h := by decide)]
    _ = (((((((js.sail.regs.insert Register.mtvec
                    (js.vregs JoltISA.trapHandlerVReg)).insert Register.mscratch
                  (js.vregs JoltISA.mscratchVReg)).insert Register.mepc
                (js.vregs JoltISA.mepcVReg)).insert Register.nextPC target).insert Register.mcause
              (js.vregs JoltISA.mcauseVReg)).insert Register.mtval
            (js.vregs JoltISA.mtvalVReg)).insert Register.mstatus
          (js.vregs JoltISA.mstatusVReg)) := by
          rw [extDHashMap_insert_comm_of_ne
            (m := ((js.sail.regs.insert Register.mtvec
              (js.vregs JoltISA.trapHandlerVReg)).insert Register.mscratch
              (js.vregs JoltISA.mscratchVReg)))
            (k1 := Register.nextPC) (k2 := Register.mepc)
            (v1 := target) (v2 := js.vregs JoltISA.mepcVReg)
            (h := by decide)]
    _ = (((((((js.sail.regs.insert Register.mtvec
                    (js.vregs JoltISA.trapHandlerVReg)).insert Register.mscratch
                  (js.vregs JoltISA.mscratchVReg)).insert Register.mepc
                (js.vregs JoltISA.mepcVReg)).insert Register.mcause
              (js.vregs JoltISA.mcauseVReg)).insert Register.nextPC target).insert Register.mtval
            (js.vregs JoltISA.mtvalVReg)).insert Register.mstatus
          (js.vregs JoltISA.mstatusVReg)) := by
          rw [extDHashMap_insert_comm_of_ne
            (m := (((js.sail.regs.insert Register.mtvec
              (js.vregs JoltISA.trapHandlerVReg)).insert Register.mscratch
              (js.vregs JoltISA.mscratchVReg)).insert Register.mepc
              (js.vregs JoltISA.mepcVReg)))
            (k1 := Register.nextPC) (k2 := Register.mcause)
            (v1 := target) (v2 := js.vregs JoltISA.mcauseVReg)
            (h := by decide)]
    _ = (((((((js.sail.regs.insert Register.mtvec
                    (js.vregs JoltISA.trapHandlerVReg)).insert Register.mscratch
                  (js.vregs JoltISA.mscratchVReg)).insert Register.mepc
                (js.vregs JoltISA.mepcVReg)).insert Register.mcause
              (js.vregs JoltISA.mcauseVReg)).insert Register.mtval
            (js.vregs JoltISA.mtvalVReg)).insert Register.nextPC target).insert Register.mstatus
          (js.vregs JoltISA.mstatusVReg)) := by
          rw [extDHashMap_insert_comm_of_ne
            (m := ((((js.sail.regs.insert Register.mtvec
              (js.vregs JoltISA.trapHandlerVReg)).insert Register.mscratch
              (js.vregs JoltISA.mscratchVReg)).insert Register.mepc
              (js.vregs JoltISA.mepcVReg)).insert Register.mcause
              (js.vregs JoltISA.mcauseVReg)))
            (k1 := Register.nextPC) (k2 := Register.mtval)
            (v1 := target) (v2 := js.vregs JoltISA.mtvalVReg)
            (h := by decide)]
    _ = (((((((js.sail.regs.insert Register.mtvec
                    (js.vregs JoltISA.trapHandlerVReg)).insert Register.mscratch
                  (js.vregs JoltISA.mscratchVReg)).insert Register.mepc
                (js.vregs JoltISA.mepcVReg)).insert Register.mcause
              (js.vregs JoltISA.mcauseVReg)).insert Register.mtval
            (js.vregs JoltISA.mtvalVReg)).insert Register.mstatus
          (js.vregs JoltISA.mstatusVReg)).insert Register.nextPC target) := by
          rw [extDHashMap_insert_comm_of_ne
            (m := (((((js.sail.regs.insert Register.mtvec
              (js.vregs JoltISA.trapHandlerVReg)).insert Register.mscratch
              (js.vregs JoltISA.mscratchVReg)).insert Register.mepc
              (js.vregs JoltISA.mepcVReg)).insert Register.mcause
              (js.vregs JoltISA.mcauseVReg)).insert Register.mtval
              (js.vregs JoltISA.mtvalVReg)))
            (k1 := Register.nextPC) (k2 := Register.mstatus)
            (v1 := target) (v2 := js.vregs JoltISA.mstatusVReg)
            (h := by decide)]

/-- Projecting after an architectural x-register write is the same as applying
that write after projecting Jolt's virtual CSR registers. -/
theorem systemProject_stateAfterWrite
    (js : SailJoltState) (rd : regidx) (value : BitVec 64) :
    systemProject { js with sail := stateAfterWrite js.sail rd value } =
      stateAfterWrite (systemProject js) rd value := by
  unfold systemProject stateAfterWrite wX_update_regs regval_into_reg
  obtain ⟨rdBits⟩ := rd
  reg_cases (regidx.Regidx rdBits) <;>
    simp_all [extDHashMap_insert_comm_of_ne]

/-- Running generated Sail `set_next_pc` through `systemProject` is the same
projected state as Jolt's final `JALR` Sail-state update. -/
theorem set_next_pc_systemProject_run
    (js : SailJoltState) (target : BitVec 64) :
    (set_next_pc target).run (systemProject js) =
      .ok () (systemProject { js with sail := setNextPCState js.sail target }) := by
  unfold set_next_pc sail_branch_announce redirect_callback
  unfold Sail.writeReg PreSail.writeReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  rw [← systemProject_setNextPCState]

/-- ECALL row 0: `AUIPC ecall_addr, 0` writes the current PC to v40. -/
def ecallAfterAuipc (js : SailJoltState) (pc : BitVec 64) : SailJoltState :=
  joltSetVReg js JoltISA.systemScratchVReg pc

/-- ECALL row 1: `ADDI mepc, ecall_addr, 0` copies v40 to virtual `mepc`. -/
def ecallAfterMepc (js : SailJoltState) (pc : BitVec 64) : SailJoltState :=
  joltSetVReg (ecallAfterAuipc js pc) JoltISA.mepcVReg pc

/-- ECALL row 2: `ADDI mcause, x0, 11` records machine-mode ECALL. -/
def ecallAfterMcause (js : SailJoltState) (pc : BitVec 64) : SailJoltState :=
  joltSetVReg (ecallAfterMepc js pc) JoltISA.mcauseVReg ecallMachineCause

/-- ECALL row 3: `ADDI mtval, x0, 0` records no trap value. -/
def ecallAfterMtval (js : SailJoltState) (pc : BitVec 64) : SailJoltState :=
  joltSetVReg (ecallAfterMcause js pc) JoltISA.mtvalVReg 0#64

/-- ECALL row 4: `ADDI three, x0, 3` reuses the scratch register. -/
def ecallAfterThree (js : SailJoltState) (pc : BitVec 64) : SailJoltState :=
  joltSetVReg (ecallAfterMtval js pc) JoltISA.systemScratchVReg 3#64

/-- ECALL row 5: lowered `SLLI mstatus, three, 11` writes `0x1800`. -/
def ecallAfterMstatus (js : SailJoltState) (pc : BitVec 64) : SailJoltState :=
  joltSetVReg (ecallAfterThree js pc) JoltISA.mstatusVReg zeroOSMstatus

/-- ECALL row 6: `JALR scratch, mtvec, 0` writes `nextPC` and discards link. -/
def ecallAfterJalr (js : SailJoltState) (pc nextPC : BitVec 64) :
    SailJoltState :=
  joltSetVReg
    { ecallAfterMstatus js pc with
      sail := setNextPCState js.sail (ecallTrapTarget js) }
    JoltISA.systemScratchVReg
    nextPC

/-- The concrete final Jolt state for Rust ECALL expansion. -/
def ecallJoltFinal (js : SailJoltState) (pc nextPC : BitVec 64) :
    SailJoltState :=
  ecallAfterJalr js pc nextPC

/-- Machine ECALL's Sail cause is the same immediate used by the Rust row. -/
theorem ecallMachineCause_eq_jolt_imm :
    sign_extend (m := 64) (11 : BitVec 12) = ecallMachineCause := by
  decide

/-- The lowered `SLLI` multiplication row computes Jolt's ZeroOS mstatus. -/
theorem virtualMuli_three_to_zeroOS :
    jolt_virtual_muli_value (3#64) (2048#64) = zeroOSMstatus := by
  decide

/-- A zero AUIPC immediate contributes no offset. -/
theorem auipc_zero_offset (pc : BitVec 64) :
    pc + sign_extend (m := 64) ((0 : BitVec 20) +++ 0#12) = pc := by
  have hoff : sign_extend (m := 64) ((0 : BitVec 20) +++ 0#12) = 0#64 := by
    decide
  rw [hoff]
  norm_num

/-- ECALL's trap target already has bit 0 cleared by the JALR rule. -/
theorem ecallTrapTarget_bit0_zero (js : SailJoltState) :
    BitVec.access (ecallTrapTarget js) 0 = 0#1 := by
  unfold ecallTrapTarget
  unfold Sail.BitVec.access Sail.BitVec.update Sail.BitVec.updateSubrange'
  rw [getElem!_pos (h := by decide)]
  norm_num
  rfl

/-- Writing a virtual register and reading that same register returns the new
value. -/
theorem vregWrite_self (vregs : BitVec 7 → BitVec 64) (vr : JoltISA.VReg)
    (value : BitVec 64) :
    vregWrite vregs vr value vr = value := by
  unfold vregWrite
  exact if_pos rfl

/-- Writing one virtual register leaves every different virtual register alone. -/
theorem vregWrite_other (vregs : BitVec 7 → BitVec 64)
    (written read : JoltISA.VReg) (value : BitVec 64)
    (h_ne : read ≠ written) :
    vregWrite vregs written value read = vregs read := by
  unfold vregWrite
  exact if_neg h_ne

/-- `ADDI x, 0` leaves a 64-bit Jolt value unchanged. -/
theorem addi_zero_value (x : BitVec 64) :
    x + sign_extend (m := 64) (0 : BitVec 12) = x := by
  have hzero : sign_extend (m := 64) (0 : BitVec 12) = 0#64 := by
    decide
  rw [hzero]
  norm_num

/-- JALR with immediate zero computes the ECALL trap target. -/
theorem ecallJalrTarget_zero_imm (js : SailJoltState) :
    BitVec.update
        (js.vregs JoltISA.trapHandlerVReg + sign_extend (m := 64) (0 : BitVec 12))
        0 0#1 =
      ecallTrapTarget js := by
  rw [addi_zero_value]
  rfl

/-- `ADDI x0, 11` is the machine-mode ECALL cause value. -/
theorem addi_ecall_machine_cause_value :
    0#64 + sign_extend (m := 64) (11 : BitVec 12) = ecallMachineCause := by
  rw [ecallMachineCause_eq_jolt_imm]
  decide

/-- `ADDI x0, 3` produces the scratch value used by the lowered `SLLI`. -/
theorem addi_three_value :
    0#64 + sign_extend (m := 64) (3 : BitVec 12) = 3#64 := by
  decide

/-- The trap-handler virtual register is distinct from ECALL's scratch register. -/
theorem trapHandler_ne_systemScratch :
    JoltISA.trapHandlerVReg ≠ JoltISA.systemScratchVReg := by
  decide

/-- The trap-handler virtual register is distinct from virtual `mepc`. -/
theorem trapHandler_ne_mepc :
    JoltISA.trapHandlerVReg ≠ JoltISA.mepcVReg := by
  decide

/-- The trap-handler virtual register is distinct from virtual `mcause`. -/
theorem trapHandler_ne_mcause :
    JoltISA.trapHandlerVReg ≠ JoltISA.mcauseVReg := by
  decide

/-- The trap-handler virtual register is distinct from virtual `mtval`. -/
theorem trapHandler_ne_mtval :
    JoltISA.trapHandlerVReg ≠ JoltISA.mtvalVReg := by
  decide

/-- The trap-handler virtual register is distinct from virtual `mstatus`. -/
theorem trapHandler_ne_mstatus :
    JoltISA.trapHandlerVReg ≠ JoltISA.mstatusVReg := by
  decide

/-- The ECALL mstatus phase leaves the trap-handler virtual register untouched. -/
theorem ecallAfterMstatus_trapHandler
    (js : SailJoltState) (pc : BitVec 64) :
    (ecallAfterMstatus js pc).vregs JoltISA.trapHandlerVReg =
      js.vregs JoltISA.trapHandlerVReg := by
  unfold ecallAfterMstatus ecallAfterThree ecallAfterMtval
  unfold ecallAfterMcause ecallAfterMepc ecallAfterAuipc
  unfold joltSetVReg vregWrite
  simp only [trapHandler_ne_mstatus, trapHandler_ne_systemScratch,
    trapHandler_ne_mtval, trapHandler_ne_mcause, trapHandler_ne_mepc, if_false]

/-- ECALL's virtual CSR materialization rows do not alter the embedded Sail
state. -/
theorem ecallAfterMstatus_sail
    (js : SailJoltState) (pc : BitVec 64) :
    (ecallAfterMstatus js pc).sail = js.sail := by
  unfold ecallAfterMstatus ecallAfterThree ecallAfterMtval
  unfold ecallAfterMcause ecallAfterMepc ecallAfterAuipc
  unfold joltSetVReg
  rfl

/-- ECALL's virtual CSR materialization leaves virtual `mscratch` unchanged. -/
theorem ecallAfterMstatus_mscratch
    (js : SailJoltState) (pc : BitVec 64) :
    (ecallAfterMstatus js pc).vregs JoltISA.mscratchVReg =
      js.vregs JoltISA.mscratchVReg := by
  unfold ecallAfterMstatus ecallAfterThree ecallAfterMtval
  unfold ecallAfterMcause ecallAfterMepc ecallAfterAuipc
  unfold joltSetVReg vregWrite
  have h1 : JoltISA.mscratchVReg ≠ JoltISA.mstatusVReg := by decide
  have h2 : JoltISA.mscratchVReg ≠ JoltISA.systemScratchVReg := by decide
  have h3 : JoltISA.mscratchVReg ≠ JoltISA.mtvalVReg := by decide
  have h4 : JoltISA.mscratchVReg ≠ JoltISA.mcauseVReg := by decide
  have h5 : JoltISA.mscratchVReg ≠ JoltISA.mepcVReg := by decide
  simp only [h1, h2, h3, h4, h5, if_false]

/-- ECALL's virtual CSR materialization writes `mepc = pc`. -/
theorem ecallAfterMstatus_mepc
    (js : SailJoltState) (pc : BitVec 64) :
    (ecallAfterMstatus js pc).vregs JoltISA.mepcVReg = pc := by
  unfold ecallAfterMstatus ecallAfterThree ecallAfterMtval
  unfold ecallAfterMcause ecallAfterMepc ecallAfterAuipc
  unfold joltSetVReg vregWrite
  have h1 : JoltISA.mepcVReg ≠ JoltISA.mstatusVReg := by decide
  have h2 : JoltISA.mepcVReg ≠ JoltISA.systemScratchVReg := by decide
  have h3 : JoltISA.mepcVReg ≠ JoltISA.mtvalVReg := by decide
  have h4 : JoltISA.mepcVReg ≠ JoltISA.mcauseVReg := by decide
  simp only [h1, h2, h3, h4, if_false, if_true]

/-- ECALL's virtual CSR materialization writes the machine ECALL cause. -/
theorem ecallAfterMstatus_mcause
    (js : SailJoltState) (pc : BitVec 64) :
    (ecallAfterMstatus js pc).vregs JoltISA.mcauseVReg =
      ecallMachineCause := by
  unfold ecallAfterMstatus ecallAfterThree ecallAfterMtval
  unfold ecallAfterMcause ecallAfterMepc ecallAfterAuipc
  unfold joltSetVReg vregWrite
  have h1 : JoltISA.mcauseVReg ≠ JoltISA.mstatusVReg := by decide
  have h2 : JoltISA.mcauseVReg ≠ JoltISA.systemScratchVReg := by decide
  have h3 : JoltISA.mcauseVReg ≠ JoltISA.mtvalVReg := by decide
  simp only [h1, h2, h3, if_false, if_true]

/-- ECALL's virtual CSR materialization writes `mtval = 0`. -/
theorem ecallAfterMstatus_mtval
    (js : SailJoltState) (pc : BitVec 64) :
    (ecallAfterMstatus js pc).vregs JoltISA.mtvalVReg = 0#64 := by
  unfold ecallAfterMstatus ecallAfterThree ecallAfterMtval
  unfold ecallAfterMcause ecallAfterMepc ecallAfterAuipc
  unfold joltSetVReg vregWrite
  have h1 : JoltISA.mtvalVReg ≠ JoltISA.mstatusVReg := by decide
  have h2 : JoltISA.mtvalVReg ≠ JoltISA.systemScratchVReg := by decide
  simp only [h1, h2, if_false, if_true]

/-- ECALL's virtual CSR materialization writes the ZeroOS trap `mstatus`. -/
theorem ecallAfterMstatus_mstatus
    (js : SailJoltState) (pc : BitVec 64) :
    (ecallAfterMstatus js pc).vregs JoltISA.mstatusVReg = zeroOSMstatus := by
  unfold ecallAfterMstatus joltSetVReg vregWrite
  simp only [if_true]

/-- ECALL's final Jolt state has Sail `nextPC` set to the trap target. -/
theorem ecallJoltFinal_sail
    (js : SailJoltState) (pc nextPC : BitVec 64) :
    (ecallJoltFinal js pc nextPC).sail =
      setNextPCState js.sail (ecallTrapTarget js) := by
  unfold ecallJoltFinal ecallAfterJalr
  unfold joltSetVReg
  rfl

/-- The final local scratch write does not change projected virtual `mtvec`. -/
theorem ecallJoltFinal_trapHandler
    (js : SailJoltState) (pc nextPC : BitVec 64) :
    (ecallJoltFinal js pc nextPC).vregs JoltISA.trapHandlerVReg =
      js.vregs JoltISA.trapHandlerVReg := by
  unfold ecallJoltFinal ecallAfterJalr
  unfold joltSetVReg vregWrite
  simp only [trapHandler_ne_systemScratch, if_false,
    ecallAfterMstatus_trapHandler]

/-- The final local scratch write does not change projected virtual `mscratch`. -/
theorem ecallJoltFinal_mscratch
    (js : SailJoltState) (pc nextPC : BitVec 64) :
    (ecallJoltFinal js pc nextPC).vregs JoltISA.mscratchVReg =
      js.vregs JoltISA.mscratchVReg := by
  unfold ecallJoltFinal ecallAfterJalr
  unfold joltSetVReg vregWrite
  have h : JoltISA.mscratchVReg ≠ JoltISA.systemScratchVReg := by
    decide
  simp only [h, if_false, ecallAfterMstatus_mscratch]

/-- The final local scratch write does not change projected virtual `mepc`. -/
theorem ecallJoltFinal_mepc
    (js : SailJoltState) (pc nextPC : BitVec 64) :
    (ecallJoltFinal js pc nextPC).vregs JoltISA.mepcVReg = pc := by
  unfold ecallJoltFinal ecallAfterJalr
  unfold joltSetVReg vregWrite
  have h : JoltISA.mepcVReg ≠ JoltISA.systemScratchVReg := by
    decide
  simp only [h, if_false, ecallAfterMstatus_mepc]

/-- The final local scratch write does not change projected virtual `mcause`. -/
theorem ecallJoltFinal_mcause
    (js : SailJoltState) (pc nextPC : BitVec 64) :
    (ecallJoltFinal js pc nextPC).vregs JoltISA.mcauseVReg =
      ecallMachineCause := by
  unfold ecallJoltFinal ecallAfterJalr
  unfold joltSetVReg vregWrite
  have h : JoltISA.mcauseVReg ≠ JoltISA.systemScratchVReg := by
    decide
  simp only [h, if_false, ecallAfterMstatus_mcause]

/-- The final local scratch write does not change projected virtual `mtval`. -/
theorem ecallJoltFinal_mtval
    (js : SailJoltState) (pc nextPC : BitVec 64) :
    (ecallJoltFinal js pc nextPC).vregs JoltISA.mtvalVReg = 0#64 := by
  unfold ecallJoltFinal ecallAfterJalr
  unfold joltSetVReg vregWrite
  have h : JoltISA.mtvalVReg ≠ JoltISA.systemScratchVReg := by
    decide
  simp only [h, if_false, ecallAfterMstatus_mtval]

/-- The final local scratch write does not change projected virtual `mstatus`. -/
theorem ecallJoltFinal_mstatus
    (js : SailJoltState) (pc nextPC : BitVec 64) :
    (ecallJoltFinal js pc nextPC).vregs JoltISA.mstatusVReg =
      zeroOSMstatus := by
  unfold ecallJoltFinal ecallAfterJalr
  unfold joltSetVReg vregWrite
  have h : JoltISA.mstatusVReg ≠ JoltISA.systemScratchVReg := by
    decide
  simp only [h, if_false, ecallAfterMstatus_mstatus]

/-- Projecting ECALL's final Jolt state is the same as projecting the
post-CSR-write state after Sail `set_next_pc`.

The final JALR row only changes the embedded Sail `nextPC` and a scratch
virtual register; `systemProject` ignores that scratch register. -/
theorem systemProject_ecallJoltFinal_setNext
    (js : SailJoltState) (pc nextPC : BitVec 64) :
    systemProject (ecallJoltFinal js pc nextPC) =
      systemProject
        { ecallAfterMstatus js pc with
          sail := setNextPCState (ecallAfterMstatus js pc).sail
            (ecallTrapTarget js) } := by
  unfold systemProject
  simp only [ecallJoltFinal_sail, ecallJoltFinal_trapHandler,
    ecallJoltFinal_mscratch, ecallJoltFinal_mepc, ecallJoltFinal_mcause,
    ecallJoltFinal_mtval, ecallJoltFinal_mstatus,
    ecallAfterMstatus_sail, ecallAfterMstatus_trapHandler,
    ecallAfterMstatus_mscratch,
    ecallAfterMstatus_mepc, ecallAfterMstatus_mcause,
    ecallAfterMstatus_mtval, ecallAfterMstatus_mstatus]

/-- Sail's compressed-extension query reads `misa` and otherwise leaves state
unchanged.  `jump_to` evaluates this even when the trap target's bit 1 is
already clear. -/
theorem currentlyEnabled_Ext_C_run
    (s : SailState) (misa : BitVec 64)
    (hmisa : s.regs.get? Register.misa =
      some (misa : RegisterType Register.misa)) :
    (currentlyEnabled extension.Ext_C) s =
      .ok (hartSupports extension.Ext_C && ((_get_Misa_C misa) == 1#1)) s := by
  unfold currentlyEnabled Sail.readReg PreSail.readReg
  simp only [hmisa, bind, EStateM.bind, pure, EStateM.pure,
    MonadStateOf.get, EStateM.get, getThe, get]

/-- Jumping to ECALL's projected trap target succeeds and writes `nextPC`.

The generated Sail `jump_to` still evaluates `currentlyEnabled Ext_C` through
`Ext_Zca`, so this helper keeps that read localized to one control-flow fact. -/
theorem jump_to_ecallTrapTarget_run
    (js : SailJoltState) (misa : BitVec 64)
    (hmisa : js.sail.regs.get? Register.misa =
      some (misa : RegisterType Register.misa))
    (hfetch : BitVec.access (ecallTrapTarget js) 1 = 0#1) :
    jump_to (ecallTrapTarget js) js.sail =
      .ok RETIRE_SUCCESS (setNextPCState js.sail (ecallTrapTarget js)) := by
  have hExtC := currentlyEnabled_Ext_C_run js.sail misa hmisa
  have hassert : (0#1 == 0#1) = true := by
    decide
  have hbit1 : bool_bit_backwards 0#1 = false := by
    decide
  unfold jump_to ext_control_check_pc SailME.run PreSail.PreSailME.run
  unfold currentlyEnabled hartSupports
  unfold set_next_pc setNextPCState sail_branch_announce redirect_callback
  unfold Sail.assert PreSail.assert Sail.writeReg PreSail.writeReg
  simp only [hassert, hbit1, hExtC, ecallTrapTarget_bit0_zero, hfetch, bit_to_bool,
    if_true, if_false, Bool.false_and, Bool.false_eq_true, bind, EStateM.bind, EStateM.run,
    pure, EStateM.pure, EStateM.map, Functor.map, ExceptT.run, ExceptT.mk,
    ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift,
    MonadLift.monadLift, monadLift, liftM, modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet]

/-- In this generated model, `Zicsr` support is unconditional and does not read
or write state. -/
theorem currentlyEnabled_Ext_Zicsr_run (s : SailState) :
    currentlyEnabled extension.Ext_Zicsr s = .ok true s := by
  unfold currentlyEnabled hartSupports
  simp only [pure, EStateM.pure]

/-- Machine-mode synchronous exceptions are handled in Machine mode.

Sail still reads `medeleg` and `misa` while computing the delegatee, but when the
current privilege is Machine the final delegatee cannot become less privileged. -/
theorem exception_delegatee_machine_ecall_run
    (s : SailState) (medeleg misa : BitVec 64)
    (hmedeleg : s.regs.get? Register.medeleg =
      some (medeleg : RegisterType Register.medeleg))
    (hmisa : s.regs.get? Register.misa =
      some (misa : RegisterType Register.misa)) :
    exception_delegatee (ExceptionType.E_M_EnvCall ()) Privilege.Machine s =
      .ok Privilege.Machine s := by
  have hZicsr := currentlyEnabled_Ext_Zicsr_run s
  unfold exception_delegatee currentlyEnabled Sail.readReg PreSail.readReg
  simp only [hmedeleg, hmisa, hZicsr, hartSupports, bind, EStateM.bind,
    pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get]
  by_cases hdeleg : (true && (_get_Misa_S misa == 1#1 && true) &&
      bit_to_bool (BitVec.access medeleg
        (BitVec.toNatInt
          (exceptionType_bits_forwards (ExceptionType.E_M_EnvCall ()))).toNat)) = true
  · rw [if_pos hdeleg]
    have hlt : zopz0zI_u (privLevel_to_bits Privilege.Supervisor)
        (privLevel_to_bits Privilege.Machine) = true := by
      decide
    simp only [EStateM.bind, EStateM.pure, hlt, if_true]
  · rw [if_neg hdeleg]
    have hlt : zopz0zI_u (privLevel_to_bits Privilege.Machine)
        (privLevel_to_bits Privilege.Machine) = false := by
      decide
    simp only [EStateM.bind, EStateM.pure, hlt, Bool.false_eq_true, if_false]

/-- In projected machine mode, generated Sail `execute_ECALL` produces the
machine ECALL trap and leaves state unchanged. -/
theorem execute_ECALL_machine_run
    (js : SailJoltState) (pc : BitVec 64)
    (hpc : js.sail.regs.get? Register.PC =
      some (pc : RegisterType Register.PC))
    (hpriv : js.sail.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege)) :
    (execute_ECALL ()).run (systemProject js) =
      .ok (ExecutionResult.Trap (Privilege.Machine,
        ctl_result.CTL_TRAP
          { trap := ExceptionType.E_M_EnvCall (), excinfo := none, ext := none },
        pc)) (systemProject js) := by
  have hPc := systemProject_pc_read js pc hpc
  have hPriv := systemProject_cur_privilege_read js hpriv
  unfold execute_ECALL Sail.readReg PreSail.readReg
  simp only [hPriv, hPc,
    bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]

/-- Literal callback map lookup for the generated `mstatus` CSR name. -/
theorem csr_name_map_backwards_mstatus_run (s : SailState) :
    csr_name_map_backwards "mstatus" s = .ok (0x300#12) s := by
  rfl

/-- Literal callback map lookup for the generated `mcause` CSR name. -/
theorem csr_name_map_backwards_mcause_run (s : SailState) :
    csr_name_map_backwards "mcause" s = .ok (0x342#12) s := by
  rfl

/-- Literal callback map lookup for the generated `mtval` CSR name. -/
theorem csr_name_map_backwards_mtval_run (s : SailState) :
    csr_name_map_backwards "mtval" s = .ok (0x343#12) s := by
  rfl

/-- Literal callback map lookup for the generated `mepc` CSR name. -/
theorem csr_name_map_backwards_mepc_run (s : SailState) :
    csr_name_map_backwards "mepc" s = .ok (0x341#12) s := by
  rfl

/-- The generated CSR-name write callback for `mstatus` is state-neutral. -/
theorem csr_name_write_callback_mstatus_run
    (s : SailState) (value : BitVec 64) :
    csr_name_write_callback "mstatus" value s = .ok () s := by
  unfold csr_name_write_callback csr_full_write_callback
  simp only [bind, EStateM.bind, csr_name_map_backwards_mstatus_run,
    pure, EStateM.pure]

/-- The generated CSR-name write callback for `mcause` is state-neutral. -/
theorem csr_name_write_callback_mcause_run
    (s : SailState) (value : BitVec 64) :
    csr_name_write_callback "mcause" value s = .ok () s := by
  unfold csr_name_write_callback csr_full_write_callback
  simp only [bind, EStateM.bind, csr_name_map_backwards_mcause_run,
    pure, EStateM.pure]

/-- The generated CSR-name write callback for `mtval` is state-neutral. -/
theorem csr_name_write_callback_mtval_run
    (s : SailState) (value : BitVec 64) :
    csr_name_write_callback "mtval" value s = .ok () s := by
  unfold csr_name_write_callback csr_full_write_callback
  simp only [bind, EStateM.bind, csr_name_map_backwards_mtval_run,
    pure, EStateM.pure]

/-- The generated CSR-name write callback for `mepc` is state-neutral. -/
theorem csr_name_write_callback_mepc_run
    (s : SailState) (value : BitVec 64) :
    csr_name_write_callback "mepc" value s = .ok () s := by
  unfold csr_name_write_callback csr_full_write_callback
  simp only [bind, EStateM.bind, csr_name_map_backwards_mepc_run,
    pure, EStateM.pure]

/-- The generated long-CSR callback for `mstatus` is state-neutral. -/
theorem long_csr_write_callback_mstatus_run
    (s : SailState) (value : BitVec 64) :
    long_csr_write_callback "mstatus" "mstatush" value s = .ok () s := by
  unfold long_csr_write_callback
  rw [csr_name_write_callback_mstatus_run]

/-- The generated machine trap tracker only reads the machine trap CSRs and
runs no-op callbacks, so it is state-neutral once those reads are populated. -/
theorem track_trap_machine_run
    (s : SailState) (mstatus mcause mtval mepc : BitVec 64)
    (hmstatus : s.regs.get? Register.mstatus =
      some (mstatus : RegisterType Register.mstatus))
    (hmcause : s.regs.get? Register.mcause =
      some (mcause : RegisterType Register.mcause))
    (hmtval : s.regs.get? Register.mtval =
      some (mtval : RegisterType Register.mtval))
    (hmepc : s.regs.get? Register.mepc =
      some (mepc : RegisterType Register.mepc)) :
    track_trap Privilege.Machine s = .ok () s := by
  have hReadMstatus := sail_readReg_run s Register.mstatus mstatus hmstatus
  have hReadMcause := sail_readReg_run s Register.mcause mcause hmcause
  have hReadMtval := sail_readReg_run s Register.mtval mtval hmtval
  have hReadMepc := sail_readReg_run s Register.mepc mepc hmepc
  unfold track_trap
  simp only [bind, EStateM.bind, hReadMstatus, pure, EStateM.pure]
  rw [long_csr_write_callback_mstatus_run]
  simp only [EStateM.bind, EStateM.pure]
  simp only [hReadMcause, EStateM.bind, EStateM.pure]
  rw [csr_name_write_callback_mcause_run]
  simp only [EStateM.bind, EStateM.pure]
  simp only [hReadMtval, EStateM.bind, EStateM.pure]
  rw [csr_name_write_callback_mtval_run]
  simp only [EStateM.bind, EStateM.pure]
  simp only [hReadMepc, EStateM.bind, EStateM.pure]
  rw [csr_name_write_callback_mepc_run]

/-- Machine trap-vector preparation reads projected `mtvec` and returns the
same cleared JALR target required by the ECALL assumptions. -/
theorem prepare_trap_vector_machine_ecall_run
    (js : SailJoltState)
    (hvec : tvec_addr (js.vregs JoltISA.trapHandlerVReg) ecallMachineCause =
      some (ecallTrapTarget js)) :
    prepare_trap_vector Privilege.Machine ecallMachineCause (systemProject js) =
      .ok (ecallTrapTarget js) (systemProject js) := by
  have hMtvec := systemProject_mtvec_read js
  unfold prepare_trap_vector Sail.readReg PreSail.readReg
  simp only [hMtvec, hvec,
    bind, EStateM.bind, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get]

/-- The generated machine ECALL CSR-write block inside Sail `trap_handler`.

Keeping this middle phase named lets the outer trap theorem compose small facts:
Zicfilp bookkeeping, architectural CSR writes, trap tracking, then trap-vector
selection. -/
def ecallMachineTrapCsrWrites (pc : BitVec 64) : SailM Unit := do
  Sail.writeReg Register.mcause
    (Sail.BitVec.updateSubrange (← Sail.readReg Register.mcause)
      (64 -i 1) (64 -i 1)
      (bool_to_bit
        (trapCause_is_interrupt
          (TrapCause.Exception (ExceptionType.E_M_EnvCall ())))))
  Sail.writeReg Register.mcause
    (Sail.BitVec.updateSubrange (← Sail.readReg Register.mcause)
      (64 -i 2) 0
      (zero_extend (m := (64 -i 1))
        (trapCause_bits_forwards
          (TrapCause.Exception (ExceptionType.E_M_EnvCall ())))))
  Sail.writeReg Register.mstatus
    (Sail.BitVec.updateSubrange (← Sail.readReg Register.mstatus) 7 7
      (_get_Mstatus_MIE (← Sail.readReg Register.mstatus)))
  Sail.writeReg Register.mstatus
    (Sail.BitVec.updateSubrange (← Sail.readReg Register.mstatus) 3 3 0#1)
  Sail.writeReg Register.mstatus
    (Sail.BitVec.updateSubrange (← Sail.readReg Register.mstatus) 12 11
      (privLevel_to_bits (← Sail.readReg Register.cur_privilege)))
  Sail.writeReg Register.mtval (tval none)
  Sail.writeReg Register.mepc pc
  Sail.writeReg Register.cur_privilege Privilege.Machine

/-- The generated machine ECALL branch after printing and Zicfilp bookkeeping:
write trap CSRs, run the no-op trap-extension hook, track the trap, then select
the trap vector. -/
def ecallMachineTrapBranch (pc : BitVec 64) : SailM (BitVec 64) := do
  ecallMachineTrapCsrWrites pc
  let _ : Unit := handle_trap_extension Privilege.Machine pc none
  track_trap Privilege.Machine
  prepare_trap_vector Privilege.Machine (← Sail.readReg Register.mcause)

/-- The exact generated machine-ECALL tail after the Zicfilp hook in Sail's
`trap_handler`.

This deliberately does not factor through `ecallMachineTrapCsrWrites`: the
outer trap-handler proof must match the generated Sail do-block first, then the
proof of this extracted obligation can be broken into smaller CSR/tracking/vector
lemmas. -/
def ecallMachineTrapHandlerTail (pc : BitVec 64) : SailM (BitVec 64) := do
  Sail.writeReg Register.mcause
    (Sail.BitVec.updateSubrange (← Sail.readReg Register.mcause)
      (64 -i 1) (64 -i 1)
      (bool_to_bit
        (trapCause_is_interrupt
          (TrapCause.Exception (ExceptionType.E_M_EnvCall ())))))
  Sail.writeReg Register.mcause
    (Sail.BitVec.updateSubrange (← Sail.readReg Register.mcause)
      (64 -i 2) 0
      (zero_extend (m := (64 -i 1))
        (trapCause_bits_forwards
          (TrapCause.Exception (ExceptionType.E_M_EnvCall ())))))
  Sail.writeReg Register.mstatus
    (Sail.BitVec.updateSubrange (← Sail.readReg Register.mstatus) 7 7
      (_get_Mstatus_MIE (← Sail.readReg Register.mstatus)))
  Sail.writeReg Register.mstatus
    (Sail.BitVec.updateSubrange (← Sail.readReg Register.mstatus) 3 3 0#1)
  Sail.writeReg Register.mstatus
    (Sail.BitVec.updateSubrange (← Sail.readReg Register.mstatus) 12 11
      (privLevel_to_bits (← Sail.readReg Register.cur_privilege)))
  Sail.writeReg Register.mtval (tval none)
  Sail.writeReg Register.mepc pc
  Sail.writeReg Register.cur_privilege Privilege.Machine
  track_trap Privilege.Machine
  prepare_trap_vector Privilege.Machine (← Sail.readReg Register.mcause)

/-- The four architectural trap CSR writes performed by Sail line up with
Jolt's virtual-CSR materialization after the ECALL `mstatus` row. -/
theorem systemProject_ecallAfterMstatus_trap_csrs
    (js : SailJoltState) (pc : BitVec 64) :
    systemProject (ecallAfterMstatus js pc) =
      { systemProject js with
        regs := ((((systemProject js).regs.insert Register.mcause ecallMachineCause)
          |>.insert Register.mstatus zeroOSMstatus)
          |>.insert Register.mtval (0#64))
          |>.insert Register.mepc pc } := by
  unfold systemProject
  simp only [ecallAfterMstatus_sail, ecallAfterMstatus_trapHandler,
    ecallAfterMstatus_mscratch, ecallAfterMstatus_mepc,
    ecallAfterMstatus_mcause, ecallAfterMstatus_mtval,
    ecallAfterMstatus_mstatus]
  congr 1
  apply Std.ExtDHashMap.ext_get?
  intro a
  by_cases hmepc : a = Register.mepc
  · subst a
    conv_lhs =>
      rw [extDHashMap_get?_insert_of_ne
        (written := Register.mstatus) (read := Register.mepc) (h := by decide)]
      rw [extDHashMap_get?_insert_of_ne
        (written := Register.mtval) (read := Register.mepc) (h := by decide)]
      rw [extDHashMap_get?_insert_of_ne
        (written := Register.mcause) (read := Register.mepc) (h := by decide)]
      rw [Std.ExtDHashMap.get?_insert_self]
    conv_rhs =>
      rw [Std.ExtDHashMap.get?_insert_self]
  · by_cases hmcause : a = Register.mcause
    · subst a
      conv_lhs =>
        rw [extDHashMap_get?_insert_of_ne
          (written := Register.mstatus) (read := Register.mcause) (h := by decide)]
        rw [extDHashMap_get?_insert_of_ne
          (written := Register.mtval) (read := Register.mcause) (h := by decide)]
        rw [Std.ExtDHashMap.get?_insert_self]
      conv_rhs =>
        rw [extDHashMap_get?_insert_of_ne
          (written := Register.mepc) (read := Register.mcause) (h := by decide)]
        rw [extDHashMap_get?_insert_of_ne
          (written := Register.mtval) (read := Register.mcause) (h := by decide)]
        rw [extDHashMap_get?_insert_of_ne
          (written := Register.mstatus) (read := Register.mcause) (h := by decide)]
        rw [Std.ExtDHashMap.get?_insert_self]
    · by_cases hmtval : a = Register.mtval
      · subst a
        conv_lhs =>
          rw [extDHashMap_get?_insert_of_ne
            (written := Register.mstatus) (read := Register.mtval) (h := by decide)]
          rw [Std.ExtDHashMap.get?_insert_self]
        conv_rhs =>
          rw [extDHashMap_get?_insert_of_ne
            (written := Register.mepc) (read := Register.mtval) (h := by decide)]
          rw [Std.ExtDHashMap.get?_insert_self]
      · by_cases hmstatus : a = Register.mstatus
        · subst a
          conv_lhs =>
            rw [Std.ExtDHashMap.get?_insert_self]
          conv_rhs =>
            rw [extDHashMap_get?_insert_of_ne
              (written := Register.mepc) (read := Register.mstatus) (h := by decide)]
            rw [extDHashMap_get?_insert_of_ne
              (written := Register.mtval) (read := Register.mstatus) (h := by decide)]
            rw [Std.ExtDHashMap.get?_insert_self]
        · conv_lhs =>
            rw [extDHashMap_get?_insert_of_ne
              (written := Register.mstatus) (read := a) (h := by
                intro h
                exact hmstatus h.symm)]
            rw [extDHashMap_get?_insert_of_ne
              (written := Register.mtval) (read := a) (h := by
                intro h
                exact hmtval h.symm)]
            rw [extDHashMap_get?_insert_of_ne
              (written := Register.mcause) (read := a) (h := by
                intro h
                exact hmcause h.symm)]
            rw [extDHashMap_get?_insert_of_ne
              (written := Register.mepc) (read := a) (h := by
                intro h
                exact hmepc h.symm)]
          conv_rhs =>
            rw [extDHashMap_get?_insert_of_ne
              (written := Register.mepc) (read := a) (h := by
                intro h
                exact hmepc h.symm)]
            rw [extDHashMap_get?_insert_of_ne
              (written := Register.mtval) (read := a) (h := by
                intro h
                exact hmtval h.symm)]
            rw [extDHashMap_get?_insert_of_ne
              (written := Register.mstatus) (read := a) (h := by
                intro h
                exact hmstatus h.symm)]
            rw [extDHashMap_get?_insert_of_ne
              (written := Register.mcause) (read := a) (h := by
                intro h
                exact hmcause h.symm)]
            rw [extDHashMap_get?_insert_of_ne
              (written := Register.mstatus) (read := a) (h := by
                intro h
                exact hmstatus h.symm)]
            rw [extDHashMap_get?_insert_of_ne
              (written := Register.mtval) (read := a) (h := by
                intro h
                exact hmtval h.symm)]
            rw [extDHashMap_get?_insert_of_ne
              (written := Register.mcause) (read := a) (h := by
                intro h
                exact hmcause h.symm)]
            rw [extDHashMap_get?_insert_of_ne
              (written := Register.mepc) (read := a) (h := by
                intro h
                exact hmepc h.symm)]

/-- The final generated Sail `cur_privilege := Machine` trap write is redundant
under the ECALL machine-mode assumption, even after the trap CSR writes. -/
theorem ecallTrapCsrWrites_cur_privilege_insert_eq_self
    (js : SailJoltState) (pc : BitVec 64)
    (hpriv : js.sail.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege)) :
    ((((((systemProject js).regs.insert Register.mcause ecallMachineCause).insert
          Register.mstatus zeroOSMstatus).insert Register.mtval (0#64)).insert
          Register.mepc pc).insert Register.cur_privilege Privilege.Machine) =
      (((((systemProject js).regs.insert Register.mcause ecallMachineCause).insert
          Register.mstatus zeroOSMstatus).insert Register.mtval (0#64)).insert
          Register.mepc pc) := by
  have hCurPriv := systemProject_cur_privilege_read js hpriv
  apply extDHashMap_insert_eq_self_of_get?
  rw [extDHashMap_get?_insert_of_ne (h := by decide)]
  rw [extDHashMap_get?_insert_of_ne (h := by decide)]
  rw [extDHashMap_get?_insert_of_ne (h := by decide)]
  rw [extDHashMap_get?_insert_of_ne (h := by decide)]
  exact hCurPriv

/-- The ECALL virtual-CSR rows leave the projected trap target unchanged. -/
theorem ecallTrapTarget_after_mstatus
    (js : SailJoltState) (pc : BitVec 64) :
    ecallTrapTarget (ecallAfterMstatus js pc) = ecallTrapTarget js := by
  unfold ecallTrapTarget
  rw [ecallAfterMstatus_trapHandler]

/-- The named machine ECALL CSR-write block reaches the same projected state as
Jolt's virtual CSR materialization. -/
theorem ecallMachineTrapCsrWrites_run
    (js : SailJoltState) (pc : BitVec 64)
    (hpriv : js.sail.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : sailMachineTrapMstatus (js.vregs JoltISA.mstatusVReg) =
      zeroOSMstatus) :
    (ecallMachineTrapCsrWrites pc).run (systemProject js) =
      .ok () (systemProject (ecallAfterMstatus js pc)) := by
  have hMcause := systemProject_mcause_read js
  have hMstatus := systemProject_mstatus_read js
  have hCurPriv := systemProject_cur_privilege_read js hpriv
  have hTrapShape := systemProject_ecallAfterMstatus_trap_csrs js pc
  have hMcauseSelf : (Register.mcause == Register.mcause) = true := by
    decide
  have hMstatusSelf : (Register.mstatus == Register.mstatus) = true := by
    decide
  have hMcauseMstatus : (Register.mcause == Register.mstatus) = false := by
    decide
  have hMstatusCurPriv : (Register.mstatus == Register.cur_privilege) = false := by
    decide
  have hMcauseCurPriv : (Register.mcause == Register.cur_privilege) = false := by
    decide
  unfold ecallMachineTrapCsrWrites
  unfold Sail.readReg PreSail.readReg Sail.writeReg PreSail.writeReg
  simp only [hMcause, hMstatus, hCurPriv, hmstatus,
    ecall_mcause_machine_write_value, Std.ExtDHashMap.get?_insert,
    Std.ExtDHashMap.get?_insert_self, hMcauseSelf, hMstatusSelf,
    hMcauseMstatus, hMstatusCurPriv, hMcauseCurPriv,
    Bool.false_eq_true, cast_eq, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  repeat first
    | rw [dif_pos (by trivial)]
    | rw [dif_neg (by intro h; cases h)]
  simp only [hMcause, hMstatus, hCurPriv, hmstatus,
    ecall_mcause_machine_write_value, Std.ExtDHashMap.get?_insert,
    Std.ExtDHashMap.get?_insert_self, hMcauseSelf, hMstatusSelf,
    hMcauseMstatus, hMstatusCurPriv, hMcauseCurPriv,
    Bool.false_eq_true, cast_eq, bind, EStateM.bind, pure, EStateM.pure]
  repeat first
    | rw [dif_pos (by trivial)]
    | rw [dif_neg (by intro h; cases h)]
  simp only [hMcause, hMstatus, hCurPriv, hmstatus,
    ecall_mcause_machine_write_value, Std.ExtDHashMap.get?_insert,
    Std.ExtDHashMap.get?_insert_self, hMcauseSelf, hMstatusSelf,
    hMcauseMstatus, hMstatusCurPriv, hMcauseCurPriv,
    Bool.false_eq_true, cast_eq, bind, EStateM.bind, pure, EStateM.pure]
  repeat first
    | rw [dif_pos (by trivial)]
    | rw [dif_neg (by intro h; cases h)]
  simp only [hMcause, hMstatus, hCurPriv, hmstatus,
    ecall_mcause_machine_write_value, Std.ExtDHashMap.get?_insert,
    Std.ExtDHashMap.get?_insert_self, hMcauseSelf, hMstatusSelf,
    hMcauseMstatus, hMstatusCurPriv, hMcauseCurPriv,
    Bool.false_eq_true, cast_eq, bind, EStateM.bind, pure, EStateM.pure]
  repeat first
    | rw [dif_pos (by trivial)]
    | rw [dif_neg (by intro h; cases h)]
  simp only [hMcause, hMstatus, hCurPriv, hmstatus,
    ecall_mcause_machine_write_value, Std.ExtDHashMap.get?_insert,
    Std.ExtDHashMap.get?_insert_self, hMcauseSelf, hMstatusSelf,
    hMcauseMstatus, hMstatusCurPriv, hMcauseCurPriv,
    Bool.false_eq_true, cast_eq, bind, EStateM.bind, pure, EStateM.pure]
  repeat first
    | rw [dif_pos (by trivial)]
    | rw [dif_neg (by intro h; cases h)]
  simp only [hMcause, hMstatus, hCurPriv, hmstatus,
    ecall_mcause_machine_write_value, Std.ExtDHashMap.get?_insert,
    Std.ExtDHashMap.get?_insert_self, hMcauseSelf, hMstatusSelf,
    hMcauseMstatus, hMstatusCurPriv, hMcauseCurPriv,
    Bool.false_eq_true, cast_eq, bind, EStateM.bind, pure, EStateM.pure]
  repeat first
    | rw [dif_pos (by trivial)]
    | rw [dif_neg (by intro h; cases h)]
  simp only [hMcause, hMstatus, hCurPriv, hmstatus,
    ecall_mcause_machine_write_value, Std.ExtDHashMap.get?_insert,
    Std.ExtDHashMap.get?_insert_self, hMcauseSelf, hMstatusSelf,
    hMcauseMstatus, hMstatusCurPriv, hMcauseCurPriv,
    Bool.false_eq_true, cast_eq, bind, EStateM.bind, pure, EStateM.pure]
  repeat first
    | rw [dif_pos (by trivial)]
    | rw [dif_neg (by intro h; cases h)]
  rw [extDHashMap_insert_insert_same]
  rw [extDHashMap_insert_insert_same]
  rw [extDHashMap_insert_insert_same]
  unfold sailMachineTrapMstatus at hmstatus
  rw [hmstatus]
  rw [ecall_tval_none]
  rw [ecallTrapCsrWrites_cur_privilege_insert_eq_self js pc hpriv]
  rw [← hTrapShape]

/-- After the machine ECALL CSR writes, generated trap tracking is state-neutral
and trap-vector selection returns the same target as Jolt's final `JALR`. -/
theorem ecallMachineTrapBranch_run
    (js : SailJoltState) (pc : BitVec 64)
    (hpriv : js.sail.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : sailMachineTrapMstatus (js.vregs JoltISA.mstatusVReg) =
      zeroOSMstatus)
    (hvec : tvec_addr (js.vregs JoltISA.trapHandlerVReg) ecallMachineCause =
      some (ecallTrapTarget js)) :
    (ecallMachineTrapBranch pc).run (systemProject js) =
      .ok (ecallTrapTarget js) (systemProject (ecallAfterMstatus js pc)) := by
  have hCsr := ecallMachineTrapCsrWrites_run js pc hpriv hmstatus
  change ecallMachineTrapCsrWrites pc (systemProject js) =
    .ok () (systemProject (ecallAfterMstatus js pc)) at hCsr
  have hMstatusFinal :
      (systemProject (ecallAfterMstatus js pc)).regs.get? Register.mstatus =
        some (zeroOSMstatus : RegisterType Register.mstatus) := by
    rw [systemProject_mstatus_read]
    rw [ecallAfterMstatus_mstatus]
  have hMcauseFinal :
      (systemProject (ecallAfterMstatus js pc)).regs.get? Register.mcause =
        some (ecallMachineCause : RegisterType Register.mcause) := by
    rw [systemProject_mcause_read]
    rw [ecallAfterMstatus_mcause]
  have hMtvalFinal :
      (systemProject (ecallAfterMstatus js pc)).regs.get? Register.mtval =
        some (0#64 : RegisterType Register.mtval) := by
    rw [systemProject_mtval_read]
    rw [ecallAfterMstatus_mtval]
  have hMepcFinal :
      (systemProject (ecallAfterMstatus js pc)).regs.get? Register.mepc =
        some (pc : RegisterType Register.mepc) := by
    rw [systemProject_mepc_read]
    rw [ecallAfterMstatus_mepc]
  have hTrack := track_trap_machine_run
    (systemProject (ecallAfterMstatus js pc))
    zeroOSMstatus ecallMachineCause (0#64) pc
    hMstatusFinal hMcauseFinal hMtvalFinal hMepcFinal
  have hReadMcause := sail_readReg_run
    (systemProject (ecallAfterMstatus js pc))
    Register.mcause ecallMachineCause hMcauseFinal
  have hvecAfter :
      tvec_addr ((ecallAfterMstatus js pc).vregs JoltISA.trapHandlerVReg)
          ecallMachineCause =
        some (ecallTrapTarget (ecallAfterMstatus js pc)) := by
    rw [ecallAfterMstatus_trapHandler]
    rw [ecallTrapTarget_after_mstatus]
    exact hvec
  have hPrepare := prepare_trap_vector_machine_ecall_run
    (ecallAfterMstatus js pc) hvecAfter
  unfold ecallMachineTrapBranch
  simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure]
  rw [hCsr]
  simp only
  rw [hTrack]
  simp only
  rw [hReadMcause]
  simp only
  rw [hPrepare]
  rw [ecallTrapTarget_after_mstatus]

/-- Extracted obligation from the generated Sail `trap_handler` after the
Zicfilp hook.

This is the proof boundary the outer ECALL theorem should use. Its left-hand
side is intentionally the generated trap-handler tail, not the cleaner
`ecallMachineTrapBranch` phase. -/
theorem ecallMachineTrapHandlerTail_run
    (js : SailJoltState) (pc : BitVec 64)
    (hpriv : js.sail.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : sailMachineTrapMstatus (js.vregs JoltISA.mstatusVReg) =
      zeroOSMstatus)
    (hvec : tvec_addr (js.vregs JoltISA.trapHandlerVReg) ecallMachineCause =
      some (ecallTrapTarget js)) :
    (ecallMachineTrapHandlerTail pc).run (systemProject js) =
      .ok (ecallTrapTarget js) (systemProject (ecallAfterMstatus js pc)) := by
  have hBridge :
      ecallMachineTrapHandlerTail pc =
        (do
          ecallMachineTrapCsrWrites pc
          track_trap Privilege.Machine
          prepare_trap_vector Privilege.Machine (← Sail.readReg Register.mcause)) := by
    unfold ecallMachineTrapHandlerTail ecallMachineTrapCsrWrites
    simp only [bind_assoc]
  rw [hBridge]
  have hCsr := ecallMachineTrapCsrWrites_run js pc hpriv hmstatus
  change ecallMachineTrapCsrWrites pc (systemProject js) =
    .ok () (systemProject (ecallAfterMstatus js pc)) at hCsr
  have hMstatusFinal :
      (systemProject (ecallAfterMstatus js pc)).regs.get? Register.mstatus =
        some (zeroOSMstatus : RegisterType Register.mstatus) := by
    rw [systemProject_mstatus_read]
    rw [ecallAfterMstatus_mstatus]
  have hMcauseFinal :
      (systemProject (ecallAfterMstatus js pc)).regs.get? Register.mcause =
        some (ecallMachineCause : RegisterType Register.mcause) := by
    rw [systemProject_mcause_read]
    rw [ecallAfterMstatus_mcause]
  have hMtvalFinal :
      (systemProject (ecallAfterMstatus js pc)).regs.get? Register.mtval =
        some (0#64 : RegisterType Register.mtval) := by
    rw [systemProject_mtval_read]
    rw [ecallAfterMstatus_mtval]
  have hMepcFinal :
      (systemProject (ecallAfterMstatus js pc)).regs.get? Register.mepc =
        some (pc : RegisterType Register.mepc) := by
    rw [systemProject_mepc_read]
    rw [ecallAfterMstatus_mepc]
  have hTrack := track_trap_machine_run
    (systemProject (ecallAfterMstatus js pc))
    zeroOSMstatus ecallMachineCause (0#64) pc
    hMstatusFinal hMcauseFinal hMtvalFinal hMepcFinal
  have hReadMcause := sail_readReg_run
    (systemProject (ecallAfterMstatus js pc))
    Register.mcause ecallMachineCause hMcauseFinal
  have hvecAfter :
      tvec_addr ((ecallAfterMstatus js pc).vregs JoltISA.trapHandlerVReg)
          ecallMachineCause =
        some (ecallTrapTarget (ecallAfterMstatus js pc)) := by
    rw [ecallAfterMstatus_trapHandler]
    rw [ecallTrapTarget_after_mstatus]
    exact hvec
  have hPrepare := prepare_trap_vector_machine_ecall_run
    (ecallAfterMstatus js pc) hvecAfter
  simp only [bind, EStateM.bind, EStateM.run]
  rw [hCsr]
  simp only
  rw [hTrack]
  simp only
  rw [hReadMcause]
  simp only
  rw [hPrepare]
  rw [ecallTrapTarget_after_mstatus]

/-- Sail's machine trap handler for ECALL reaches the projected Jolt ECALL trap
state and returns the same trap target used by the final Jolt `JALR`. -/
theorem trap_handler_machine_ecall_run
    (js : SailJoltState) (pc : BitVec 64)
    (help : js.sail.regs.get? Register.elp =
      some (0#1 : RegisterType Register.elp))
    (hpriv : js.sail.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : sailMachineTrapMstatus (js.vregs JoltISA.mstatusVReg) =
      zeroOSMstatus)
    (hvec : tvec_addr (js.vregs JoltISA.trapHandlerVReg) ecallMachineCause =
      some (ecallTrapTarget js)) :
    trap_handler Privilege.Machine
        (TrapCause.Exception (ExceptionType.E_M_EnvCall ())) pc none none
    (systemProject js) =
      .ok (ecallTrapTarget js) (systemProject (ecallAfterMstatus js pc)) := by
  have hZicfilp := zicfilp_preserve_elp_machine_ecall_run js help hmstatus
  have hTail := ecallMachineTrapHandlerTail_run js pc hpriv hmstatus hvec
  have hZicfilpSupport : hartSupports extension.Ext_Zicfilp = true := by
    rw [hartSupports]
  have hPrintException : get_config_print_exception () = false := rfl
  have hPrintInterrupt : get_config_print_interrupt () = false := rfl
  unfold trap_handler
  simp only [hPrintException, hPrintInterrupt, Bool.false_or, Bool.false_eq_true,
    if_false, hZicfilpSupport, if_true, bind, EStateM.bind, EStateM.run,
    pure, EStateM.pure, hZicfilp]
  change (ecallMachineTrapHandlerTail pc).run (systemProject js) =
    .ok (ecallTrapTarget js) (systemProject (ecallAfterMstatus js pc))
  exact hTail

/-- Sail's generated `exception_handler` for a machine-mode ECALL delegates to
the machine trap handler and reaches the projected Jolt trap state. -/
theorem exception_handler_machine_ecall_run
    (js : SailJoltState) (pc medeleg misa : BitVec 64)
    (hmedeleg : js.sail.regs.get? Register.medeleg =
      some (medeleg : RegisterType Register.medeleg))
    (hmisa : js.sail.regs.get? Register.misa =
      some (misa : RegisterType Register.misa))
    (help : js.sail.regs.get? Register.elp =
      some (0#1 : RegisterType Register.elp))
    (hpriv : js.sail.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : sailMachineTrapMstatus (js.vregs JoltISA.mstatusVReg) =
      zeroOSMstatus)
    (hvec : tvec_addr (js.vregs JoltISA.trapHandlerVReg) ecallMachineCause =
      some (ecallTrapTarget js)) :
    exception_handler Privilege.Machine
        (ctl_result.CTL_TRAP
          { trap := ExceptionType.E_M_EnvCall (), excinfo := none, ext := none })
        pc
    (systemProject js) =
      .ok (ecallTrapTarget js) (systemProject (ecallAfterMstatus js pc)) := by
  have hMedeleg := systemProject_medeleg_read js medeleg hmedeleg
  have hMisa := systemProject_misa_read js misa hmisa
  have hDelegate :=
    exception_delegatee_machine_ecall_run (systemProject js) medeleg misa
      hMedeleg hMisa
  have hTrap :=
    trap_handler_machine_ecall_run js pc help hpriv hmstatus hvec
  have hPrintException : get_config_print_exception () = false := rfl
  unfold exception_handler
  simp only [hDelegate, hPrintException, Bool.false_eq_true, if_false,
    bind, EStateM.bind, pure, EStateM.pure, hTrap]

/-- Sail's trap postlude for a single instruction result.

Raw `execute_ECALL` only returns a `Trap`. The generated Sail step function then
routes that trap through `exception_handler` and writes `nextPC` with
`set_next_pc`. ECALL equivalence must target this postlude, not raw
`execute_ECALL`. -/
def sailTrapPostlude (result : ExecutionResult) : SailM ExecutionResult := do
  match result with
  | .Trap (priv, ctl, pc) =>
      set_next_pc (← exception_handler priv ctl pc)
      pure RETIRE_SUCCESS
  | other => pure other

/-- Sail ECALL followed by the generated trap postlude. -/
def sailEcallTrapEntry : SailM ExecutionResult := do
  let result ← execute_ECALL ()
  sailTrapPostlude result

/-- Sail ECALL followed by the generated trap postlude reaches the same
projected final state as the Rust-faithful Jolt ECALL program. -/
theorem sailEcallTrapEntry_machine_run
    (js : SailJoltState) (pc nextPC medeleg misa : BitVec 64)
    (hpc : js.sail.regs.get? Register.PC =
      some (pc : RegisterType Register.PC))
    (hmedeleg : js.sail.regs.get? Register.medeleg =
      some (medeleg : RegisterType Register.medeleg))
    (hmisa : js.sail.regs.get? Register.misa =
      some (misa : RegisterType Register.misa))
    (help : js.sail.regs.get? Register.elp =
      some (0#1 : RegisterType Register.elp))
    (hpriv : js.sail.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : sailMachineTrapMstatus (js.vregs JoltISA.mstatusVReg) =
      zeroOSMstatus)
    (hvec : tvec_addr (js.vregs JoltISA.trapHandlerVReg) ecallMachineCause =
      some (ecallTrapTarget js)) :
    sailEcallTrapEntry.run (systemProject js) =
      .ok RETIRE_SUCCESS (systemProject (ecallJoltFinal js pc nextPC)) := by
  have hExecute := execute_ECALL_machine_run js pc hpc hpriv
  have hException :=
    exception_handler_machine_ecall_run js pc medeleg misa hmedeleg hmisa help
      hpriv hmstatus hvec
  have hSetNext :=
    set_next_pc_systemProject_run (ecallAfterMstatus js pc)
      (ecallTrapTarget js)
  have hFinal := systemProject_ecallJoltFinal_setNext js pc nextPC
  change (execute_ECALL ()) (systemProject js) =
    .ok (ExecutionResult.Trap (Privilege.Machine,
      ctl_result.CTL_TRAP
        { trap := ExceptionType.E_M_EnvCall (), excinfo := none, ext := none },
      pc)) (systemProject js) at hExecute
  change (set_next_pc (ecallTrapTarget js))
      (systemProject (ecallAfterMstatus js pc)) =
    .ok ()
      (systemProject
        { ecallAfterMstatus js pc with
          sail := setNextPCState (ecallAfterMstatus js pc).sail
            (ecallTrapTarget js) }) at hSetNext
  unfold sailEcallTrapEntry sailTrapPostlude
  unfold EStateM.run
  simp only [bind, EStateM.bind]
  rw [hExecute]
  simp only [bind, EStateM.bind]
  rw [hException]
  simp only [bind, EStateM.bind]
  rw [hSetNext]
  simp only [pure, EStateM.pure]
  rw [← hFinal]

end System

end
