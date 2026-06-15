import JoltBytecode.Bundles

/-!
# Derived facts from top-level assumptions

This file proves consequences of the primitive assumptions in
`JoltBytecode.Assumptions`. Nothing here is assumed.
-/

set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

theorem readReg_eq_of_get? (r : Register) (s : SailState) (v : RegisterType r)
    (h : s.regs.get? r = some v) :
    (Sail.readReg r : SailM (RegisterType r)) s = .ok v s := by
  unfold Sail.readReg PreSail.readReg
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             MonadStateOf.get, EStateM.get, getThe, get, h]

/-- Under Jolt's M-mode/MPRV=0 execution assumptions, a normal data-load
    address translation is the bare identity translation. -/
theorem translateAddr_load_data_of_joltConfig
    (addr : BitVec 64) (s : SailState) (hcfg : JoltConfig s) :
    translateAddr (Virtaddr addr) (Load Data) s =
      .ok (Ok (physaddr.Physaddr addr, init_ext_ptw)) s := by
  obtain ⟨mval, hmstatus, hmprv⟩ := hcfg.mstatus_mprv.value
  have h_ms_read := readReg_eq_of_get? Register.mstatus s mval hmstatus
  have h_priv := readReg_eq_of_get? Register.cur_privilege s Privilege.Machine
    hcfg.cur_privilege.value
  unfold translateAddr SailME.run PreSail.PreSailME.run
  simp (config := { decide := true }) [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
        ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
        ExceptT.pure, ExceptT.lift,
        MonadLift.monadLift, liftM, monadLift, Functor.map,
        effectivePrivilege, translationMode, is_shadow_stack_access,
        h_ms_read, h_priv, hmprv,
        bits_of_virtaddr, BEq.beq]
  rfl

/-- Under Jolt's M-mode/MPRV=0 execution assumptions, a normal data-store
    address translation is the bare identity translation. -/
theorem translateAddr_store_data_of_joltConfig
    (addr : BitVec 64) (s : SailState) (hcfg : JoltConfig s) :
    translateAddr (Virtaddr addr) (Store Data) s =
      .ok (Ok (physaddr.Physaddr addr, init_ext_ptw)) s := by
  obtain ⟨mval, hmstatus, hmprv⟩ := hcfg.mstatus_mprv.value
  have h_ms_read := readReg_eq_of_get? Register.mstatus s mval hmstatus
  have h_priv := readReg_eq_of_get? Register.cur_privilege s Privilege.Machine
    hcfg.cur_privilege.value
  unfold translateAddr SailME.run PreSail.PreSailME.run
  simp (config := { decide := true }) [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
        ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
        ExceptT.pure, ExceptT.lift,
        MonadLift.monadLift, liftM, monadLift, Functor.map,
        effectivePrivilege, translationMode, is_shadow_stack_access,
        h_ms_read, h_priv, hmprv,
        bits_of_virtaddr, BEq.beq]
  rfl

/-- Under Jolt's M-mode/MPRV=0 execution assumptions, a data AMO address
    translation is the bare identity translation. -/
theorem translateAddr_atomic_data_of_joltConfig
    (op : amoop) (addr : BitVec 64) (s : SailState) (hcfg : JoltConfig s) :
    translateAddr (Virtaddr addr) (Atomic (op, Data, Data)) s =
      .ok (Ok (physaddr.Physaddr addr, init_ext_ptw)) s := by
  obtain ⟨mval, hmstatus, hmprv⟩ := hcfg.mstatus_mprv.value
  have h_ms_read := readReg_eq_of_get? Register.mstatus s mval hmstatus
  have h_priv := readReg_eq_of_get? Register.cur_privilege s Privilege.Machine
    hcfg.cur_privilege.value
  unfold translateAddr SailME.run PreSail.PreSailME.run
  simp (config := { decide := true }) [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
        ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
        ExceptT.pure, ExceptT.lift,
        MonadLift.monadLift, liftM, monadLift, Functor.map,
        effectivePrivilege, translationMode, is_shadow_stack_access,
        h_ms_read, h_priv, hmprv,
        bits_of_virtaddr, BEq.beq]
  rfl

end
