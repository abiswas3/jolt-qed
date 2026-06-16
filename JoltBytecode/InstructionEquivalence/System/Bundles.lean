import JoltBytecode.InstructionEquivalence.System.Common

/-!
# System proof bundles

These bundles are the public assumption interface for ECALL, MRET, and CSRRW.
They only compose primitive assumptions from `JoltBytecode.Assumptions`; they do
not introduce derived facts or hide proof obligations in helper structures.

The CSR read/write matching fields are still deliberate W10 debt, but not
layout debt. The vreg-to-Sail-register/vreg-to-CSR-address map is Jolt ISA
definition in `JoltBytecode.JoltISA.VirtualRegisters` and reduces by `rfl`;
these fields are only about generated Sail accessor/legalizer behavior.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace System

/-- Public assumptions for ECALL trap-entry equivalence.

The first group is ordinary generated-Sail register availability. The final
group is the current ZeroOS trap envelope: Sail's machine-trap `mstatus` update
must equal Jolt's fixed virtual-register write, Sail's `tvec_addr` helper must
choose Jolt's `JALR` target, and that target must satisfy the fetch-alignment
check used by both paths. -/
structure EcallSystemAssumptions (js : SailJoltState) : Prop where
  pc_readable : Assumptions.SailRegReadable Register.PC js.sail
  nextPC_readable : Assumptions.SailRegReadable Register.nextPC js.sail
  -- Jolt source: `tracer/src/emulator/cpu.rs:332`
  -- `privilege_mode: PrivilegeMode::Machine,`
  cur_privilege_machine : Assumptions.CurPrivilegeMachine js.sail
  medeleg_readable : Assumptions.SailRegReadable Register.medeleg js.sail
  misa_readable : Assumptions.SailRegReadable Register.misa js.sail
  -- WARNING: (sail) Sail's trap path may read `elp` through Zicfilp:
  -- `LeanRV64D/ZicfilpRegs.lean:254-257`.
  -- No matching Rust/tracer source was found for this ELP state.
  elp_zero :
    js.sail.regs.get? Register.elp =
      some (0#1 : RegisterType Register.elp)
  -- Sail side: `LeanRV64D/SysControl.lean:611-615` updates `mstatus`
  -- on Machine trap entry.
  -- Jolt side: `crates/jolt-program/src/expand/control_flow/ecall.rs:43-51`
  -- writes `3 << 11`, i.e. `zeroOSMstatus`.
  mstatus_matches_zeroOS_trap :
    Assumptions.MachineTrapMstatusMatches
      (js.vregs JoltISA.mstatusVReg) zeroOSMstatus
  -- Sail side: `LeanRV64D/SysExceptions.lean:209-222` calls `tvec_addr`;
  -- `LeanRV64D/SysRegs.lean:1251-1259` defines the address calculation.
  -- Jolt side: `crates/jolt-program/src/expand/control_flow/ecall.rs:54-62`
  -- emits `JALR ... reg(v_trap_handler_reg), 0`.
  trap_vector_matches_jalr :
    Assumptions.TrapVectorTargetMatches
      (js.vregs JoltISA.trapHandlerVReg) ecallMachineCause (ecallTrapTarget js)
  -- WARNING: (sail) This is the generated-Sail fetch-alignment side condition
  -- used by the proof. No Rust/tracer source was found that states it directly.
  trap_target_fetch_aligned :
    Assumptions.FetchTargetAligned (ecallTrapTarget js)

/-- Public assumptions for MRET equivalence.

The readable-register fields cover the generated Sail control-flow and Zicfilp
reads. The four `mstatus` fields are the current machine-only ZeroOS envelope
under which Sail's architectural MRET postlude is idempotent; these are W10
debt until proved from a sharper system contract. -/
structure MretSystemAssumptions (js : SailJoltState) : Prop where
  pc_readable : Assumptions.SailRegReadable Register.PC js.sail
  nextPC_readable : Assumptions.SailRegReadable Register.nextPC js.sail
  misa_user_disabled : Assumptions.MisaUserDisabled js.sail
  mseccfg_readable : Assumptions.SailRegReadable Register.mseccfg js.sail
  elp_zero :
    js.sail.regs.get? Register.elp =
      some (0#1 : RegisterType Register.elp)
  cur_privilege_machine : Assumptions.CurPrivilegeMachine js.sail
  mstatus_mie_matches_mpie :
    Assumptions.MstatusMieMatchesMpie (js.vregs JoltISA.mstatusVReg)
  mstatus_mpie_one :
    Assumptions.MstatusMpieOne (js.vregs JoltISA.mstatusVReg)
  mstatus_mpp_machine :
    Assumptions.MstatusMppMachine (js.vregs JoltISA.mstatusVReg)
  mstatus_mpelp_zero :
    Assumptions.MstatusMpelpZero (js.vregs JoltISA.mstatusVReg)
  return_target_fetch_aligned :
    Assumptions.FetchTargetAligned (mretReturnTarget js)

/-- If the linked CSR virtual registers agree with the generated Sail CSR
registers, materializing those virtual registers is the same state as the plain
projection. This is the global linked-register invariant made explicit. -/
theorem systemProject_eq_project_of_compatible
    (js : SailJoltState)
    (h :
      Assumptions.MstatusVRegMatchesSail js ∧
      Assumptions.MtvecVRegMatchesSail js ∧
      Assumptions.MscratchVRegMatchesSail js ∧
      Assumptions.MepcVRegMatchesSail js ∧
      Assumptions.McauseVRegMatchesSail js ∧
      Assumptions.MtvalVRegMatchesSail js) :
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

/-- Public assumptions for CSRRW equivalence over the supported System CSR
whitelist.

This bundle keeps only the real public inputs: the source register value, the
machine-mode execution envelope, and the decoded six-CSR whitelist carried by
`csr : JoltISA.SystemCSR`. Register non-aliasing, CSR permission checks,
callback neutrality, and projected `rd` writeback are derived in the CSRRW proof
file. -/
structure CsrrwSystemAssumptions
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rs1 rd : regidx) :
    Type where
  rs1_val : BitVec 64
  source_read : rX_bits rs1 js.sail = .ok rs1_val js.sail
  cur_privilege_machine : Assumptions.CurPrivilegeMachine js.sail
  linked_csrs :
    Assumptions.MstatusVRegMatchesSail js ∧
    Assumptions.MtvecVRegMatchesSail js ∧
    Assumptions.MscratchVRegMatchesSail js ∧
    Assumptions.MepcVRegMatchesSail js ∧
    Assumptions.McauseVRegMatchesSail js ∧
    Assumptions.MtvalVRegMatchesSail js

end System

end
