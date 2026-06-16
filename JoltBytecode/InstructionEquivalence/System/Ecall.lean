import JoltBytecode.InstructionEquivalence.System.Bundles

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace System

/-!
# ECALL system expansion

The Rust expansion writes the machine-mode trap fields into reserved virtual
registers and jumps to the virtual `mtvec` register.

The theorem below deliberately does not compare against raw `execute_ECALL`.
Raw Sail ECALL returns a `Trap`; the generated Sail step postlude then calls
`exception_handler` and `set_next_pc`. Jolt's inline sequence has already
materialized the trap entry, so the correct target is `sailEcallTrapEntry`
under `systemProject`.
-/

/-- Concrete ECALL row 0: `AUIPC ecall_addr, 0` stores the current PC in v40. -/
theorem ecall_auipc_run
    (js : SailJoltState) (pc : BitVec 64)
    (hpc : js.sail.regs.get? Register.PC =
      some (pc : RegisterType Register.PC)) :
    (JoltISA.execInstr
      (.AUIPC (.vreg JoltISA.systemScratchVReg) (0 : BitVec 20))).run js =
      .ok RETIRE_SUCCESS (ecallAfterAuipc js pc) := by
  unfold JoltISA.execInstr JoltISA.writeDst writeVReg liftSail
  unfold get_arch_pc Sail.readReg PreSail.readReg
  unfold ecallAfterAuipc joltSetVReg vregWrite
  simp only [hpc, auipc_zero_offset,
    bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- Concrete ECALL row 1: copy v40 into virtual `mepc`. -/
theorem ecall_mepc_run
    (js : SailJoltState) (pc : BitVec 64) :
    (JoltISA.execInstr
      (.ADDI (.vreg JoltISA.mepcVReg) (.vreg JoltISA.systemScratchVReg)
        (0 : BitVec 12))).run (ecallAfterAuipc js pc) =
      .ok RETIRE_SUCCESS (ecallAfterMepc js pc) := by
  unfold JoltISA.execInstr JoltISA.readSrc JoltISA.writeDst
  unfold readVReg writeVReg ecallAfterMepc ecallAfterAuipc
  unfold joltSetVReg vregWrite
  simp only [if_true, addi_zero_value,
    bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- Concrete ECALL row 2: write machine-mode ECALL cause to virtual `mcause`. -/
theorem ecall_mcause_run
    (js : SailJoltState) (pc : BitVec 64) :
    (JoltISA.execInstr
      (.ADDI (.vreg JoltISA.mcauseVReg) (.xreg (regidx.Regidx 0))
        (11 : BitVec 12))).run (ecallAfterMepc js pc) =
      .ok RETIRE_SUCCESS (ecallAfterMcause js pc) := by
  unfold JoltISA.execInstr JoltISA.readSrc JoltISA.writeDst liftSail writeVReg
  unfold ecallAfterMcause joltSetVReg vregWrite
  simp only [rX_bits_regidx_zero, addi_ecall_machine_cause_value,
    bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- Concrete ECALL row 3: write zero to virtual `mtval`. -/
theorem ecall_mtval_run
    (js : SailJoltState) (pc : BitVec 64) :
    (JoltISA.execInstr
      (.ADDI (.vreg JoltISA.mtvalVReg) (.xreg (regidx.Regidx 0))
        (0 : BitVec 12))).run (ecallAfterMcause js pc) =
      .ok RETIRE_SUCCESS (ecallAfterMtval js pc) := by
  unfold JoltISA.execInstr JoltISA.readSrc JoltISA.writeDst liftSail writeVReg
  unfold ecallAfterMtval joltSetVReg vregWrite
  simp only [rX_bits_regidx_zero, addi_zero_value,
    bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- Concrete ECALL row 4: reuse v40 for the literal value three. -/
theorem ecall_three_run
    (js : SailJoltState) (pc : BitVec 64) :
    (JoltISA.execInstr
      (.ADDI (.vreg JoltISA.systemScratchVReg) (.xreg (regidx.Regidx 0))
        (3 : BitVec 12))).run (ecallAfterMtval js pc) =
      .ok RETIRE_SUCCESS (ecallAfterThree js pc) := by
  unfold JoltISA.execInstr JoltISA.readSrc JoltISA.writeDst liftSail writeVReg
  unfold ecallAfterThree joltSetVReg vregWrite
  simp only [rX_bits_regidx_zero, addi_three_value,
    bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- Concrete ECALL row 5: lowered `SLLI mstatus, three, 11`. -/
theorem ecall_mstatus_run
    (js : SailJoltState) (pc : BitVec 64) :
    (JoltISA.execInstr
      (.VirtualMULI (.vreg JoltISA.mstatusVReg)
        (.vreg JoltISA.systemScratchVReg) (2048 : BitVec 64))).run
        (ecallAfterThree js pc) =
      .ok RETIRE_SUCCESS (ecallAfterMstatus js pc) := by
  unfold JoltISA.execInstr JoltISA.readSrc JoltISA.writeDst
  unfold readVReg writeVReg ecallAfterMstatus ecallAfterThree
  unfold joltSetVReg vregWrite
  simp only [if_true,
    bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  have hmuli :
      jolt_virtual_muli_value (3#64) (2048 : BitVec 64) = zeroOSMstatus :=
    virtualMuli_three_to_zeroOS
  rw [hmuli]

/-- Concrete ECALL row 6: jump through virtual `mtvec` and discard the link in
the scratch register. -/
theorem ecall_jalr_run
    (js : SailJoltState) (pc nextPC misa : BitVec 64)
    (hnextPC : js.sail.regs.get? Register.nextPC =
      some (nextPC : RegisterType Register.nextPC))
    (hmisa : js.sail.regs.get? Register.misa =
      some (misa : RegisterType Register.misa))
    (hfetch : BitVec.access (ecallTrapTarget js) 1 = 0#1) :
    (JoltISA.execInstr
      (.JALR (.vreg JoltISA.systemScratchVReg)
        (.vreg JoltISA.trapHandlerVReg) (0 : BitVec 12))).run
        (ecallAfterMstatus js pc) =
      .ok RETIRE_SUCCESS (ecallAfterJalr js pc nextPC) := by
  have hJump := jump_to_ecallTrapTarget_run js misa hmisa hfetch
  rw [RETIRE_SUCCESS] at hJump
  unfold JoltISA.execInstr JoltISA.readSrc JoltISA.writeDst readVReg writeVReg
  unfold liftSail get_next_pc
  unfold Sail.readReg PreSail.readReg
  unfold ecallAfterJalr setNextPCState joltSetVReg vregWrite
  unfold RETIRE_SUCCESS
  simp only [ecallAfterMstatus_sail, hnextPC, hJump, ecallAfterMstatus_trapHandler,
    ecallJalrTarget_zero_imm, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  unfold setNextPCState
  rfl

/-- The full Rust-faithful ECALL Jolt program reaches the concrete final Jolt
state described by the row lemmas. -/
theorem ecallProgram_run
    (js : SailJoltState) (pc nextPC misa : BitVec 64)
    (hpc : js.sail.regs.get? Register.PC =
      some (pc : RegisterType Register.PC))
    (hnextPC : js.sail.regs.get? Register.nextPC =
      some (nextPC : RegisterType Register.nextPC))
    (hmisa : js.sail.regs.get? Register.misa =
      some (misa : RegisterType Register.misa))
    (hfetch : BitVec.access (ecallTrapTarget js) 1 = 0#1) :
    (JoltISA.execProgram JoltISA.ecallProgram).run js =
      .ok RETIRE_SUCCESS (ecallJoltFinal js pc nextPC) := by
  unfold JoltISA.ecallProgram ecallJoltFinal
  rw [JoltISA.execProgram_instr_run_retire _ _ js (ecallAfterAuipc js pc)
    (ecall_auipc_run js pc hpc)]
  rw [JoltISA.execProgram_instr_run_retire _ _ (ecallAfterAuipc js pc)
    (ecallAfterMepc js pc) (ecall_mepc_run js pc)]
  rw [JoltISA.execProgram_instr_run_retire _ _ (ecallAfterMepc js pc)
    (ecallAfterMcause js pc) (ecall_mcause_run js pc)]
  rw [JoltISA.execProgram_instr_run_retire _ _ (ecallAfterMcause js pc)
    (ecallAfterMtval js pc) (ecall_mtval_run js pc)]
  rw [JoltISA.execProgram_instr_run_retire _ _ (ecallAfterMtval js pc)
    (ecallAfterThree js pc) (ecall_three_run js pc)]
  rw [JoltISA.execProgram_instr_run_retire _ _ (ecallAfterThree js pc)
    (ecallAfterMstatus js pc) (ecall_mstatus_run js pc)]
  rw [JoltISA.execProgram_instr_run_retire _ _ (ecallAfterMstatus js pc)
    (ecallAfterJalr js pc nextPC)
    (ecall_jalr_run js pc nextPC misa hnextPC hmisa hfetch)]
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure]

/-- ECALL trap-entry equivalence under the system CSR projection.

The assumptions expose exactly the current ZeroOS/M-mode envelope: ordinary
architectural reads needed by the two control-flow rows are present; the current
privilege is Machine; Sail's generated mstatus trap update agrees with Rust's
constant `0x1800`; and Sail's `tvec_addr` helper selects the same target as
Jolt's final `JALR`. -/
theorem ecallProgram_eq_sail_trap_entry
    (js : SailJoltState)
    (h_sys : EcallSystemAssumptions js) :
    systemProjectResult ((JoltISA.execProgram JoltISA.ecallProgram).run js) =
      sailEcallTrapEntry.run (systemProject js) := by
  rcases h_sys.pc_readable.exists_value with ⟨pc, hpc⟩
  rcases h_sys.nextPC_readable.exists_value with ⟨nextPC, hnextPC⟩
  rcases h_sys.medeleg_readable.exists_value with ⟨medeleg, hmedeleg⟩
  rcases h_sys.misa_readable.exists_value with ⟨misa, hmisa⟩
  have hJolt :=
    ecallProgram_run js pc nextPC misa hpc hnextPC hmisa
      h_sys.trap_target_fetch_aligned.bit1_zero
  have hSail :=
    sailEcallTrapEntry_machine_run js pc nextPC medeleg misa hpc hmedeleg hmisa
      h_sys.elp_zero h_sys.cur_privilege_machine.value
      h_sys.mstatus_matches_zeroOS_trap.value_eq
      h_sys.trap_vector_matches_jalr.value_eq
  unfold systemProjectResult
  rw [hJolt]
  exact hSail.symm

end System

end
