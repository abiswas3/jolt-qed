import JoltBytecode.InstructionEquivalence.System.Common

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace System

/-!
# EBREAK system expansion

Rust does not expand `EBREAK` by synthesizing Sail's architectural breakpoint
trap. It emits one Jolt row:

* `JAL scratch, 0`

That row jumps to the current architectural `PC`, writes the old `nextPC` link
into an instruction-local virtual scratch register, and retires successfully.
At the emulator layer that fixed-PC jump is used as a termination marker.

The generated Sail instruction has a different result shape: `execute_EBREAK`
returns a software-breakpoint `Trap` at the current `PC` and does not perform
the Jolt scratch/link write. Therefore the old theorem shape,

```
projectResult (run Jolt ebreakProgram) = run Sail execute_EBREAK
```

is too strong and is expected to be false. The theorem below instead uses the
relation that the Rust expansion intends: Jolt reaches the self-loop
termination marker at the same `PC` for which Sail reports a software
breakpoint trap. This keeps the mismatch explicit rather than hiding it behind
an equality assumption.
-/

/-- Concrete Jolt state after Rust's single-row EBREAK expansion.

The embedded Sail state records the self-loop by setting `nextPC := pc`. The
virtual scratch write preserves the emitted `JAL scratch, 0` row exactly, but it
is intentionally not visible through plain `projectResult`. -/
def ebreakAfterJal (js : SailJoltState) (pc nextPC : BitVec 64) :
    SailJoltState :=
  joltSetVReg { js with sail := setNextPCState js.sail pc }
    JoltISA.systemScratchVReg nextPC

/-- `JAL scratch, 0` computes the current `PC` as its jump target. -/
theorem jal_zero_target (pc : BitVec 64) :
    pc + sign_extend (m := 64) (0 : BitVec 21) = pc := by
  have hzero : sign_extend (m := 64) (0 : BitVec 21) = 0#64 := by
    native_decide
  rw [hzero]
  bv_decide

/-- Jumping to a fetch-aligned `PC` succeeds and writes that value into
`nextPC`.

Even when bit 1 is known to be zero, the generated Sail `jump_to` expression
still evaluates the compressed-extension query, so this helper carries the
`misa` read needed by `currentlyEnabled Ext_Zca`. -/
theorem jump_to_pc_run
    (js : SailJoltState) (pc misa : BitVec 64)
    (hmisa : js.sail.regs.get? Register.misa =
      some (misa : RegisterType Register.misa))
    (hpc0 : BitVec.access pc 0 = 0#1)
    (hpc1 : BitVec.access pc 1 = 0#1) :
    jump_to pc js.sail =
      .ok RETIRE_SUCCESS (setNextPCState js.sail pc) := by
  have hExtC := currentlyEnabled_Ext_C_run js.sail misa hmisa
  have hassert : (0#1 == 0#1) = true := by
    native_decide
  have hbit1 : bool_bit_backwards 0#1 = false := by
    native_decide
  unfold jump_to ext_control_check_pc SailME.run PreSail.PreSailME.run
  unfold currentlyEnabled hartSupports
  unfold set_next_pc setNextPCState sail_branch_announce redirect_callback
  unfold Sail.assert PreSail.assert Sail.writeReg PreSail.writeReg
  simp only [hassert, hbit1, hExtC, hpc0, hpc1, bit_to_bool, if_true,
    if_false, Bool.false_and, Bool.false_eq_true, bind, EStateM.bind,
    pure, EStateM.pure, EStateM.map, Functor.map, ExceptT.run,
    ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift,
    MonadLift.monadLift, monadLift, liftM, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet]

/-- Concrete Jolt row for EBREAK: Rust's `JAL scratch, 0` retires after writing
the self-loop target to Sail `nextPC` and the link to the scratch vreg. -/
theorem ebreak_jal_run
    (js : SailJoltState) (pc nextPC misa : BitVec 64)
    (hpc : js.sail.regs.get? Register.PC =
      some (pc : RegisterType Register.PC))
    (hnextPC : js.sail.regs.get? Register.nextPC =
      some (nextPC : RegisterType Register.nextPC))
    (hmisa : js.sail.regs.get? Register.misa =
      some (misa : RegisterType Register.misa))
    (hpc0 : BitVec.access pc 0 = 0#1)
    (hpc1 : BitVec.access pc 1 = 0#1) :
    (JoltISA.execInstr
      (.JAL (.vreg JoltISA.systemScratchVReg) (0 : BitVec 21))).run js =
      .ok RETIRE_SUCCESS (ebreakAfterJal js pc nextPC) := by
  have hJump := jump_to_pc_run js pc misa hmisa hpc0 hpc1
  rw [RETIRE_SUCCESS] at hJump
  unfold JoltISA.execInstr JoltISA.writeDst readVReg writeVReg
  unfold liftSail get_next_pc
  unfold Sail.readReg PreSail.readReg
  unfold ebreakAfterJal setNextPCState joltSetVReg vregWrite
  unfold RETIRE_SUCCESS
  simp only [hnextPC, hpc, hJump, jal_zero_target, bind, EStateM.bind,
    pure, EStateM.pure, EStateM.run, get, getThe, MonadStateOf.get,
    EStateM.get, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  unfold setNextPCState
  rfl

/-- The full one-row EBREAK program reaches the concrete Jolt self-loop state. -/
theorem ebreakProgram_run
    (js : SailJoltState) (pc nextPC misa : BitVec 64)
    (hpc : js.sail.regs.get? Register.PC =
      some (pc : RegisterType Register.PC))
    (hnextPC : js.sail.regs.get? Register.nextPC =
      some (nextPC : RegisterType Register.nextPC))
    (hmisa : js.sail.regs.get? Register.misa =
      some (misa : RegisterType Register.misa))
    (hpc0 : BitVec.access pc 0 = 0#1)
    (hpc1 : BitVec.access pc 1 = 0#1) :
    (JoltISA.execProgram JoltISA.ebreakProgram).run js =
      .ok RETIRE_SUCCESS (ebreakAfterJal js pc nextPC) := by
  unfold JoltISA.ebreakProgram
  rw [JoltISA.execProgram_instr_run_retire _ _ js (ebreakAfterJal js pc nextPC)
    (ebreak_jal_run js pc nextPC misa hpc hnextPC hmisa hpc0 hpc1)]
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure]

/-- Concrete Sail row for EBREAK: Sail reports a software-breakpoint trap at
the current `PC` and leaves the state unchanged. -/
theorem sail_ebreak_run
    (js : SailJoltState) (pc : BitVec 64) (priv : Privilege)
    (hpc : js.sail.regs.get? Register.PC =
      some (pc : RegisterType Register.PC))
    (hpriv : js.sail.regs.get? Register.cur_privilege =
      some (priv : RegisterType Register.cur_privilege)) :
    (execute_EBREAK ()).run js.sail =
      .ok
        (ExecutionResult.Trap
          (priv,
            ctl_result.CTL_TRAP
              (make_sync_exception
                (ExceptionType.E_Breakpoint breakpoint_cause.Brk_Software) pc),
            pc))
        js.sail := by
  unfold execute_EBREAK
  unfold Sail.readReg PreSail.readReg
  simp only [hpriv, hpc, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]

/-- EBREAK correctness relation.

The first component is the Rust/Jolt termination marker: after projection,
`JAL scratch, 0` retires successfully with Sail `nextPC` set back to the
current `PC`. The second component is the architectural Sail behavior:
`execute_EBREAK` returns a software-breakpoint trap at that same `PC`.

This relation deliberately does not require equal `ExecutionResult`
constructors, because `Retire_Success` and `Trap` are the intended observable
difference between Jolt's termination convention and Sail's architectural
instruction semantics. -/
def EbreakResultRelation
    (s : SailState) (pc : BitVec 64)
    (joltResult sailResult :
      EStateM.Result (Error exception) SailState ExecutionResult) : Prop :=
  joltResult = .ok RETIRE_SUCCESS (setNextPCState s pc) ∧
    ∃ priv : Privilege,
      sailResult =
        .ok
          (ExecutionResult.Trap
            (priv,
              ctl_result.CTL_TRAP
                (make_sync_exception
                  (ExceptionType.E_Breakpoint breakpoint_cause.Brk_Software)
                  pc),
              pc))
          s

/-- Rust-faithful EBREAK expansion matches Sail EBREAK through the explicit
self-loop/breakpoint relation, not through raw result equality. -/
theorem ebreakProgram_rel_sail
    (js : SailJoltState) (pc nextPC misa : BitVec 64) (priv : Privilege)
    (hpc : js.sail.regs.get? Register.PC =
      some (pc : RegisterType Register.PC))
    (hnextPC : js.sail.regs.get? Register.nextPC =
      some (nextPC : RegisterType Register.nextPC))
    (hmisa : js.sail.regs.get? Register.misa =
      some (misa : RegisterType Register.misa))
    (hpriv : js.sail.regs.get? Register.cur_privilege =
      some (priv : RegisterType Register.cur_privilege))
    (hpc0 : BitVec.access pc 0 = 0#1)
    (hpc1 : BitVec.access pc 1 = 0#1) :
    EbreakResultRelation js.sail pc
      (projectResult ((JoltISA.execProgram JoltISA.ebreakProgram).run js))
      ((execute_EBREAK ()).run js.sail) := by
  have hJolt := ebreakProgram_run js pc nextPC misa hpc hnextPC hmisa hpc0 hpc1
  have hSail := sail_ebreak_run js pc priv hpc hpriv
  unfold EbreakResultRelation
  constructor
  · rw [hJolt]
    unfold projectResult project ebreakAfterJal joltSetVReg
    rfl
  · exact ⟨priv, hSail⟩

end System

end
