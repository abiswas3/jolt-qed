import JoltBytecode.InstructionEquivalence.System.Common

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
the M-mode-only ZeroOS envelope, so the theorem statement exposes the envelope
under which Sail's xret postlude is observationally the same as Jolt's virtual
CSR projection.
-/

/-- Jolt's concrete MRET return target: `JALR` reads virtual `mepc` and clears
bit 0. -/
def mretReturnTarget (js : SailJoltState) : BitVec 64 :=
  BitVec.update (js.vregs JoltISA.mepcVReg) 0 0#1

/-- Concrete Jolt state after Rust's one-row MRET expansion. The scratch write is
not part of `systemProject`, but keeping it in the model matches the emitted
`JALR` row exactly. -/
def mretAfterJalr (js : SailJoltState) (nextPC : BitVec 64) : SailJoltState :=
  joltSetVReg { js with sail := setNextPCState js.sail (mretReturnTarget js) }
    JoltISA.systemScratchVReg nextPC

/-- Assumptions for comparing Rust/Jolt MRET with Sail MRET under the system CSR
projection.

The first fields are the concrete reads needed by the Jolt `JALR` row and the
generated Sail `execute_MRET` path. The final fields are the ZeroOS/M-mode
envelope: the raw Sail xret postlude must reduce to the same projected state as
the Rust-faithful `JALR`, and the resulting return target must be fetch-aligned
for Sail/Jolt `jump_to`. -/
structure MretSystemAssumptions (js : SailJoltState) : Prop where
  pc_readable :
    ∃ pc : BitVec 64, js.sail.regs.get? Register.PC =
      some (pc : RegisterType Register.PC)
  nextPC_readable :
    ∃ nextPC : BitVec 64, js.sail.regs.get? Register.nextPC =
      some (nextPC : RegisterType Register.nextPC)
  misa_readable :
    ∃ misa : BitVec 64, js.sail.regs.get? Register.misa =
      some (misa : RegisterType Register.misa)
  cur_privilege_machine :
    js.sail.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege)
  sail_xret_matches_jalr :
    (execute_MRET ()).run (systemProject js) =
      .ok RETIRE_SUCCESS
        (systemProject
          { js with sail := setNextPCState js.sail (mretReturnTarget js) })
  return_target_fetch_aligned :
    BitVec.access (mretReturnTarget js) 1 = 0#1

/-- MRET equivalence under the system CSR projection.

This is intentionally stated before the proof is filled in. The proof should
follow ECALL's final-`JALR` shape for the Jolt side, then discharge the Sail
side through `MretSystemAssumptions.sail_xret_matches_jalr` until the ZeroOS
xret reduction is proved explicitly. -/
theorem mretProgram_eq_sail
    (js : SailJoltState)
    (h_sys : MretSystemAssumptions js) :
    systemProjectResult ((JoltISA.execProgram JoltISA.mretProgram).run js) =
      (execute_MRET ()).run (systemProject js) := by
  sorry

end System

end
