import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics

/-!
# Basic Jolt ISA semantic lemmas

Instruction-specific proof files should import this module when they need
facts about the generic interpreter rather than unfolding it ad hoc.
-/

set_option maxHeartbeats 1_000_000_000

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

-- TODO: Not sure if we need this as simp lemmas to clean up proof but to be seen.

/-- Executing a terminal Jolt program returns its terminal result without
changing the state. -/
-- True by literally how we write execProgram
@[simp] theorem execProgram_done (result : ExecutionResult) :
    execProgram (.done result) = (pure result : JoltMonad ExecutionResult) := rfl

/-- Executing a non-empty Jolt program means executing the head instruction and,
only if it retires successfully, continuing with the tail. -/
@[simp] theorem execProgram_instr (instr : Instr) (rest : Program) :
    execProgram (.instr instr rest) =
      (execInstr instr >>= fun
        | .Retire_Success () => execProgram rest
        | result => pure result) := rfl 
end JoltISA

end
