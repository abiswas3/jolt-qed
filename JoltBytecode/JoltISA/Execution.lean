import JoltBytecode.JoltISA.Semantics

/-!
# Jolt ISA execution wrappers

This file records the two execution shapes used by the Jolt side:
native final Jolt instructions run through `execInstr`, while expanded source
instructions run through `execProgram`.
-/

namespace JoltISA

inductive JoltExecution where
  | nativeInstr (instr : Instr)
  | expandedInstr (program : Program)
  deriving Repr

noncomputable def JoltExecution.run : JoltExecution → JoltMonad ExecutionResult
  | .nativeInstr instr => execInstr instr
  | .expandedInstr program => execProgram program

end JoltISA
