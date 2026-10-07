import JoltConstraints.Constraints.RamReadData
import JoltBytecode.InstructionEquivalence.ProofSupport.DeviceFrame

/-!
Execution never changes the device fields fixed when Rust builds its emulator:
the memory layout, the inputs and both advice buffers. Sail steps do not touch the device,
device stores only change `outputs` and `panic`, and HostIO only appends to the
advice tape. The trace-level result carries this from the program's initial
state to the final recorded state.
-/

set_option autoImplicit false

open Sail PreSail LeanRV64D.Functions


namespace JoltConstraints

open JoltIOSetupFrame

/-- The final recorded state has the program's initial device setup. -/
theorem finalTraceState_ioSame {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs) :
    Same trace.initialState.jolt_device (HonestWitness.finalTraceState trace).jolt_device := by
  unfold HonestWitness.finalTraceState
  split
  · rename_i nonempty
    exact (trace_preState_ioSame trace _ _).trans
      (execInstr_rule _ _ _ _ (getElem trace.rows (trace.rows.size - 1) _).executes)
  · exact Same.refl _

end JoltConstraints
