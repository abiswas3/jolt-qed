import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess
import JoltBytecode.InstructionEquivalence.ProofSupport.StateLemmas

/-!
# VirtualAdvice instruction semantics

Run lemmas for the Jolt ISA `VirtualAdvice` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `VirtualAdvice` writes the supplied advice value into a virtual register. -/
theorem virtual_advice_run (vd : VReg) (advice : BitVec 64) (js : SailJoltState)
    (hvd : WritableVReg vd) :
    (execInstr (.VirtualAdvice vd advice)).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then advice else js.vregs r } := by
  unfold execInstr
  exact writeVReg_retire_run_of_writable vd advice js hvd

/-- `VirtualAdviceLoad` writes the supplied advice value to an architectural
destination register. -/
theorem virtual_advice_load_run_xreg
    (rd : regidx) (advice : BitVec 64) (js : SailJoltState) (s' : SailState)
    (hw : wX_bits rd advice js.sail = .ok () s') :
    (execInstr (.VirtualAdviceLoad (.xreg rd) advice)).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr writeDst liftSail
  simp only [hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]

/-- `VirtualAdviceLoad` to an architectural register, exposing the resulting
Sail state as the corresponding register write. -/
theorem exists_state_after_virtual_advice_load_run_xreg
    (rd : regidx) (advice : BitVec 64) (js : SailJoltState) :
    ∃ js',
      js'.sail = stateAfterWrite js.sail rd advice ∧
      js'.vregs = js.vregs ∧
      (execInstr (.VirtualAdviceLoad (.xreg rd) advice)).run js =
        .ok RETIRE_SUCCESS js' := by
  obtain ⟨s', hw⟩ := wX_shape rd advice js.sail
  have h_sail_after :
      s' = stateAfterWrite js.sail rd advice :=
    wX_bits_eq_stateAfterWrite rd advice js.sail s' hw
  exact ⟨{ sail := s', vregs := js.vregs },
    h_sail_after,
    rfl,
    virtual_advice_load_run_xreg rd advice js s' hw⟩

/-- Existential single-write post-state for `VirtualAdvice`. -/
theorem virtual_advice_run_ex (vd : VReg) (advice : BitVec 64) (js : SailJoltState)
    (hvd : WritableVReg vd) :
    ∃ js',
      (execInstr (.VirtualAdvice vd advice)).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = advice ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail :=
  writeSingleVReg_ex (virtual_advice_run vd advice js hvd)

end JoltISA

end
