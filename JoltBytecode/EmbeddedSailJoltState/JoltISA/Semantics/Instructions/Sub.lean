import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Lemmas
import JoltBytecode.EmbeddedSailJoltState.RegisterOps

/-!
# SUB instruction semantics

Run lemmas for the Jolt ISA `SUB` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `SUB` from two real sources to a real destination reads both architectural
sources and writes their difference through Sail. -/
theorem sub_run_xreg_xreg_xreg (rd rs1 rs2 : regidx)
    (js : SailJoltState) (x y : BitVec 64) (s' : SailState)
    (h₁ : rX_bits rs1 js.sail = .ok x js.sail)
    (h₂ : rX_bits rs2 js.sail = .ok y js.sail)
    (hw : wX_bits rd (x - y) js.sail = .ok () s') :
    (execInstr (.SUB (.xreg rd) (.xreg rs1) (.xreg rs2))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst liftSail
  simp only [h₁, h₂, hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]

/-- `SUB` from two real sources to a real destination, with the output Sail
state exposed as the architectural write performed by the instruction. -/
theorem exists_state_after_sub_run_xreg_xreg_xreg (rd rs1 rs2 : regidx)
    (js : SailJoltState) (x y : BitVec 64)
    (h₁ : rX_bits rs1 js.sail = .ok x js.sail)
    (h₂ : rX_bits rs2 js.sail = .ok y js.sail) :
    ∃ js',
      rX_bits rs1 js.sail = .ok x js.sail ∧
      rX_bits rs2 js.sail = .ok y js.sail ∧
      js'.sail = stateAfterWrite js.sail rd (x - y) ∧
      (execInstr (.SUB (.xreg rd) (.xreg rs1) (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js' := by
  obtain ⟨s', hw⟩ := wX_shape rd (x - y) js.sail
  have h_sail_after_sub :
      s' = stateAfterWrite js.sail rd (x - y) :=
    wX_bits_eq_stateAfterWrite rd (x - y) js.sail s' hw
  exact ⟨{ sail := s', vregs := js.vregs },
    h₁,
    h₂,
    h_sail_after_sub,
    sub_run_xreg_xreg_xreg rd rs1 rs2 js x y s' h₁ h₂ hw⟩

end JoltISA

end
