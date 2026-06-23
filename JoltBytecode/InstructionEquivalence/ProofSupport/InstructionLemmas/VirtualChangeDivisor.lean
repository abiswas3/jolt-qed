import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.StateLemmas

/-!
# VirtualChangeDivisor instruction semantics

Run lemmas for the Jolt ISA `VirtualChangeDivisor` instructions.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `VirtualChangeDivisor` reads real dividend/divisor and writes the adjusted divisor. -/
theorem virtual_change_divisor_run (vd : VReg) (dividend divisor : regidx)
    (js : SailJoltState) (x y : BitVec 64)
    (hdividend : rX_bits dividend js.sail = .ok x js.sail)
    (hdivisor : rX_bits divisor js.sail = .ok y js.sail)
    (hvd : WritableVReg vd) :
    (execInstr (.VirtualChangeDivisor (.vreg vd) (.xreg dividend) (.xreg divisor))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then change_divisor_value x y else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [hdividend, hdivisor, bind, EStateM.bind, EStateM.run]
  exact writeVReg_retire_run_of_writable vd (change_divisor_value x y) js hvd

/-- `VirtualChangeDivisorW` reads virtual dividend/divisor and writes the adjusted divisor. -/
theorem virtual_change_divisor_w_run (vd dividend divisor : VReg)
    (js : SailJoltState) (hvd : WritableVReg vd) :
    (execInstr (.VirtualChangeDivisorW (.vreg vd) (.vreg dividend) (.vreg divisor))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then change_divisor_w_value (js.vregs dividend) (js.vregs divisor)
            else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  exact writeVReg_retire_run_of_writable vd
    (change_divisor_w_value (js.vregs dividend) (js.vregs divisor)) js hvd

/-- Existential single-write post-state for `VirtualChangeDivisor`. -/
theorem virtual_change_divisor_run_ex (vd : VReg) (dividend divisor : regidx)
    (js : SailJoltState) (x y : BitVec 64)
    (hdividend : rX_bits dividend js.sail = .ok x js.sail)
    (hdivisor : rX_bits divisor js.sail = .ok y js.sail)
    (hvd : WritableVReg vd) :
    ∃ js',
      (execInstr (.VirtualChangeDivisor (.vreg vd) (.xreg dividend) (.xreg divisor))).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = change_divisor_value x y ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail :=
  writeSingleVReg_ex (virtual_change_divisor_run vd dividend divisor js x y hdividend hdivisor hvd)

end JoltISA

end
