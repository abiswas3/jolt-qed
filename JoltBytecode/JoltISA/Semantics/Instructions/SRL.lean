import JoltBytecode.JoltISA.Semantics.Lemmas
import JoltBytecode.JoltISA.Semantics.RegisterOps

/-!
# SRL instruction semantics

Run lemmas for the Jolt ISA `SRL` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `SRL` from virtual registers to a real register performs a logical right
shift, writing the shifted value through Sail's architectural register write. -/
theorem execInstr_srl_vreg_vreg_xreg_run (rd : regidx) (value shamt : VReg)
    (js : SailJoltState) (s' : SailState)
    (h : wX_bits rd
        (shift_bits_right (js.vregs value) (Sail.BitVec.extractLsb (js.vregs shamt) 5 0))
        js.sail = .ok () s') :
    (execInstr (.SRL (.xreg rd) (.vreg value) (.vreg shamt))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get, h]

end JoltISA

end
