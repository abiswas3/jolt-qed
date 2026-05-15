import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Lemmas
import JoltBytecode.EmbeddedSailJoltState.RegisterOps

/-!
# VirtualSignExtendWord instruction semantics

Run lemmas for the Jolt ISA `VirtualSignExtendWord` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `VirtualSignExtendWord` from a real source to a real destination reads the
source and writes `sext(source[31:0])`. -/
theorem virtual_sign_extend_word_run_xreg_xreg (rd rs : regidx)
    (js : SailJoltState) (x : BitVec 64) (s' : SailState)
    (hr : rX_bits rs js.sail = .ok x js.sail)
    (hw : wX_bits rd (sign_extend (m := 64) (Sail.BitVec.extractLsb x 31 0)) js.sail =
      .ok () s') :
    (execInstr (.VirtualSignExtendWord (.xreg rd) (.xreg rs))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst liftSail
  simp only [hr, bind, EStateM.bind, pure, EStateM.pure, EStateM.run, hw]

/-- `VirtualSignExtendWord` from a real source to a real destination, with the
output state chosen by the instruction lemma. -/
theorem exists_state_after_virtual_sign_extend_word_run_xreg_xreg (rd rs : regidx)
    (js : SailJoltState) (x : BitVec 64)
    (hr : rX_bits rs js.sail = .ok x js.sail) :
    ∃ s',
      (execInstr (.VirtualSignExtendWord (.xreg rd) (.xreg rs))).run js =
        .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } ∧
      wX_bits rd (sign_extend (m := 64) (Sail.BitVec.extractLsb x 31 0)) js.sail =
        .ok () s' := by
  obtain ⟨s', hw⟩ :=
    wX_shape rd (sign_extend (m := 64) (Sail.BitVec.extractLsb x 31 0)) js.sail
  exact ⟨s', virtual_sign_extend_word_run_xreg_xreg rd rs js x s' hr hw, hw⟩

/-- `VirtualSignExtendWord` from a real source to a real destination, exposing
the full checkpoint state produced by the architectural write. -/
theorem exists_jolt_state_after_virtual_sign_extend_word_run_xreg_xreg (rd rs : regidx)
    (js : SailJoltState) (x : BitVec 64)
    (hr : rX_bits rs js.sail = .ok x js.sail) :
    ∃ js',
      (execInstr (.VirtualSignExtendWord (.xreg rd) (.xreg rs))).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64) (Sail.BitVec.extractLsb x 31 0)) := by
  obtain ⟨s', h_run, h_write⟩ :=
    exists_state_after_virtual_sign_extend_word_run_xreg_xreg rd rs js x hr
  refine ⟨{ sail := s', vregs := js.vregs }, h_run, ?_⟩
  exact wX_bits_eq_stateAfterWrite rd
    (sign_extend (m := 64) (Sail.BitVec.extractLsb x 31 0)) js.sail s' h_write

/-- `VirtualSignExtendWord` where the source register was established by a
previous architectural write. The lemma packages the read performed by this
instruction together with its successful run and output state. -/
theorem exists_state_after_virtual_sign_extend_word_run_xreg_xreg_of_source_write
    (rd rs : regidx)
    (js : SailJoltState)
    (s_before : SailState)
    (x : BitVec 64)
    (hrs : rs ≠ regidx.Regidx 0)
    (h_sail : js.sail = stateAfterWrite s_before rs x) :
    ∃ js',
      rX_bits rs js.sail = .ok x js.sail ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64) (Sail.BitVec.extractLsb x 31 0)) ∧
      (execInstr (.VirtualSignExtendWord (.xreg rd) (.xreg rs))).run js =
        .ok RETIRE_SUCCESS js' := by
  have h_source_reads_x : rX_bits rs js.sail = .ok x js.sail := by
    rw [h_sail]
    exact rX_after_stateAfterWrite rs x s_before hrs
  obtain ⟨js', h_run, h_sail_after_sign_extend⟩ :=
    exists_jolt_state_after_virtual_sign_extend_word_run_xreg_xreg rd rs js x
      h_source_reads_x
  exact ⟨js', h_source_reads_x, h_sail_after_sign_extend, h_run⟩

/-- `VirtualSignExtendWord` from a real source to a virtual destination computes
the word-sign-extended scratch value used by word operations. -/
theorem virtual_sign_extend_word_run_vreg_xreg (vd : VReg) (rs : regidx)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    (execInstr (.VirtualSignExtendWord (.vreg vd) (.xreg rs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then sign_extend (m := 64) (Sail.BitVec.extractLsb x 31 0)
            else js.vregs r } := by
  unfold execInstr readSrc writeDst liftSail writeVReg
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

end JoltISA

end
