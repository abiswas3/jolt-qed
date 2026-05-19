import JoltBytecode.JoltISA.Semantics.Lemmas
import JoltBytecode.JoltISA.Semantics.RegisterOps

/-!
# VirtualSignExtendWord instruction semantics

Run lemmas for the Jolt ISA `VirtualSignExtendWord` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

def jolt_virtual_sign_extend_word (rd : regidx) : JoltMonad Unit := do
  let v ← liftSail (rX_bits rd)
  liftSail (wX_bits rd (sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0)))

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
theorem exists_sail_state_after_virtual_sign_extend_word_run_xreg_xreg (rd rs : regidx)
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
theorem exists_state_after_virtual_sign_extend_word_run_xreg_xreg (rd rs : regidx)
    (js : SailJoltState) (x : BitVec 64)
    (hr : rX_bits rs js.sail = .ok x js.sail) :
    ∃ js',
      (execInstr (.VirtualSignExtendWord (.xreg rd) (.xreg rs))).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64) (Sail.BitVec.extractLsb x 31 0)) := by
  obtain ⟨s', h_run, h_write⟩ :=
    exists_sail_state_after_virtual_sign_extend_word_run_xreg_xreg rd rs js x hr
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
    exists_state_after_virtual_sign_extend_word_run_xreg_xreg rd rs js x
      h_source_reads_x
  exact ⟨js', h_source_reads_x, h_sail_after_sign_extend, h_run⟩

/-- `VirtualSignExtendWord rd, rd` after a prior write to the same `rd`.

For `rd ≠ x0`, the instruction reads back the value written by the previous
instruction. For `rd = x0`, both writes are no-ops and the instruction reads
zero, so the same final `stateAfterWrite` statement still holds without an
external `rd ≠ x0` assumption. -/
theorem exists_state_after_virtual_sign_extend_word_run_xreg_xreg_of_same_register_write
    (rd : regidx)
    (js : SailJoltState)
    (s_before : SailState)
    (x : BitVec 64)
    (h_sail : js.sail = stateAfterWrite s_before rd x) :
    ∃ js',
      js'.sail = stateAfterWrite s_before rd
        (sign_extend (m := 64) (Sail.BitVec.extractLsb x 31 0)) ∧
      (execInstr (.VirtualSignExtendWord (.xreg rd) (.xreg rd))).run js =
        .ok RETIRE_SUCCESS js' := by
  by_cases hrd_zero : rd = regidx.Regidx 0
  · subst hrd_zero
    obtain ⟨js', h_run, h_sail_after_sign_extend⟩ :=
      exists_state_after_virtual_sign_extend_word_run_xreg_xreg
        (regidx.Regidx 0) (regidx.Regidx 0) js 0#64
        (rX_bits_regidx_zero js.sail)
    refine ⟨js', ?_, h_run⟩
    rw [h_sail_after_sign_extend, stateAfterWrite_regidx_zero]
    rw [h_sail, stateAfterWrite_regidx_zero, stateAfterWrite_regidx_zero]
  · have h_source_reads_x : rX_bits rd js.sail = .ok x js.sail := by
      rw [h_sail]
      exact rX_after_stateAfterWrite rd x s_before hrd_zero
    obtain ⟨js', h_run, h_sail_after_sign_extend⟩ :=
      exists_state_after_virtual_sign_extend_word_run_xreg_xreg rd rd js x
        h_source_reads_x
    refine ⟨js', ?_, h_run⟩
    rw [h_sail_after_sign_extend, h_sail]
    exact stateAfterWrite_stateAfterWrite rd x
      (sign_extend (m := 64) (Sail.BitVec.extractLsb x 31 0)) s_before

theorem jolt_virtual_sign_extend_word_concrete (rd : regidx)
    (js : SailJoltState) (v : BitVec 64)
    (hread : rX_bits rd js.sail = .ok v js.sail) :
    ∃ js' : SailJoltState,
      (jolt_virtual_sign_extend_word rd).run js = .ok () js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0)) := by
  obtain ⟨s', hw⟩ := wX_shape rd
    (sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0)) js.sail
  refine ⟨{ sail := s', vregs := js.vregs }, ?_, ?_⟩
  · unfold jolt_virtual_sign_extend_word liftSail
    simp only [bind, EStateM.bind, EStateM.run, hread, hw]
  · exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

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

/-- `VirtualSignExtendWord` from a virtual source to a virtual destination. -/
theorem virtual_sign_extend_word_run_vreg_vreg (vd vs : VReg) (js : SailJoltState) :
    (execInstr (.VirtualSignExtendWord (.vreg vd) (.vreg vs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then sign_extend (m := 64) (Sail.BitVec.extractLsb (js.vregs vs) 31 0)
            else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg writeVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `VirtualSignExtendWord` from a virtual source to a real destination. -/
theorem virtual_sign_extend_word_run_xreg_vreg (rd : regidx) (vs : VReg)
    (js : SailJoltState) (s' : SailState)
    (hw : wX_bits rd
      (sign_extend (m := 64) (Sail.BitVec.extractLsb (js.vregs vs) 31 0))
      js.sail = .ok () s') :
    (execInstr (.VirtualSignExtendWord (.xreg rd) (.vreg vs))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]

/-- `VirtualSignExtendWord` from a real source to a virtual destination,
packaged as an instruction step. It exposes the read, the virtual-register
write, the unchanged Sail state, and the successful run. -/
theorem exists_state_after_virtual_sign_extend_word_run_vreg_xreg
    (vd : VReg) (rs : regidx) (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    ∃ js',
      rX_bits rs js.sail = .ok x js.sail ∧
      js'.sail = js.sail ∧
      js'.vregs vd = sign_extend (m := 64) (Sail.BitVec.extractLsb x 31 0) ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      (execInstr (.VirtualSignExtendWord (.vreg vd) (.xreg rs))).run js =
        .ok RETIRE_SUCCESS js' := by
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = vd then sign_extend (m := 64) (Sail.BitVec.extractLsb x 31 0)
        else js.vregs r }
  refine ⟨js', h, rfl, ?_, ?_, ?_⟩
  · simp [js']
  · intro r hne
    simp [js', hne]
  · simpa only [js'] using virtual_sign_extend_word_run_vreg_xreg vd rs js x h

end JoltISA

end
