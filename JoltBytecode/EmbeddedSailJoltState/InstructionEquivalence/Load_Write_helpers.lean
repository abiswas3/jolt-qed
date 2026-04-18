import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Common_Memory_helpers

open Sail PreSail LeanRV64D.Functions
open Std.Do
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace InstructionEquivalence

theorem load_write_phase_concrete (rd : regidx) (js : SailJoltState) (js_logic : SailJoltState) (logic_val : BitVec 64)
    (hrd : rd ≠ regidx.Regidx 0)
    (hlogic_sail : js_logic.sail = js.sail)
    :
    ∃ js',
      (do
        liftSail (wX_bits rd logic_val)
        jolt_virtual_sign_extend_word rd
        pure RETIRE_SUCCESS).run js_logic = .ok RETIRE_SUCCESS js' ∧
      js'.sail =
        stateAfterWrite js.sail rd
          (sign_extend (m := 64) ((Sail.BitVec.extractLsb logic_val 31 0) : BitVec 32)) := by
  obtain ⟨s', hw⟩ := wX_shape rd logic_val js.sail
  let js_write : SailJoltState := { sail := s', vregs := js_logic.vregs }
  have hwrite : liftSail (wX_bits rd logic_val) js_logic = .ok () js_write := by
    unfold liftSail js_write
    rw [hlogic_sail, hw]
  have hs_write : js_write.sail = stateAfterWrite js.sail rd logic_val := by
    exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw
  have hread_rd : rX_bits rd js_write.sail = .ok logic_val js_write.sail := by
    rw [hs_write]
    exact rX_after_stateAfterWrite rd logic_val js.sail hrd
  obtain ⟨js', hvsew, hvsew_sail⟩ :=
    jolt_virtual_sign_extend_word_concrete rd js_write logic_val hrd hread_rd
  refine ⟨js', ?_, ?_⟩
  · simp only [liftSail, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
    rw [hlogic_sail, hw]
    simp only [EStateM.bind, EStateM.pure]
    cases hlast : jolt_virtual_sign_extend_word rd js_write with
    | ok a s =>
        have hs : s = js' := by
          simp [EStateM.run, hlast] at hvsew
          exact hvsew
        subst hs
        simp [hlast]
    | error e s =>
        have : False := by
          simp [EStateM.run, hlast] at hvsew
        exact False.elim this
  · rw [hvsew_sail, hs_write, stateAfterWrite_stateAfterWrite]

end InstructionEquivalence
