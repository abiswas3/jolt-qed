import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Common_Memory_helpers

open Sail PreSail LeanRV64D.Functions
open Std.Do
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace InstructionEquivalence

theorem vreg_LD_step_concrete (js : SailJoltState) (js1 : SailJoltState) (addr : BitVec 64)
    (hcfg : JoltConfig js.sail)
    (hsetup_sail : js1.sail = js.sail)
    (hsetup_v1 : js1.vregs 1 = addr)
    (haligned : AlignedDwordAccess addr)
    (htranslate : BareTranslation addr js.sail)
    (hphys : FlatPhysMem addr 8 js.sail)
    :
    ∃ js_load,
      vreg_LD 1 1 0 js1 = .ok RETIRE_SUCCESS js_load ∧
      js_load.sail = js.sail ∧
      js_load.vregs 0 = js1.vregs 0 ∧
      js_load.vregs 1 = loaded_dword_at js.sail addr := by
  let js_load : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = 1 then loaded_dword_at js.sail addr else js1.vregs r }
  have hcfg1 : JoltConfig js1.sail := by simpa [hsetup_sail] using hcfg
  have htranslate1 : BareTranslation addr js1.sail := by
    simpa [hsetup_sail] using htranslate
  have hphys1 : FlatPhysMem addr 8 js1.sail := by
    simpa [hsetup_sail] using hphys
  have hdw : DwordLoadAssumptions addr js1.sail :=
    dword_load_assumptions_of_aligned_translate_phys addr js1.sail haligned htranslate1 hphys1
  refine ⟨js_load, ?_, rfl, ?_, ?_⟩
  · have hld := vreg_LD_run_of_dword_assumptions 1 1 js1 addr hsetup_v1 hcfg1 hdw
    simpa [js_load, hsetup_sail] using hld
  · simp [js_load]
  · simp [js_load]

-- Running the shared load setup succeeds without changing the Sail state,
-- stores the effective address in vreg 0, and stores the aligned dword base
-- address in vreg 1.
theorem load_phase_setup_concrete (imm : BitVec 12) (js : SailJoltState) (val : BitVec 64) :
    ∃ js1,
      (do
        writeVReg 0 (load_effective_address val imm)
        let v0 ← readVReg 0
        writeVReg 1 (v0 &&& (-8 : BitVec 64))).run js = .ok () js1 ∧
      js1.sail = js.sail ∧
      js1.vregs 0 = load_effective_address val imm ∧
      js1.vregs 1 = compute_aligned_dword_base_address val imm := by
  let ea := load_effective_address val imm
  let daddr := compute_aligned_dword_base_address val imm
  let js0 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = 0 then ea else js.vregs r }
  let js1 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = 1 then daddr else if r = 0 then ea else js.vregs r }
  have hw0 : writeVReg 0 ea js = .ok () js0 := by
    unfold writeVReg js0 ea
    simp [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  have hread_v0 : readVReg 0 js0 = .ok ea js0 := by
    rw [readVReg_run]
    simp [js0]
  have hw1 : writeVReg 1 daddr js0 = .ok () js1 := by
    unfold writeVReg js0 js1 ea daddr
    simp [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  refine ⟨js1, ?_, rfl, ?_, ?_⟩
  · simp only [bind, EStateM.bind, EStateM.run]
    rw [hw0]
    simp only []
    rw [hread_v0]
    simp only []
    exact hw1
  · simp [js1, daddr, ea]
  · simp [js1, daddr]

-- Running the shared load setup in its `vreg_ANDI`-based form (used by the
-- byte / halfword / vreg_ANDI-based LW load phase) succeeds without changing
-- the Sail state, stores the effective address in vreg 0, and stores the
-- aligned dword base address in vreg 1.
-- The setup is `ExecutionResult`-typed (ends with `vreg_ANDI` whose result is
-- `RETIRE_SUCCESS`), so it composes with `vreg_LD` via
-- `vreg_LD_phase_from_setup_er` below with no intervening `pure ()` to
-- collapse.
theorem load_phase_setup_concrete_andi (imm : BitVec 12) (js : SailJoltState) (val : BitVec 64) :
    ∃ js1,
      ((do
        writeVReg 0 (load_effective_address val imm)
        vreg_ANDI 1 0 (-8 : BitVec 12)) : JoltMonad ExecutionResult).run js =
          .ok RETIRE_SUCCESS js1 ∧
      js1.sail = js.sail ∧
      js1.vregs 0 = load_effective_address val imm ∧
      js1.vregs 1 = compute_aligned_dword_base_address val imm := by
  let ea := load_effective_address val imm
  let daddr := compute_aligned_dword_base_address val imm
  let js0 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = 0 then ea else js.vregs r }
  let js1 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = 1 then daddr else if r = 0 then ea else js.vregs r }
  have hw0 : writeVReg 0 ea js = .ok () js0 := by
    unfold writeVReg js0 ea
    simp [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  have h8 : sign_extend (m := 64) (-8 : BitVec 12) = (-8 : BitVec 64) := by decide
  have hv_andi : vreg_ANDI 1 0 (-8 : BitVec 12) js0 = .ok RETIRE_SUCCESS js1 := by
    change vreg_ANDI 1 0 (-8 : BitVec 12) js0 = .ok RETIRE_SUCCESS
      { sail := js0.sail
        vregs := fun r =>
          if r = 1 then js0.vregs 0 &&& sign_extend (m := 64) (-8 : BitVec 12)
          else js0.vregs r }
    simp [js0, js1, ea, daddr, h8, compute_aligned_dword_base_address,
          load_effective_address]
  refine ⟨js1, ?_, rfl, ?_, ?_⟩
  · simp only [bind, EStateM.bind, EStateM.run]
    rw [hw0]
    simp only []
    exact hv_andi
  · simp [js1, daddr, ea]
  · simp [js1, daddr]

-- If the setup phase succeeds (writing ea and base into vregs) and then
-- vreg_LD succeeds on the resulting state, then the composed sequence
-- (setup followed by vreg_LD) also succeeds with the same result.
theorem vreg_LD_phase_from_setup (setup : JoltMonad Unit) (js js1 js_load : SailJoltState)
    (hsetup_run : setup.run js = .ok () js1)
    (hld : vreg_LD 1 1 0 js1 = .ok RETIRE_SUCCESS js_load) :
    (do
      let _ ← setup
      vreg_LD 1 1 0).run js = .ok RETIRE_SUCCESS js_load := by
  have hsetup_run' : setup js = .ok () js1 := by
    simpa [EStateM.run] using hsetup_run
  simp only [bind, EStateM.bind, EStateM.run]
  rw [hsetup_run']
  simpa using hld

-- `ExecutionResult`-typed variant of `vreg_LD_phase_from_setup`. Used when
-- the setup ends in a virtual instruction (e.g. `vreg_ANDI`) whose result
-- type is `ExecutionResult` and whose successful return is `RETIRE_SUCCESS`.
-- Avoids wrapping the setup with a trailing `pure ()` to force Unit type.
theorem vreg_LD_phase_from_setup_er (setup : JoltMonad ExecutionResult)
    (js js1 js_load : SailJoltState)
    (hsetup_run : setup.run js = .ok RETIRE_SUCCESS js1)
    (hld : vreg_LD 1 1 0 js1 = .ok RETIRE_SUCCESS js_load) :
    (do
      let _ ← setup
      vreg_LD 1 1 0).run js = .ok RETIRE_SUCCESS js_load := by
  have hsetup_run' : setup js = .ok RETIRE_SUCCESS js1 := by
    simpa [EStateM.run] using hsetup_run
  simp only [bind, EStateM.bind, EStateM.run]
  rw [hsetup_run']
  simpa using hld

end InstructionEquivalence
