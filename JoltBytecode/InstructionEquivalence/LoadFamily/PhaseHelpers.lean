import JoltBytecode.JoltISA.Semantics.Instructions
import JoltBytecode.JoltISA.Semantics.ProgramComposition
import JoltBytecode.InstructionEquivalence.Common_Memory_helpers

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace InstructionEquivalence

/-!
# Program phases for the Jolt load family

The shared load prefix is a Jolt ISA program, not a proof-only monadic
reference:

1. `ADDI v0, rs1, imm` computes the effective address.
2. `ANDI v1, v0, -8` computes the enclosing dword base address.
3. `LD v1, v1, 0` loads that dword.

The lemmas below expose these as small `JoltISA.Program` phases, matching the
proof style used by the advice-family proofs.
-/

/-- Common setup phase for load expansions:
`ADDI v0, rs1, imm; ANDI v1, v0, -8`. -/
def loadSetupPhase (imm : BitVec 12) (rs1 : regidx) : JoltISA.Program :=
  .instr (.ADDI (.vreg 0) (.xreg rs1) imm) <|
  .instr (.ANDI (.vreg 1) (.vreg 0) (-8 : BitVec 12)) <|
  .done RETIRE_SUCCESS

/-- Common dword-load phase for load expansions: `LD v1, v1, 0`. -/
def loadDwordPhase : JoltISA.Program :=
  .instr (.LD 1 1 0) <|
  .done RETIRE_SUCCESS

/-- Common setup-plus-dword-load phase. -/
def loadPhase (imm : BitVec 12) (rs1 : regidx) : JoltISA.Program :=
  (loadSetupPhase imm rs1).append loadDwordPhase

/-- Running the setup phase computes `ea` in `v0` and the aligned dword base
in `v1`, without changing Sail state. -/
theorem loadSetupPhase_run (imm : BitVec 12) (rs1 : regidx)
    (js : SailJoltState) (val : BitVec 64)
    (hrx : rX_bits rs1 js.sail = .ok val js.sail) :
    ∃ js_setup,
      JoltISA.Program.Run (loadSetupPhase imm rs1) js js_setup ∧
      js_setup.sail = js.sail ∧
      js_setup.vregs 0 = load_effective_address val imm ∧
      js_setup.vregs 1 = compute_aligned_dword_base_address val imm := by
  let ea := load_effective_address val imm
  let daddr := compute_aligned_dword_base_address val imm
  let js_afterAddi : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (0 : JoltISA.VReg) then ea else js.vregs r }
  let js_setup : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = (1 : JoltISA.VReg) then daddr else js_afterAddi.vregs r }
  have h_addi_succeeds :
      (JoltISA.execInstr (.ADDI (.vreg 0) (.xreg rs1) imm)).run js =
        .ok RETIRE_SUCCESS js_afterAddi := by
    simpa only [js_afterAddi, ea, load_effective_address] using
      (JoltISA.addi_run_vreg_xreg (0 : JoltISA.VReg) rs1 imm js val hrx)
  have h_signExtend_neg8 :
      sign_extend (m := 64) (-8 : BitVec 12) = (-8 : BitVec 64) := by
    decide
  have h_andi_succeeds :
      (JoltISA.execInstr (.ANDI (.vreg 1) (.vreg 0) (-8 : BitVec 12))).run
        js_afterAddi =
        .ok RETIRE_SUCCESS js_setup := by
    simpa only [js_afterAddi, js_setup, ea, daddr, compute_aligned_dword_base_address,
      load_effective_address, h_signExtend_neg8] using
      (JoltISA.andi_run_vreg_vreg (1 : JoltISA.VReg) (0 : JoltISA.VReg)
        (-8 : BitVec 12) js_afterAddi)
  have h_setup_succeeds :
      JoltISA.Program.Run (loadSetupPhase imm rs1) js js_setup := by
    change (JoltISA.execProgram (loadSetupPhase imm rs1)).run js =
      .ok RETIRE_SUCCESS js_setup
    unfold loadSetupPhase
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterAddi h_addi_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterAddi js_setup h_andi_succeeds]
    rfl
  refine ⟨js_setup, h_setup_succeeds, rfl, ?_, ?_⟩
  · simp [js_setup, js_afterAddi, ea]
  · simp [js_setup, daddr]

/-- Running the `LD` phase from a setup state loads the enclosing dword into
`v1`, without changing Sail state or `v0`. -/
theorem loadDwordPhase_run (js : SailJoltState) (js_setup : SailJoltState)
    (addr : BitVec 64)
    (hcfg : JoltConfig js.sail)
    (hsetup_sail : js_setup.sail = js.sail)
    (hsetup_v1 : js_setup.vregs 1 = addr)
    (haligned : AlignedDwordAccess addr)
    (htranslate : BareTranslation addr js.sail)
    (hphys : FlatPhysMem addr 8 js.sail) :
    ∃ js_load,
      JoltISA.Program.Run loadDwordPhase js_setup js_load ∧
      js_load.sail = js.sail ∧
      js_load.vregs 0 = js_setup.vregs 0 ∧
      js_load.vregs 1 = loaded_dword_at js.sail addr := by
  let dword := loaded_dword_at js.sail addr
  let js_load : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (1 : JoltISA.VReg) then dword else js_setup.vregs r }
  have hcfg_setup : JoltConfig js_setup.sail := by
    simpa only [hsetup_sail] using hcfg
  have htranslate_setup : BareTranslation addr js_setup.sail := by
    simpa only [hsetup_sail] using htranslate
  have hphys_setup : FlatPhysMem addr 8 js_setup.sail := by
    simpa only [hsetup_sail] using hphys
  have hdword : DwordLoadAssumptions addr js_setup.sail :=
    dword_load_assumptions_of_aligned_translate_phys
      addr js_setup.sail haligned htranslate_setup hphys_setup
  have h_ld_succeeds :
      (JoltISA.execInstr (.LD 1 1 0)).run js_setup =
        .ok RETIRE_SUCCESS js_load := by
    have hld :=
      vreg_LD_run_of_dword_assumptions 1 1 js_setup addr hsetup_v1 hcfg_setup hdword
    simpa only [js_load, dword, hsetup_sail] using hld
  have h_phase_succeeds :
      JoltISA.Program.Run loadDwordPhase js_setup js_load := by
    change (JoltISA.execProgram loadDwordPhase).run js_setup =
      .ok RETIRE_SUCCESS js_load
    unfold loadDwordPhase
    rw [JoltISA.execProgram_instr_run_retire _ _ js_setup js_load h_ld_succeeds]
    rfl
  refine ⟨js_load, h_phase_succeeds, rfl, ?_, ?_⟩
  · simp [js_load]
  · simp [js_load, dword]

/-- Running the common load phase computes the effective address in `v0` and
loads the enclosing dword into `v1`. -/
theorem loadPhase_run (imm : BitVec 12) (rs1 : regidx)
    (js : SailJoltState) (val : BitVec 64)
    (hcfg : JoltConfig js.sail)
    (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_dword_translate :
      BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys :
      FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail) :
    ∃ js_load,
      JoltISA.Program.Run (loadPhase imm rs1) js js_load ∧
      js_load.sail = js.sail ∧
      js_load.vregs 0 = load_effective_address val imm ∧
      js_load.vregs 1 =
        loaded_dword_at js.sail (compute_aligned_dword_base_address val imm) := by
  obtain ⟨js_setup, h_setup_succeeds, h_setup_sail, h_setup_v0, h_setup_v1⟩ :=
    loadSetupPhase_run imm rs1 js val hrx
  have h_daddr_aligned :
      AlignedDwordAccess (compute_aligned_dword_base_address val imm) := by
    simpa only [compute_aligned_dword_base_address, load_effective_address,
      aligned_dword_addr_eq] using
      (aligned_dword_addr_is_aligned_dword_access val imm)
  obtain ⟨js_load, h_load_succeeds, h_load_sail, h_load_v0_raw, h_load_v1⟩ :=
    loadDwordPhase_run js js_setup (compute_aligned_dword_base_address val imm)
      hcfg h_setup_sail h_setup_v1 h_daddr_aligned h_dword_translate h_dword_phys
  have h_phase_succeeds :
      JoltISA.Program.Run (loadPhase imm rs1) js js_load := by
    unfold loadPhase
    exact JoltISA.Program.Run.append h_setup_succeeds h_load_succeeds
  have h_load_v0 : js_load.vregs 0 = load_effective_address val imm := by
    rw [h_load_v0_raw, h_setup_v0]
  exact ⟨js_load, h_phase_succeeds, h_load_sail, h_load_v0, h_load_v1⟩

end InstructionEquivalence

end
