import JoltBytecode.JoltISA.Environment
import JoltBytecode.JoltISA.Expansions.Load
import JoltBytecode.InstructionEquivalence.Memory.Utils
import JoltBytecode.InstructionEquivalence.LoadDefUtils
import JoltBytecode.InstructionEquivalence.LoadFamily.PhaseHelpers
import JoltBytecode.InstructionEquivalence.LoadFamily.DwordArithmetic
import JoltBytecode.InstructionEquivalence.LoadFamily.ProgramBlocks
import JoltBytecode.InstructionEquivalence.ProofSupport
import Mathlib.Tactic.IntervalCases

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace LW_main

/-!
# LW: Jolt load-word (signed) top-level equivalence

From `tracer/src/instruction/lw.rs::inline_sequence_64`:

    VirtualAssertWordAlignment rs1, imm
    ADDI  v0, rs1, imm
    ANDI  rd, v0, -8
    LD    rd, rd, 0
    SLLI  v0, v0, 3
    SRL   rd, rd, v0
    VirtualSignExtendWord rd, rd, 0

This file proves equivalence for the structured `JoltISA.lwProgram`, using
the bridge lemma (a pure bit-vector identity specialised to LW), the Sail-side
load-pipeline helpers (`LWDwordReadAssumptions` and friends), and separate
aligned/misaligned cases.

## What lives here (by role)

* `jolt_lw_bridge` — specialisation of the DwordArithmetic identities to
  LW: Jolt's logic-phase expression equals `sign_extend (loaded_word_at …)`.
* `LWDwordReadAssumptions` + `lw_dword_*_of_*` — Sail-side structures
  packaging the dword-translate / phys assumptions.
* `execute_LW_reduces`, `execute_LW_misaligned` — Sail-side `execute_LOAD`
  reductions for the two cases.
* `lwProgram_concrete_aligned`, `lwProgram_concrete_misaligned` —
  program-level Jolt execution facts.
* `lwProgram_eq_sail_aligned`, `lwProgram_eq_sail_misaligned`,
  `lwProgram_eq_sail` — main equivalence theorems.

Shared pure bit-vector, memory-shape, and phase-composition helpers live in
`DwordArithmetic.lean`, `LoadDefUtils.lean`, and `PhaseHelpers.lean`.
-/

/-!
## Program-proof architecture

The public Jolt-side object is `JoltISA.lwProgram`. The proof keeps Ari's
three-block decomposition:

* **load block**: alignment guard, effective-address setup, aligned dword load;
* **logic block**: shift the dword so the requested word is in the low 32 bits;
* **write block**: apply the final signed 32-to-64 extension.

The reusable block lemmas live in `LoadFamily.ProgramBlocks`.  They are
deliberately stated for an arbitrary remaining `Program` tail.  That makes
each block a theorem about `execProgram` composition rather than a one-off
tactic script for the full expansion.
-/

/-- **Bridge lemma for LW.** The Jolt logic-phase computation (shift the
    enclosing dword right by `(ea mod 8) * 8`, take the low 32 bits, then
    sign-extend to 64 bits) equals the Sail-side direct word load
    sign-extended to 64 bits. Requires word alignment `halign : ea & 3 = 0`.
    Pure bit-vector algebra — just combines
    `srl_sign_extend_word_extracts_word` with `loaded_word_in_dword`. -/
theorem jolt_lw_bridge (s : SailState) (addr : BitVec 64)
    (halign : addr &&& 3 = 0) :
    (let dword := loaded_dword_at s (addr &&& (-8 : BitVec 64))
     let shift := Sail.BitVec.extractLsb (shift_bits_left addr (3 : BitVec 6)) 5 0
     let shifted := shift_bits_right dword shift
     sign_extend (m := 64) ((Sail.BitVec.extractLsb shifted 31 0) : BitVec 32))
    = sign_extend (m := 64) (loaded_word_at s addr) := by
  simp only [srl_sign_extend_word_extracts_word _ _ halign, ← loaded_word_in_dword _ _ halign]

-- ============================================================================
-- Sail-side dword-read assumption bundles (LW-specific)
-- ============================================================================

/-- LW-flavoured dword read assumptions: the aligned dword base
    `aligned_dword_addr val imm` is bare-translatable and lives in ordinary
    RAM (not MMIO). Currently unused; kept for callers that want a bundled
    assumption type. -/
structure LWDwordReadAssumptions (val : BitVec 64) (imm : BitVec 12) (s : SailState) : Prop where
  translate : BareTranslation (aligned_dword_addr val imm) s
  phys : FlatPhysMem (aligned_dword_addr val imm) 8 s

/-- Promote `LWDwordReadAssumptions` to the generic
    `DwordLoadAssumptions`. -/
theorem lw_dword_load_assumptions_of_local
    (val : BitVec 64) (imm : BitVec 12) (s : SailState)
    (h : LWDwordReadAssumptions val imm s) :
    DwordLoadAssumptions (aligned_dword_addr val imm) s := by
  refine
    { aligned := aligned_dword_addr_is_aligned_dword_access val imm
      translate := h.translate
      phys := h.phys }

/-- Construct `LWDwordReadAssumptions` from the `compute_aligned_dword_base_address`-phrased
    translate / phys hypotheses. (The two addresses are definitionally
    equal; `aligned_dword_addr_eq` bridges the notation.) -/
theorem lw_dword_read_assumptions_of_addr
    (val : BitVec 64)
    (imm : BitVec 12)
    (s : SailState)
    (htranslate : BareTranslation (compute_aligned_dword_base_address val imm) s)
    (hphys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 s) :
    LWDwordReadAssumptions val imm s := by
  have haddr : aligned_dword_addr val imm = compute_aligned_dword_base_address val imm := by
    simp [compute_aligned_dword_base_address, load_effective_address, aligned_dword_addr_eq]
  refine
    { translate := ?_
      phys := ?_ }
  · simpa [haddr] using htranslate
  · simpa [haddr] using hphys

-- ============================================================================
-- Top-level LW ↔ Sail equivalence theorems
-- ============================================================================

/-- Sail-side `execute_LOAD imm rs1 rd false 4` reduces to
    `stateAfterWrite rd (sign_extend (loaded_word_at ea))` under aligned +
    translate + phys + no-overflow assumptions. -/
theorem execute_LW_reduces (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (hload : LoadReadAssumptions (load_effective_address val imm) 4 js.sail)
    (h_no_ovf : (load_effective_address val imm).toNat + 3 < 2 ^ 64) :
    (execute_LOAD imm rs1 rd false 4).run js.sail =
    .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (loaded_word_at js.sail (load_effective_address val imm)))) := by
  unfold execute_LOAD
  simp only [bind, pure]
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  simp (config := { decide := true }) only []
  simp (config := { decide := true }) only [PreSail.assert, EStateM.bind, pure, EStateM.pure,
       EStateM.run, if_true]
  rw [vmem_read_word_reduces imm rs1 js.sail val hrx hload.aligned hload.translate
      (mem_read_4_eq_loaded_word _ js.sail hcfg h_no_ovf hload.phys)]
  simp only [extend_value, Bool.false_eq_true, if_false, EStateM.bind, EStateM.pure]
  obtain ⟨s', hw⟩ := wX_shape rd
    (sign_extend (m := 64) (loaded_word_at js.sail (load_effective_address val imm)))
    js.sail
  rw [hw]
  simp only [RETIRE_SUCCESS]
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

/-- Sail-side `execute_LOAD` on a misaligned input returns the same
    memory-alignment exception as Jolt. Uses
    `access_misaligned_4_unaligned_true` from `MemoryUtils`. -/
theorem execute_LW_misaligned (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (htranslate : BareTranslation (load_effective_address val imm) js.sail)
    (hphys : FlatPhysMem (load_effective_address val imm) 4 js.sail)
    (h_no_ovf : (load_effective_address val imm).toNat + 3 < 2 ^ 64)
    (h_align : load_effective_address val imm &&& 3 ≠ 0)
    :
    (execute_LOAD imm rs1 rd false 4).run js.sail =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (load_effective_address val imm), ExceptionType.E_Load_Addr_Align ())) js.sail := by
  let ea := load_effective_address val imm
  unfold execute_LOAD
  simp only [bind, pure]
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  simp (config := { decide := true }) only []
  simp (config := { decide := true }) only [PreSail.assert, EStateM.bind, pure, EStateM.pure,
       EStateM.run, if_true]
  unfold vmem_read
  unfold SailME.run PreSail.PreSailME.run
  have hmis :
      access_causes_misaligned_exception (Virtaddr ea) 4 false = true := by
    simpa [ea] using access_misaligned_4_unaligned_true ea h_align
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
        ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
        ExceptT.pure, ExceptT.lift,
        MonadLift.monadLift, liftM, monadLift, Functor.map,
        ext_data_get_addr, hrx,
        vmem_read_addr, hmis, ea]
  rfl

/-- Load block for the structured `LW` program.

This lemma is the program-level replacement for the old load phase.  It proves
that, on an aligned input, the prefix

`VirtualAssertLoadAlignment; ADDI; ANDI; LD`

retire-runs to a state where `v0 = ea`, `v1 = loaded_dword_at daddr`, and Sail
state is unchanged.  The statement is tail-parametric: after the block retires,
`execProgram` continues with the supplied `rest`. -/
private theorem lwProgram_load_block_aligned (rest : JoltISA.Program)
    (imm : BitVec 12) (rs1 : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (halign : load_effective_address val imm &&& 3 = 0)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail) :
    ∃ js_load : SailJoltState,
      (JoltISA.execProgram
        (.instr (.VirtualAssertLoadAlignment rs1 imm (3 : BitVec 64)) <|
         .instr (.ADDI (.vreg 0) (.xreg rs1) imm) <|
         .instr (.ANDI (.vreg 1) (.vreg 0) (-8 : BitVec 12)) <|
         .instr (.LD 1 1 0) rest)).run js =
        (JoltISA.execProgram rest).run js_load ∧
      js_load.sail = js.sail ∧
      js_load.vregs 0 = load_effective_address val imm ∧
      js_load.vregs 1 =
        loaded_dword_at js.sail (compute_aligned_dword_base_address val imm) := by
  let ea := load_effective_address val imm
  let daddr := compute_aligned_dword_base_address val imm
  let dword := loaded_dword_at js.sail daddr
  let js0 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (0 : JoltISA.VReg) then ea else js.vregs r }
  let js1 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (1 : JoltISA.VReg) then daddr else js0.vregs r }
  let js_load : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (1 : JoltISA.VReg) then dword else js1.vregs r }
  have hassert :
      (JoltISA.execInstr (.VirtualAssertLoadAlignment rs1 imm (3 : BitVec 64))).run js =
        .ok RETIRE_SUCCESS js := by
    exact JoltISA.execInstr_VirtualAssertLoadAlignment_run_aligned rs1 imm (3 : BitVec 64)
      js val hrx (by simpa [ea, load_effective_address] using halign)
  have haddi :
      (JoltISA.execInstr (.ADDI (.vreg 0) (.xreg rs1) imm)).run js =
        .ok RETIRE_SUCCESS js0 := by
    simpa [js0, ea, load_effective_address] using
      (JoltISA.addi_run_vreg_xreg (0 : JoltISA.VReg) rs1 imm js val hrx)
  have h8 : sign_extend (m := 64) (-8 : BitVec 12) = (-8 : BitVec 64) := by decide
  have handi :
      (JoltISA.execInstr (.ANDI (.vreg 1) (.vreg 0) (-8 : BitVec 12))).run js0 =
        .ok RETIRE_SUCCESS js1 := by
    simpa [js0, js1, ea, daddr, compute_aligned_dword_base_address,
      load_effective_address, h8] using
      (JoltISA.andi_run_vreg_vreg (1 : JoltISA.VReg) (0 : JoltISA.VReg)
        (-8 : BitVec 12) js0)
  have h_daddr_aligned : AlignedDwordAccess daddr := by
    simpa [daddr, compute_aligned_dword_base_address, load_effective_address,
      aligned_dword_addr_eq] using
      (aligned_dword_addr_is_aligned_dword_access val imm)
  have hd : DwordLoadAssumptions daddr js.sail :=
    { aligned := h_daddr_aligned
      translate := by simpa [daddr] using h_dword_translate
      phys := by simpa [daddr] using h_dword_phys }
  have hld_read :
      vmem_read_addr (Virtaddr (js1.vregs 1 + sign_extend (m := 64) (0 : BitVec 12))) 0 8
        (Load Data) false false false js1.sail =
        .ok (Ok dword) js1.sail := by
    have h0 : sign_extend (m := 64) (0 : BitVec 12) = (0 : BitVec 64) := by decide
    have haddr0 : daddr + sign_extend (m := 64) (0 : BitVec 12) = daddr := by
      rw [h0]
      bv_decide
    have hread := aligned_dword_vmem_read_reduces daddr js.sail hcfg hd
    rw [show js1.sail = js.sail by rfl]
    have hv1 : js1.vregs 1 = daddr := by
      simp [js1]
    rw [hv1, haddr0]
    simpa [dword] using hread
  have hld :
      (JoltISA.execInstr (.LD 1 1 0)).run js1 =
        .ok RETIRE_SUCCESS js_load := by
    simpa [js_load, dword] using
      (JoltISA.ld_run_vreg_vreg_from_memory_read (1 : JoltISA.VReg) (1 : JoltISA.VReg)
        (0 : BitVec 12) js1 dword hld_read)
  refine ⟨js_load, ?_, rfl, ?_, ?_⟩
  · rw [JoltISA.execProgram_instr_run_retire _ _ js js hassert]
    rw [JoltISA.execProgram_instr_run_retire _ _ js js0 haddi]
    rw [JoltISA.execProgram_instr_run_retire _ _ js0 js1 handi]
    rw [JoltISA.execProgram_instr_run_retire _ _ js1 js_load hld]
  · simp [js_load, js1, js0, ea]
  · simp [js_load, dword, daddr]

/-- Logic block for the structured `LW` program.

Starting from the load-block boundary (`v0 = ea`, `v1 = dword`), this proves
that

`SLLI; SRL`

continues to the supplied tail after writing the shifted word to real `rd`.
The lemma also records the exact `logic_val`; the pure bridge lemma later
identifies this value with the Sail word load. -/
private theorem lwProgram_logic_block (rest : JoltISA.Program)
    (imm : BitVec 12) (rd : regidx)
    (js js_load : SailJoltState) (val : BitVec 64)
    (hload_sail : js_load.sail = js.sail)
    (hload_v0 : js_load.vregs 0 = load_effective_address val imm)
    (hload_v1 : js_load.vregs 1 =
      loaded_dword_at js.sail (compute_aligned_dword_base_address val imm)) :
    ∃ (js_logic : SailJoltState) (logic_val : BitVec 64),
      (JoltISA.execProgram
        (.instr (.SLLI (.vreg 0) (.vreg 0) (3 : BitVec 6)) <|
         .instr (.SRL (.xreg rd) (.vreg 1) (.vreg 0)) rest)).run js_load =
        (JoltISA.execProgram rest).run js_logic ∧
      logic_val =
        shift_bits_right
          (loaded_dword_at js.sail (compute_aligned_dword_base_address val imm))
          (Sail.BitVec.extractLsb
            (shift_bits_left (load_effective_address val imm) (3 : BitVec 6)) 5 0) ∧
      js_logic.sail = stateAfterWrite js.sail rd logic_val := by
  let logic_val :=
    shift_bits_right
      (loaded_dword_at js.sail (compute_aligned_dword_base_address val imm))
      (Sail.BitVec.extractLsb
        (shift_bits_left (load_effective_address val imm) (3 : BitVec 6)) 5 0)
  let js_shift : SailJoltState :=
    { sail := js_load.sail
      vregs := fun r =>
        if r = (0 : JoltISA.VReg) then shift_bits_left (js_load.vregs 0) (3 : BitVec 6)
        else js_load.vregs r }
  have hslli :
      (JoltISA.execInstr (.SLLI (.vreg 0) (.vreg 0) (3 : BitVec 6))).run js_load =
        .ok RETIRE_SUCCESS js_shift := by
    simpa [js_shift] using
      (JoltISA.slli_run_vreg_vreg (0 : JoltISA.VReg) (0 : JoltISA.VReg)
        (3 : BitVec 6) js_load)
  obtain ⟨s_shift, hw_shift⟩ := wX_shape rd logic_val js.sail
  let js_logic : SailJoltState := { sail := s_shift, vregs := js_shift.vregs }
  have hshift_sail : js_shift.sail = js.sail := by
    simp [js_shift, hload_sail]
  have hshift_v0 :
      js_shift.vregs 0 =
        shift_bits_left (load_effective_address val imm) (3 : BitVec 6) := by
    change shift_bits_left (js_load.vregs (0 : JoltISA.VReg)) (3 : BitVec 6) =
      shift_bits_left (load_effective_address val imm) (3 : BitVec 6)
    rw [hload_v0]
  have hshift_v1 :
      js_shift.vregs 1 =
        loaded_dword_at js.sail (compute_aligned_dword_base_address val imm) := by
    change js_load.vregs (1 : JoltISA.VReg) =
      loaded_dword_at js.sail (compute_aligned_dword_base_address val imm)
    exact hload_v1
  have hsrl :
      (JoltISA.execInstr (.SRL (.xreg rd) (.vreg 1) (.vreg 0))).run js_shift =
        .ok RETIRE_SUCCESS js_logic := by
    have hw_shift' :
        wX_bits rd
          (shift_bits_right (js_shift.vregs 1)
            (Sail.BitVec.extractLsb (js_shift.vregs 0) 5 0))
          js_shift.sail = .ok () s_shift := by
      rw [hshift_sail, hshift_v1, hshift_v0]
      exact hw_shift
    simpa [js_logic] using
      (JoltISA.execInstr_srl_vreg_vreg_xreg_run rd (1 : JoltISA.VReg)
        (0 : JoltISA.VReg) js_shift s_shift hw_shift')
  have hs_logic : js_logic.sail = stateAfterWrite js.sail rd logic_val := by
    exact wX_bits_eq_stateAfterWrite rd logic_val js.sail s_shift hw_shift
  refine ⟨js_logic, logic_val, ?_, rfl, hs_logic⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js_load js_shift hslli]
  rw [JoltISA.execProgram_instr_run_retire _ _ js_shift js_logic hsrl]

/-- Write block for the structured `LW` program.

At this boundary, `SRL` has already written `logic_val` to real `rd`.  `VirtualSignExtendWord`
reads `rd` back, sign-extends the low 32 bits, and writes the final value.
The collapse `stateAfterWrite (stateAfterWrite s rd x) rd y = stateAfterWrite
s rd y` keeps the theorem statement focused on the final architectural state. -/
private theorem lwProgram_write_block
    (rd : regidx) (js js_logic : SailJoltState) (logic_val : BitVec 64)
    (hlogic_sail : js_logic.sail = stateAfterWrite js.sail rd logic_val) :
    ∃ js' : SailJoltState,
      (JoltISA.execProgram
        (.instr (.VirtualSignExtendWord (.xreg rd) (.xreg rd)) (.done RETIRE_SUCCESS))).run js_logic =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail =
        stateAfterWrite js.sail rd
          (sign_extend (m := 64) ((Sail.BitVec.extractLsb logic_val 31 0) : BitVec 32)) := by
  obtain ⟨js', hwrite_sail, hsextw⟩ :=
    JoltISA.exists_state_after_virtual_sign_extend_word_run_xreg_xreg_of_same_register_write
      rd js_logic js.sail logic_val hlogic_sail
  refine ⟨js', ?_, ?_⟩
  · rw [JoltISA.execProgram_instr_run_retire _ _ js_logic js' hsextw]
    rfl
  · exact hwrite_sail

/-- Program-level aligned execution for LW.

This is the design pilot for load-family Jolt-ISA proofs. The program is the
structured bytecode object that Rust extraction should eventually emit. The
proof therefore traces the actual interpreter:

* `VirtualAssertLoadAlignment` checks `ea & 3 = 0`; on the aligned path it retires and
  leaves the whole Jolt state unchanged.
* `ADDI`, `ANDI`, and `LD` build the enclosing aligned dword address and load
  the dword into virtual register `v1`.
* `SLLI` prepares the shift amount, and `SRL` writes the selected word into
  the real destination register.
* `VirtualSignExtendWord` reads that real destination back and sign-extends its low 32 bits.

The theorem is intentionally a trace rather than a black-box simplification:
each local `have` names one bytecode instruction.  That is the pattern we want
for paper-facing proofs, because it lets the reader line the Lean proof up
against the Rust expansion and the Jolt-ISA interpreter. -/
theorem lwProgram_concrete_aligned (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (halign : load_effective_address val imm &&& 3 = 0)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail) :
    ∃ js' : SailJoltState,
      (JoltISA.execProgram (JoltISA.lwProgram imm rs1 rd)).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (loaded_word_at js.sail (load_effective_address val imm))) := by
  let writeTail : JoltISA.Program :=
    .instr (.VirtualSignExtendWord (.xreg rd) (.xreg rd)) (.done RETIRE_SUCCESS)
  let logicTail : JoltISA.Program :=
    .instr (.SLLI (.vreg 0) (.vreg 0) (3 : BitVec 6)) <|
    .instr (.SRL (.xreg rd) (.vreg 1) (.vreg 0)) writeTail
  rcases LoadProgramBlocks.assertSetupBlockAligned logicTail (3 : BitVec 64)
      imm rs1 js hcfg val hrx halign h_dword_translate h_dword_phys with
    ⟨js_load, hload_run, hload_sail, hload_v0, hload_v1⟩
  rcases LoadProgramBlocks.lwSrlBlock writeTail imm rd js js_load val
      hload_sail hload_v0 hload_v1 with
    ⟨js_logic, logic_val, hlogic_run, hlogic_val, hlogic_sail⟩
  rcases LoadProgramBlocks.sextwWriteBlock rd js js_logic logic_val hlogic_sail with
    ⟨js', hwrite_run, hwrite_sail⟩
  refine ⟨js', ?_, ?_⟩
  · unfold JoltISA.lwProgram
    change (JoltISA.execProgram
      (.instr (.VirtualAssertLoadAlignment rs1 imm (3 : BitVec 64)) <|
       .instr (.ADDI (.vreg 0) (.xreg rs1) imm) <|
       .instr (.ANDI (.vreg 1) (.vreg 0) (-8 : BitVec 12)) <|
       .instr (.LD 1 1 0) logicTail)).run js = .ok RETIRE_SUCCESS js'
    rw [hload_run, hlogic_run, hwrite_run]
  · rw [hwrite_sail, hlogic_val]
    exact congrArg (stateAfterWrite js.sail rd)
      (jolt_lw_bridge js.sail (load_effective_address val imm) halign)

/-- Program-level misaligned execution for LW.

This is the control-flow half of the pilot.  The leading `VirtualAssertLoadAlignment`
returns `Memory_Exception`; `execProgram` sees that the result is not
`Retire_Success` and therefore does not execute `ADDI`, `LD`, or the writeback
tail.  This is exactly why `Program.instr` carries retire-checking semantics
instead of being a plain list fold over state updates. -/
theorem lwProgram_concrete_misaligned (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_align : load_effective_address val imm &&& 3 ≠ 0) :
    (JoltISA.execProgram (JoltISA.lwProgram imm rs1 rd)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (load_effective_address val imm), ExceptionType.E_Load_Addr_Align ())) js := by
  let e :=
    (Virtaddr (load_effective_address val imm), ExceptionType.E_Load_Addr_Align ())
  unfold JoltISA.lwProgram
  simpa [e] using
    (LoadProgramBlocks.assertBlockMisaligned
      (.instr (.ADDI (.vreg 0) (.xreg rs1) imm) <|
       .instr (.ANDI (.vreg 1) (.vreg 0) (-8 : BitVec 12)) <|
       .instr (.LD 1 1 0) <|
       .instr (.SLLI (.vreg 0) (.vreg 0) (3 : BitVec 6)) <|
       .instr (.SRL (.xreg rd) (.vreg 1) (.vreg 0)) <|
       .instr (.VirtualSignExtendWord (.xreg rd) (.xreg rd)) <|
       .done RETIRE_SUCCESS)
      (3 : BitVec 64) imm rs1 js val hrx h_align)

/-- Aligned public program theorem for LW. The Jolt side is the structured
Jolt-ISA program. -/
theorem lwProgram_eq_sail_aligned (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail)
    (htranslate : BareTranslation (load_effective_address val imm) js.sail)
    (hphys : FlatPhysMem (load_effective_address val imm) 4 js.sail)
    (h_word_no_ovf : (load_effective_address val imm).toNat + 3 < 2 ^ 64)
    (h_align : load_effective_address val imm &&& 3 = 0) :
    projectResult ((JoltISA.execProgram (JoltISA.lwProgram imm rs1 rd)).run js) =
    (execute_LOAD imm rs1 rd false 4).run js.sail := by
  let ea := load_effective_address val imm
  have hload : LoadReadAssumptions (load_effective_address val imm) 4 js.sail := by
    refine
      { aligned := ?_
        translate := htranslate
        phys := hphys }
    refine
      { misalign := ?_
        split := ?_ }
    · simpa [ea] using access_misaligned_4_aligned_false ea h_align
    · simpa [ea] using split_misaligned_aligned_4 ea h_align
  rcases lwProgram_concrete_aligned imm rs1 rd js hcfg val hrx h_align
      h_dword_translate h_dword_phys with
    ⟨js', hjolt, hjolt_sail⟩
  have hsail := execute_LW_reduces imm rs1 rd js hcfg val hrx hload h_word_no_ovf
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail, hsail]

/-- Misaligned public program theorem for LW.  Both sides return the same
load-address-alignment exception, and the Jolt side does so at the explicit
`VirtualAssertLoadAlignment` instruction. -/
theorem lwProgram_eq_sail_misaligned (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (htranslate : BareTranslation (load_effective_address val imm) js.sail)
    (hphys : FlatPhysMem (load_effective_address val imm) 4 js.sail)
    (h_word_no_ovf : (load_effective_address val imm).toNat + 3 < 2 ^ 64)
    (h_align : load_effective_address val imm &&& 3 ≠ 0) :
    projectResult ((JoltISA.execProgram (JoltISA.lwProgram imm rs1 rd)).run js) =
    (execute_LOAD imm rs1 rd false 4).run js.sail := by
  let ea := load_effective_address val imm
  have hjolt :
      (JoltISA.execProgram (JoltISA.lwProgram imm rs1 rd)).run js =
        .ok (ExecutionResult.Memory_Exception
          (Virtaddr ea, ExceptionType.E_Load_Addr_Align ())) js := by
    simpa [ea] using lwProgram_concrete_misaligned imm rs1 rd js val hrx h_align
  have hsail :
      (execute_LOAD imm rs1 rd false 4).run js.sail =
        .ok (ExecutionResult.Memory_Exception
          (Virtaddr ea, ExceptionType.E_Load_Addr_Align ())) js.sail := by
    simpa [ea] using
      (execute_LW_misaligned imm rs1 rd js hcfg val hrx htranslate hphys
        h_word_no_ovf h_align)
  rw [hjolt]
  simp only [projectResult, project]
  symm
  exact hsail

/-- **Main program theorem for LW.**  The structured Jolt-ISA expansion
`lwProgram`, interpreted by `execProgram`, agrees with Sail's `execute_LOAD`
for signed word loads.  The proof dispatches on the same alignment predicate
that the first Jolt virtual instruction checks. -/
theorem lwProgram_eq_sail (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail)
    (htranslate : BareTranslation (load_effective_address val imm) js.sail)
    (hphys : FlatPhysMem (load_effective_address val imm) 4 js.sail)
    (h_word_no_ovf : (load_effective_address val imm).toNat + 3 < 2 ^ 64) :
    projectResult ((JoltISA.execProgram (JoltISA.lwProgram imm rs1 rd)).run js) =
    (execute_LOAD imm rs1 rd false 4).run js.sail := by
  let ea := load_effective_address val imm
  by_cases h_align : ea &&& 3 = 0
  · exact lwProgram_eq_sail_aligned imm rs1 rd js hcfg val hrx
      h_dword_translate h_dword_phys htranslate hphys h_word_no_ovf h_align
  · exact lwProgram_eq_sail_misaligned imm rs1 rd js hcfg val hrx
      htranslate hphys h_word_no_ovf h_align

end LW_main
