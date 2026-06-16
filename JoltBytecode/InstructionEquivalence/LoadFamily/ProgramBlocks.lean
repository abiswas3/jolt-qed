import JoltBytecode.JoltISA.Semantics.Instructions
import JoltBytecode.JoltISA.Semantics.ExpansionBlocks.ALU
import JoltBytecode.InstructionEquivalence.LoadDefUtils
import JoltBytecode.InstructionEquivalence.ProofSupport

/-!
# Program blocks for load-family Jolt-ISA proofs

The load-family Rust expansions all have the same control-flow skeleton:

* compute the effective address in virtual register `v0`;
* align that address down and load the enclosing dword into virtual register
  `v1`;
* run a small virtual-register extraction program; and
* write the extracted value back to the architectural destination register.

This file proves those skeleton pieces once, at the level of
`JoltISA.execProgram`.  The instruction files (`LB_main`, `LWU_main`, …) should
then state their public theorems over the handwritten-for-now `JoltISA.Program`
objects and compose these blocks with their instruction-specific pure
bit-vector bridge lemmas.

The statements are intentionally tail-parametric: a block theorem says "after
this prefix retires, execution continues with `rest` from the boundary state."
That is the structured-program version of Ari's three-block proof style, and
it scales to generated programs because the theorem follows the interpreter
rather than an ad hoc do-block.
-/

set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace LoadProgramBlocks

/-- The common dword setup block for load expansions with no leading alignment
assertion.

The prefix

`ADDI v0, rs1, imm; ANDI v1, v0, -8; LD v1, v1, 0`

computes the effective address `ea`, computes the enclosing 8-byte-aligned
dword address, reads that dword, and then continues with the supplied tail.
The resulting boundary facts are the only facts later extraction/writeback
blocks should need: `v0 = ea`, `v1 = loaded_dword_at daddr`, and the Sail state
has not changed. -/
theorem setupBlock (rest : JoltISA.Program)
    (imm : BitVec 12) (rs1 : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail) :
    ∃ js_load : SailJoltState,
      (JoltISA.execProgram
        (.instr (.ADDI (.vreg JoltISA.inlineTmp0) (.xreg rs1) imm) <|
         .instr (.ANDI (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp0) (-8 : BitVec 12)) <|
         .instr (.LD (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp1) 0) rest)).run js =
        (JoltISA.execProgram rest).run js_load ∧
      js_load.sail = js.sail ∧
      js_load.vregs JoltISA.inlineTmp0 = load_effective_address val imm ∧
      js_load.vregs JoltISA.inlineTmp1 =
        loaded_dword_at js.sail (compute_aligned_dword_base_address val imm) := by
  let ea := load_effective_address val imm
  let daddr := compute_aligned_dword_base_address val imm
  let dword := loaded_dword_at js.sail daddr
  let js0 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = JoltISA.inlineTmp0 then ea else js.vregs r }
  let js1 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = JoltISA.inlineTmp1 then daddr else js0.vregs r }
  let js_load : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = JoltISA.inlineTmp1 then dword else js1.vregs r }
  have haddi :
      (JoltISA.execInstr (.ADDI (.vreg JoltISA.inlineTmp0) (.xreg rs1) imm)).run js =
        .ok RETIRE_SUCCESS js0 := by
    simpa [js0, ea, load_effective_address] using
      (JoltISA.addi_run_vreg_xreg JoltISA.inlineTmp0 rs1 imm js val hrx
        (by unfold WritableVReg; decide))
  have h8 : sign_extend (m := 64) (-8 : BitVec 12) = (-8 : BitVec 64) := by decide
  have handi :
      (JoltISA.execInstr (.ANDI (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp0) (-8 : BitVec 12))).run js0 =
        .ok RETIRE_SUCCESS js1 := by
    simpa [js0, js1, ea, daddr, compute_aligned_dword_base_address,
      load_effective_address, h8] using
      (JoltISA.andi_run_vreg_vreg JoltISA.inlineTmp1 JoltISA.inlineTmp0
        (-8 : BitVec 12) js0 (by unfold WritableVReg; decide))
  have h_daddr_aligned : AlignedDwordAccess daddr := by
    simpa [daddr, compute_aligned_dword_base_address, load_effective_address,
      aligned_dword_addr_eq] using
      (aligned_dword_addr_is_aligned_dword_access val imm)
  have hd : DwordLoadEvidence daddr js.sail :=
    dwordLoadEvidence_of_aligned_phys daddr js.sail h_daddr_aligned
      (by simpa [daddr] using h_dword_phys)
  have hld_read :
      vmem_read_addr (Virtaddr (js1.vregs JoltISA.inlineTmp1 + sign_extend (m := 64) (0 : BitVec 12))) 0 8
        (Load Data) false false false js1.sail =
        .ok (Ok dword) js1.sail := by
    have h0 : sign_extend (m := 64) (0 : BitVec 12) = (0 : BitVec 64) := by decide
    have haddr0 : daddr + sign_extend (m := 64) (0 : BitVec 12) = daddr := by
      rw [h0]
      bv_decide
    have hread := aligned_dword_vmem_read_reduces daddr js.sail hcfg hd
    rw [show js1.sail = js.sail by rfl]
    have hv1 : js1.vregs JoltISA.inlineTmp1 = daddr := by
      simp only [js1]
      simp only [if_true]
    rw [hv1, haddr0]
    simpa [dword] using hread
  have hld :
      (JoltISA.execInstr (.LD (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp1) 0)).run js1 =
        .ok RETIRE_SUCCESS js_load := by
    have hld_align :
        (js1.vregs JoltISA.inlineTmp1 + sign_extend (m := 64) (0 : BitVec 12)) &&&
            (7 : BitVec 64) =
          0 := by
      have h0 : sign_extend (m := 64) (0 : BitVec 12) = (0 : BitVec 64) := by
        decide
      have hv1 : js1.vregs JoltISA.inlineTmp1 = daddr := by
        simp only [js1]
        simp only [if_true]
      have haddr0 : daddr + (0 : BitVec 64) = daddr := by
        bv_decide
      rw [hv1, h0, haddr0]
      exact h_daddr_aligned.align
    simpa [js_load, dword] using
      (JoltISA.ld_run_vreg_vreg_from_memory_read JoltISA.inlineTmp1 JoltISA.inlineTmp1
        (0 : BitVec 12) js1 dword hld_align hld_read
        (by unfold WritableVReg; decide))
  refine ⟨js_load, ?_, rfl, ?_, ?_⟩
  · rw [JoltISA.execProgram_instr_run_retire _ _ js js0 haddi]
    rw [JoltISA.execProgram_instr_run_retire _ _ js0 js1 handi]
    rw [JoltISA.execProgram_instr_run_retire _ _ js1 js_load hld]
  · simp only [js_load, js1, js0, ea]
    rw [if_neg (by decide : JoltISA.inlineTmp0 ≠ JoltISA.inlineTmp1)]
    rw [if_neg (by decide : JoltISA.inlineTmp0 ≠ JoltISA.inlineTmp1)]
    simp only [if_true]
  · simp only [js_load, dword, daddr]
    simp only [if_true]

/-- The setup block with a successful leading halfword load-alignment assertion.

Halfword loads have an explicit virtual assertion before the common dword setup
block.  On the aligned path the assertion retires without changing state, so the
proof immediately reuses `setupBlock`. -/
theorem assertHalfwordSetupBlockAligned (rest : JoltISA.Program)
    (imm : BitVec 12) (rs1 : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (halign : load_effective_address val imm &&& (1 : BitVec 64) = 0)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail) :
    ∃ js_load : SailJoltState,
      (JoltISA.execProgram
        (.instr (.VirtualAssertHalfwordAlignment rs1 imm (ExceptionType.E_Load_Addr_Align ())) <|
         .instr (.ADDI (.vreg JoltISA.inlineTmp0) (.xreg rs1) imm) <|
         .instr (.ANDI (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp0) (-8 : BitVec 12)) <|
         .instr (.LD (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp1) 0) rest)).run js =
        (JoltISA.execProgram rest).run js_load ∧
      js_load.sail = js.sail ∧
      js_load.vregs JoltISA.inlineTmp0 = load_effective_address val imm ∧
      js_load.vregs JoltISA.inlineTmp1 =
        loaded_dword_at js.sail (compute_aligned_dword_base_address val imm) := by
  have hassert :
      (JoltISA.execInstr
        (.VirtualAssertHalfwordAlignment rs1 imm (ExceptionType.E_Load_Addr_Align ()))).run js =
        .ok RETIRE_SUCCESS js := by
    exact JoltISA.virtual_assert_halfword_alignment_run_aligned rs1 imm
      (ExceptionType.E_Load_Addr_Align ()) js val hrx
      (by simpa [load_effective_address] using halign)
  rcases setupBlock rest imm rs1 js hcfg val hrx h_dword_phys with
    ⟨js_load, hrun, hsail, hv0, hv1⟩
  refine ⟨js_load, ?_, hsail, hv0, hv1⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js js hassert]
  exact hrun

/-- The setup block with a successful leading word load-alignment assertion.

Word loads use the word-alignment variant of the virtual assertion.  On the
aligned path it also retires without changing state, then control passes to the
common dword setup block. -/
theorem assertWordSetupBlockAligned (rest : JoltISA.Program)
    (imm : BitVec 12) (rs1 : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (halign : load_effective_address val imm &&& (3 : BitVec 64) = 0)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail) :
    ∃ js_load : SailJoltState,
      (JoltISA.execProgram
        (.instr (.VirtualAssertWordAlignment rs1 imm (ExceptionType.E_Load_Addr_Align ())) <|
         .instr (.ADDI (.vreg JoltISA.inlineTmp0) (.xreg rs1) imm) <|
         .instr (.ANDI (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp0) (-8 : BitVec 12)) <|
         .instr (.LD (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp1) 0) rest)).run js =
        (JoltISA.execProgram rest).run js_load ∧
      js_load.sail = js.sail ∧
      js_load.vregs JoltISA.inlineTmp0 = load_effective_address val imm ∧
      js_load.vregs JoltISA.inlineTmp1 =
        loaded_dword_at js.sail (compute_aligned_dword_base_address val imm) := by
  have hassert :
      (JoltISA.execInstr
        (.VirtualAssertWordAlignment rs1 imm (ExceptionType.E_Load_Addr_Align ()))).run js =
        .ok RETIRE_SUCCESS js := by
    exact JoltISA.virtual_assert_word_alignment_run_aligned rs1 imm
      (ExceptionType.E_Load_Addr_Align ()) js val hrx
      (by simpa [load_effective_address] using halign)
  rcases setupBlock rest imm rs1 js hcfg val hrx h_dword_phys with
    ⟨js_load, hrun, hsail, hv0, hv1⟩
  refine ⟨js_load, ?_, hsail, hv0, hv1⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js js hassert]
  exact hrun

/-- A failed leading halfword load-alignment assertion stops the structured program.

This is the generic early-exit fact for halfword/word program theorems.  When
the low bit is nonzero, the assertion returns Sail's load-address-alignment
exception, and `execProgram` does not run the tail. -/
theorem assertHalfwordBlockMisaligned (tail : JoltISA.Program)
    (imm : BitVec 12) (rs1 : regidx)
    (js : SailJoltState)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (hmis : load_effective_address val imm &&& (1 : BitVec 64) ≠ 0) :
    (JoltISA.execProgram
      (.instr (.VirtualAssertHalfwordAlignment rs1 imm (ExceptionType.E_Load_Addr_Align ()))
        tail)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (load_effective_address val imm), ExceptionType.E_Load_Addr_Align ())) js := by
  let e :=
    (Virtaddr (load_effective_address val imm), ExceptionType.E_Load_Addr_Align ())
  have hassert :
      (JoltISA.execInstr
        (.VirtualAssertHalfwordAlignment rs1 imm (ExceptionType.E_Load_Addr_Align ()))).run js =
        .ok (ExecutionResult.Memory_Exception e) js := by
    simpa [e, load_effective_address] using
      (JoltISA.virtual_assert_halfword_alignment_run_misaligned rs1 imm
        (ExceptionType.E_Load_Addr_Align ()) js val hrx
        (by simpa [load_effective_address] using hmis))
  simpa [e] using
    (JoltISA.execProgram_instr_run_memory_exception
      (.VirtualAssertHalfwordAlignment rs1 imm (ExceptionType.E_Load_Addr_Align ()))
      tail js js e hassert)

/-- A failed leading word load-alignment assertion stops the structured program
with Sail's load-address-alignment exception. -/
theorem assertWordBlockMisaligned (tail : JoltISA.Program)
    (imm : BitVec 12) (rs1 : regidx)
    (js : SailJoltState)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (hmis : load_effective_address val imm &&& (3 : BitVec 64) ≠ 0) :
    (JoltISA.execProgram
      (.instr (.VirtualAssertWordAlignment rs1 imm (ExceptionType.E_Load_Addr_Align ()))
        tail)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (load_effective_address val imm), ExceptionType.E_Load_Addr_Align ())) js := by
  let e :=
    (Virtaddr (load_effective_address val imm), ExceptionType.E_Load_Addr_Align ())
  have hassert :
      (JoltISA.execInstr
        (.VirtualAssertWordAlignment rs1 imm (ExceptionType.E_Load_Addr_Align ()))).run js =
        .ok (ExecutionResult.Memory_Exception e) js := by
    simpa [e, load_effective_address] using
      (JoltISA.virtual_assert_word_alignment_run_misaligned rs1 imm
        (ExceptionType.E_Load_Addr_Align ()) js val hrx
        (by simpa [load_effective_address] using hmis))
  simpa [e] using
    (JoltISA.execProgram_instr_run_memory_exception
      (.VirtualAssertWordAlignment rs1 imm (ExceptionType.E_Load_Addr_Align ()))
      tail js js e hassert)

/-- Common virtual extraction block for `LB`, `LBU`, `LH`, `LHU`, and `LWU`.

Starting from the setup boundary (`v0 = ea`, `v1 = dword`), the prefix

`XORI v0, v0, xorImm; slliBlock v0, v0, 3; sllBlock v1, v1, v0 using v2`

moves the requested byte/halfword/word lane to the top of the dword.  The
signedness is not handled here; the final `SRAI` or `SRLI` block decides
whether the top lane is sign-extended or zero-extended into the real
destination. -/
theorem xoriSlliSllBlock (rest : JoltISA.Program)
    (imm xorImm : BitVec 12)
    (js js_load : SailJoltState) (val : BitVec 64)
    (hload_sail : js_load.sail = js.sail)
    (hload_v0 : js_load.vregs JoltISA.inlineTmp0 = load_effective_address val imm)
    (hload_v1 : js_load.vregs JoltISA.inlineTmp1 =
      loaded_dword_at js.sail (compute_aligned_dword_base_address val imm)) :
    ∃ js_shift : SailJoltState,
      (JoltISA.execProgram
        (.instr (.XORI (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp0) xorImm) <|
         JoltISA.slliBlock (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp0) (3 : BitVec 6) <|
         JoltISA.sllBlock (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp0) JoltISA.inlineTmp2 rest)).run js_load =
        (JoltISA.execProgram rest).run js_shift ∧
      js_shift.sail = js.sail ∧
      js_shift.vregs JoltISA.inlineTmp0 =
        shift_bits_left
          (load_effective_address val imm ^^^ sign_extend (m := 64) xorImm)
          (3 : BitVec 6) ∧
      js_shift.vregs JoltISA.inlineTmp1 =
        shift_bits_left
          (loaded_dword_at js.sail (compute_aligned_dword_base_address val imm))
          (Sail.BitVec.extractLsb
            (shift_bits_left
              (load_effective_address val imm ^^^ sign_extend (m := 64) xorImm)
              (3 : BitVec 6)) 5 0) := by
  let xorValue := load_effective_address val imm ^^^ sign_extend (m := 64) xorImm
  let shiftValue := shift_bits_left xorValue (3 : BitVec 6)
  let shiftedDword :=
    shift_bits_left
      (loaded_dword_at js.sail (compute_aligned_dword_base_address val imm))
      (Sail.BitVec.extractLsb shiftValue 5 0)
  let js_xor : SailJoltState :=
    { sail := js_load.sail
      vregs := fun r => if r = JoltISA.inlineTmp0 then js_load.vregs JoltISA.inlineTmp0 ^^^ sign_extend (m := 64) xorImm else js_load.vregs r }
  have hxori :
      (JoltISA.execInstr (.XORI (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp0) xorImm)).run js_load =
        .ok RETIRE_SUCCESS js_xor := by
    simpa [js_xor] using
      (JoltISA.execInstr_xori_vreg_vreg_run JoltISA.inlineTmp0 JoltISA.inlineTmp0
        xorImm js_load (by unfold WritableVReg; decide))
  have hxv0 : js_xor.vregs JoltISA.inlineTmp0 = xorValue := by
    change js_load.vregs JoltISA.inlineTmp0 ^^^ sign_extend (m := 64) xorImm =
      load_effective_address val imm ^^^ sign_extend (m := 64) xorImm
    rw [hload_v0]
  obtain ⟨js_slli, hslli_sail, hslli_writes_v0, hslli_preserves, hslli_run⟩ :=
    JoltISA.exists_state_after_slli_block_run_vreg_vreg
      JoltISA.inlineTmp0 JoltISA.inlineTmp0 (3 : BitVec 6) js_xor
      (by unfold WritableVReg; decide)
  have hslli_v0_is_shiftValue : js_slli.vregs JoltISA.inlineTmp0 = shiftValue := by
    rw [hslli_writes_v0, hxv0]
  have hslli_v1 :
      js_slli.vregs JoltISA.inlineTmp1 =
        loaded_dword_at js.sail (compute_aligned_dword_base_address val imm) := by
    rw [hslli_preserves JoltISA.inlineTmp1 (by decide)]
    change js_load.vregs JoltISA.inlineTmp1 =
      loaded_dword_at js.sail (compute_aligned_dword_base_address val imm)
    exact hload_v1
  obtain ⟨js_shift, hsll_sail, hsll_v1, hsll_preserves, hsll_run⟩ :=
    JoltISA.exists_state_after_sll_block_run_vreg_vreg_vreg
      JoltISA.inlineTmp1 JoltISA.inlineTmp1 JoltISA.inlineTmp0
      JoltISA.inlineTmp2 js_slli (by decide)
      (by unfold WritableVReg; decide) (by unfold WritableVReg; decide)
  refine ⟨js_shift, ?_, ?_, ?_, ?_⟩
  · rw [JoltISA.execProgram_instr_run_retire _ _ js_load js_xor hxori]
    rw [hslli_run
      (JoltISA.sllBlock (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp0) JoltISA.inlineTmp2 rest)]
    rw [hsll_run rest]
  · rw [hsll_sail, hslli_sail]
    simp [js_xor, hload_sail]
  · rw [hsll_preserves JoltISA.inlineTmp0 (by decide) (by decide)]
    exact hslli_v0_is_shiftValue
  · rw [hsll_v1, hslli_v1, hslli_v0_is_shiftValue]

/-- Final signed extraction block for byte and halfword loads.

Given a boundary state whose `v1` already contains the dword shifted left so
the requested lane sits at the top, `VirtualSRAI rd, v1, shamt` writes the
sign-extended lane to the real destination and continues with `rest`. -/
theorem sraiWriteBlock (rest : JoltISA.Program)
    (rd : regidx) (shamt : BitVec 6)
    (js js_shift : SailJoltState) (shiftedValue : BitVec 64)
    (hshift_sail : js_shift.sail = js.sail)
    (hshift_v1 : js_shift.vregs JoltISA.inlineTmp1 = shiftedValue) :
    ∃ js_write : SailJoltState,
      (JoltISA.execProgram
        (.instr (.VirtualSRAI (.xreg rd) (.vreg JoltISA.inlineTmp1) (JoltISA.sraiBitmask shamt))
          rest)).run js_shift =
        (JoltISA.execProgram rest).run js_write ∧
      js_write.sail =
        stateAfterWrite js.sail rd (shift_bits_right_arith shiftedValue shamt) := by
  let finalValue := shift_bits_right_arith shiftedValue shamt
  obtain ⟨s_write, hw_write⟩ := wX_shape rd finalValue js.sail
  let js_write : SailJoltState := { sail := s_write, vregs := js_shift.vregs }
  have hsrai :
      (JoltISA.execInstr
        (.VirtualSRAI (.xreg rd) (.vreg JoltISA.inlineTmp1) (JoltISA.sraiBitmask shamt))).run js_shift =
        .ok RETIRE_SUCCESS js_write := by
    have hw_write' :
        wX_bits rd
          (jolt_virtual_srai_value (js_shift.vregs JoltISA.inlineTmp1) (JoltISA.sraiBitmask shamt))
          js_shift.sail =
          .ok () s_write := by
      rw [hshift_sail, hshift_v1, JoltISA.srai_block_value_eq]
      exact hw_write
    simpa [js_write] using
      (JoltISA.virtual_srai_run_xreg_vreg rd JoltISA.inlineTmp1 (JoltISA.sraiBitmask shamt)
        js_shift s_write hw_write')
  refine ⟨js_write, ?_, ?_⟩
  · rw [JoltISA.execProgram_instr_run_retire _ _ js_shift js_write hsrai]
  · exact wX_bits_eq_stateAfterWrite rd finalValue js.sail s_write hw_write

/-- Final unsigned extraction block for byte, halfword, and unsigned-word
loads.

This is the logical-right-shift sibling of `sraiWriteBlock`.  The input
boundary is the same shifted `v1`; the final instruction uses `SRLI`, so the
written value is zero-extended rather than sign-extended. -/
theorem srliWriteBlock (rest : JoltISA.Program)
    (rd : regidx) (shamt : BitVec 6)
    (js js_shift : SailJoltState) (shiftedValue : BitVec 64)
    (hshift_sail : js_shift.sail = js.sail)
    (hshift_v1 : js_shift.vregs JoltISA.inlineTmp1 = shiftedValue) :
    ∃ js_write : SailJoltState,
      (JoltISA.execProgram
        (.instr (.VirtualSRLI (.xreg rd) (.vreg JoltISA.inlineTmp1) (JoltISA.srliBitmask shamt))
          rest)).run js_shift =
        (JoltISA.execProgram rest).run js_write ∧
      js_write.sail =
        stateAfterWrite js.sail rd (shift_bits_right shiftedValue shamt) := by
  let finalValue := shift_bits_right shiftedValue shamt
  obtain ⟨s_write, hw_write⟩ := wX_shape rd finalValue js.sail
  let js_write : SailJoltState := { sail := s_write, vregs := js_shift.vregs }
  have hsrli :
      (JoltISA.execInstr
        (.VirtualSRLI (.xreg rd) (.vreg JoltISA.inlineTmp1) (JoltISA.srliBitmask shamt))).run js_shift =
        .ok RETIRE_SUCCESS js_write := by
    have hw_write' :
        wX_bits rd
          (jolt_virtual_srli_value (js_shift.vregs JoltISA.inlineTmp1) (JoltISA.srliBitmask shamt))
          js_shift.sail =
          .ok () s_write := by
      rw [hshift_sail, hshift_v1, JoltISA.srli_block_value_eq]
      exact hw_write
    simpa [js_write] using
      (JoltISA.virtual_srli_run_xreg_vreg rd JoltISA.inlineTmp1 (JoltISA.srliBitmask shamt)
        js_shift s_write hw_write')
  refine ⟨js_write, ?_, ?_⟩
  · rw [JoltISA.execProgram_instr_run_retire _ _ js_shift js_write hsrli]
  · exact wX_bits_eq_stateAfterWrite rd finalValue js.sail s_write hw_write

/-- The signed-word (`LW`) extraction block.

`LW` is the odd member of the load family: after the common dword setup it
does not use the `XORI; SLL; SRAI/SRLI` lane-to-top shape.  Instead it shifts
the loaded dword right by `(ea * 8) & 63`, leaves that intermediate value in
`v1`, and lets the final `VirtualSignExtendWord` write the architectural
destination. -/
theorem lwSrlBlock (rest : JoltISA.Program)
    (imm : BitVec 12)
    (js js_load : SailJoltState) (val : BitVec 64)
    (hload_sail : js_load.sail = js.sail)
    (hload_v0 : js_load.vregs JoltISA.inlineTmp0 = load_effective_address val imm)
    (hload_v1 : js_load.vregs JoltISA.inlineTmp1 =
      loaded_dword_at js.sail (compute_aligned_dword_base_address val imm)) :
    ∃ (js_logic : SailJoltState) (logic_val : BitVec 64),
      (JoltISA.execProgram
        (JoltISA.slliBlock (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp0) (3 : BitVec 6) <|
         JoltISA.srlBlock (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp0) JoltISA.inlineTmp2 rest)).run js_load =
        (JoltISA.execProgram rest).run js_logic ∧
      logic_val =
        shift_bits_right
          (loaded_dword_at js.sail (compute_aligned_dword_base_address val imm))
          (Sail.BitVec.extractLsb
            (shift_bits_left (load_effective_address val imm) (3 : BitVec 6)) 5 0) ∧
      js_logic.sail = js.sail ∧
      js_logic.vregs JoltISA.inlineTmp1 = logic_val := by
  let logic_val :=
    shift_bits_right
      (loaded_dword_at js.sail (compute_aligned_dword_base_address val imm))
      (Sail.BitVec.extractLsb
        (shift_bits_left (load_effective_address val imm) (3 : BitVec 6)) 5 0)
  obtain ⟨js_slli, hslli_sail, hslli_writes_v0, hslli_preserves, hslli_run⟩ :=
    JoltISA.exists_state_after_slli_block_run_vreg_vreg
      JoltISA.inlineTmp0 JoltISA.inlineTmp0 (3 : BitVec 6) js_load
      (by unfold WritableVReg; decide)
  have hslli_v0 :
      js_slli.vregs JoltISA.inlineTmp0 =
        shift_bits_left (load_effective_address val imm) (3 : BitVec 6) := by
    rw [hslli_writes_v0, hload_v0]
  have hslli_v1 :
      js_slli.vregs JoltISA.inlineTmp1 =
        loaded_dword_at js.sail (compute_aligned_dword_base_address val imm) := by
    rw [hslli_preserves JoltISA.inlineTmp1 (by decide)]
    exact hload_v1
  obtain ⟨js_logic, hsrl_sail, hsrl_v1, _hsrl_preserves, hsrl_run⟩ :=
    JoltISA.exists_state_after_srl_block_run_vreg_vreg_vreg
      JoltISA.inlineTmp1 JoltISA.inlineTmp1 JoltISA.inlineTmp0
      JoltISA.inlineTmp2 js_slli (by decide)
      (by unfold WritableVReg; decide) (by unfold WritableVReg; decide)
  refine ⟨js_logic, logic_val, ?_, rfl, ?_, ?_⟩
  · rw [hslli_run
      (JoltISA.srlBlock (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp0) JoltISA.inlineTmp2 rest)]
    rw [hsrl_run rest]
  · rw [hsrl_sail, hslli_sail, hload_sail]
  · rw [hsrl_v1, hslli_v1, hslli_v0]

/-- Final `LW` sign-extension block.

At this boundary, the preceding virtual `SRL` has left the shifted word in
`v1`.  `VirtualSignExtendWord rd, v1` sign-extends the low 32 bits and writes
the final architectural value. -/
theorem sextwWriteBlock
    (rd : regidx) (js js_logic : SailJoltState) (logic_val : BitVec 64)
    (hlogic_sail : js_logic.sail = js.sail)
    (hlogic_v1 : js_logic.vregs JoltISA.inlineTmp1 = logic_val) :
    ∃ js' : SailJoltState,
      (JoltISA.execProgram
        (.instr (.VirtualSignExtendWord (.xreg rd) (.vreg JoltISA.inlineTmp1)) (.done RETIRE_SUCCESS))).run js_logic =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail =
        stateAfterWrite js.sail rd
          (sign_extend (m := 64) ((Sail.BitVec.extractLsb logic_val 31 0) : BitVec 32)) := by
  let finalValue :=
    sign_extend (m := 64) ((Sail.BitVec.extractLsb logic_val 31 0) : BitVec 32)
  obtain ⟨s_write, hw_write⟩ := wX_shape rd finalValue js.sail
  let js' : SailJoltState := { sail := s_write, vregs := js_logic.vregs }
  have hsextw :
      (JoltISA.execInstr (.VirtualSignExtendWord (.xreg rd) (.vreg JoltISA.inlineTmp1))).run js_logic =
        .ok RETIRE_SUCCESS js' := by
    have hw_write' :
        wX_bits rd
          (sign_extend (m := 64)
            ((Sail.BitVec.extractLsb (js_logic.vregs JoltISA.inlineTmp1) 31 0) : BitVec 32))
          js_logic.sail = .ok () s_write := by
      rw [hlogic_sail, hlogic_v1]
      exact hw_write
    simpa [js'] using
      (JoltISA.virtual_sign_extend_word_run_xreg_vreg rd JoltISA.inlineTmp1
        js_logic s_write hw_write')
  refine ⟨js', ?_, ?_⟩
  · rw [JoltISA.execProgram_instr_run_retire _ _ js_logic js' hsextw]
    rfl
  · exact wX_bits_eq_stateAfterWrite rd finalValue js.sail s_write hw_write

end LoadProgramBlocks

end
