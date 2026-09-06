import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.ExpansionBlocks.ALU
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Read
import JoltBytecode.InstructionEquivalence.ProofSupport.Basic

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

/-- Generated load setup: compute the containing aligned dword address with
`VirtualAlignAddr`, load that dword, and continue with `rest`. -/
theorem alignAddrLdBlock (rest : JoltISA.Program)
    (v : JoltISA.VReg) (imm : BitVec 12) (rs1 : regidx)
    (js : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (hbytes :
      MemBytesPresentAt js.sail (compute_aligned_dword_base_address val imm) 8)
    (hload_pmp :
      Assumptions.LoadPmpOk (compute_aligned_dword_base_address val imm) 8 js.sail)
    (hread_mmio :
      Assumptions.NotReadableMmio (compute_aligned_dword_base_address val imm) 8 js.sail)
    (hv : WritableVReg v) :
    ∃ js_load : SailJoltState,
      (JoltISA.execProgram
        (.instr (.VirtualAlignAddr (.vreg v) (.xreg rs1) imm) <|
         .instr (.LD .normal (.vreg v) (.vreg v) 0) rest)).run js =
        (JoltISA.execProgram rest).run js_load ∧
      js_load.sail = js.sail ∧
      js_load.vregs v =
        loaded_dword_at js.sail (compute_aligned_dword_base_address val imm)
          hbytes
          (aligned_dword_addr_is_aligned_dword_access val imm).no_ovf := by
  let daddr := compute_aligned_dword_base_address val imm
  have hdaddr : AlignedDwordAccess daddr := by
    simpa only [daddr] using aligned_dword_addr_is_aligned_dword_access val imm
  let dword := loaded_dword_at js.sail daddr (by simpa only [daddr] using hbytes)
    hdaddr.no_ovf
  let js_addr : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = v then daddr else js.vregs r }
  let js_load : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = v then dword else js_addr.vregs r }
  have halign_value : jolt_virtual_align_addr_value val imm = daddr := by
    simp only [jolt_virtual_align_addr_value, daddr,
      compute_aligned_dword_base_address, load_effective_address,
      Memory.effectiveAddr12,
      show ~~~(7 : BitVec 64) = (-8 : BitVec 64) by decide]
  have halign :
      (JoltISA.execInstr (.VirtualAlignAddr (.vreg v) (.xreg rs1) imm)).run js =
        .ok RETIRE_SUCCESS js_addr := by
    simpa only [js_addr, halign_value] using
      JoltISA.virtual_align_addr_run_vreg_xreg v rs1 imm js val hrx hv
  have hread :
      vmem_read_addr (Virtaddr (js_addr.vregs v +
        sign_extend (m := 64) (0 : BitVec 12))) 0 8
        (Load Data) false false false js_addr.sail =
        .ok (Ok dword) js_addr.sail := by
    have hzero : sign_extend (m := 64) (0 : BitVec 12) = (0 : BitVec 64) := by decide
    have haddr_zero : daddr + sign_extend (m := 64) (0 : BitVec 12) = daddr := by
      rw [hzero]
      norm_num
    have hvaddr : js_addr.vregs v = daddr := by
      simp only [js_addr, if_true]
    have hmemory := aligned_dword_vmem_read_reduces daddr js.sail hpriv hmprv
      hdaddr (by simpa only [daddr] using hbytes)
      (by simpa only [daddr] using hload_pmp)
      (by simpa only [daddr] using hread_mmio)
    rw [show js_addr.sail = js.sail by rfl, hvaddr, haddr_zero]
    simpa only [dword] using hmemory
  have hld_align :
      (js_addr.vregs v + sign_extend (m := 64) (0 : BitVec 12)) &&&
          (7 : BitVec 64) = 0 := by
    have hzero : sign_extend (m := 64) (0 : BitVec 12) = (0 : BitVec 64) := by decide
    have haddr_zero : daddr + sign_extend (m := 64) (0 : BitVec 12) = daddr := by
      rw [hzero]
      norm_num
    have hvaddr : js_addr.vregs v = daddr := by
      simp only [js_addr, if_true]
    rw [hvaddr, haddr_zero]
    exact hdaddr.align
  have hld :
      (JoltISA.execInstr (.LD .normal (.vreg v) (.vreg v) 0)).run js_addr =
        .ok RETIRE_SUCCESS js_load := by
    simpa only [js_load] using
      JoltISA.ld_run_vreg_vreg_from_memory_read (faultClass := .normal)
        v v (0 : BitVec 12)
        js_addr dword hld_align hread hv
  refine ⟨js_load, ?_, rfl, ?_⟩
  · rw [JoltISA.execProgram_instr_run_retire _ _ js js_addr halign]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_addr js_load hld]
  · simp only [js_load, dword, daddr, if_true]

/-- A successful halfword-alignment assertion followed by the generated
`VirtualAlignAddr; LD` setup block. -/
theorem assertHalfwordAlignAddrLdBlockAligned (rest : JoltISA.Program)
    (v : JoltISA.VReg) (imm : BitVec 12) (rs1 : regidx)
    (js : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (halign : load_effective_address val imm &&& (1 : BitVec 64) = 0)
    (hbytes :
      MemBytesPresentAt js.sail (compute_aligned_dword_base_address val imm) 8)
    (hload_pmp :
      Assumptions.LoadPmpOk (compute_aligned_dword_base_address val imm) 8 js.sail)
    (hread_mmio :
      Assumptions.NotReadableMmio (compute_aligned_dword_base_address val imm) 8 js.sail)
    (hv : WritableVReg v) :
    ∃ js_load : SailJoltState,
      (JoltISA.execProgram
        (.instr
          (.VirtualAssertHalfwordAlignment rs1 imm
            (ExceptionType.E_Load_Addr_Align ())) <|
         .instr (.VirtualAlignAddr (.vreg v) (.xreg rs1) imm) <|
         .instr (.LD .normal (.vreg v) (.vreg v) 0) rest)).run js =
        (JoltISA.execProgram rest).run js_load ∧
      js_load.sail = js.sail ∧
      js_load.vregs v =
        loaded_dword_at js.sail (compute_aligned_dword_base_address val imm)
          hbytes
          (aligned_dword_addr_is_aligned_dword_access val imm).no_ovf := by
  have hassert :
      (JoltISA.execInstr
        (.VirtualAssertHalfwordAlignment rs1 imm
          (ExceptionType.E_Load_Addr_Align ()))).run js =
        .ok RETIRE_SUCCESS js := by
    exact JoltISA.virtual_assert_halfword_alignment_run_aligned rs1 imm
      (ExceptionType.E_Load_Addr_Align ()) js val hrx
      (by simpa only [load_effective_address] using halign)
  rcases alignAddrLdBlock rest v imm rs1 js hpriv hmprv val hrx
      hbytes hload_pmp hread_mmio hv with
    ⟨js_load, hrun, hsail, hvalue⟩
  refine ⟨js_load, ?_, hsail, hvalue⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js js hassert]
  exact hrun

/-- A successful word-alignment assertion followed by the generated
`VirtualAlignAddr; LD` setup block. -/
theorem assertWordAlignAddrLdBlockAligned (rest : JoltISA.Program)
    (v : JoltISA.VReg) (imm : BitVec 12) (rs1 : regidx)
    (js : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (halign : load_effective_address val imm &&& (3 : BitVec 64) = 0)
    (hbytes :
      MemBytesPresentAt js.sail (compute_aligned_dword_base_address val imm) 8)
    (hload_pmp :
      Assumptions.LoadPmpOk (compute_aligned_dword_base_address val imm) 8 js.sail)
    (hread_mmio :
      Assumptions.NotReadableMmio (compute_aligned_dword_base_address val imm) 8 js.sail)
    (hv : WritableVReg v) :
    ∃ js_load : SailJoltState,
      (JoltISA.execProgram
        (.instr
          (.VirtualAssertWordAlignment rs1 imm
            (ExceptionType.E_Load_Addr_Align ())) <|
         .instr (.VirtualAlignAddr (.vreg v) (.xreg rs1) imm) <|
         .instr (.LD .normal (.vreg v) (.vreg v) 0) rest)).run js =
        (JoltISA.execProgram rest).run js_load ∧
      js_load.sail = js.sail ∧
      js_load.vregs v =
        loaded_dword_at js.sail (compute_aligned_dword_base_address val imm)
          hbytes
          (aligned_dword_addr_is_aligned_dword_access val imm).no_ovf := by
  have hassert :
      (JoltISA.execInstr
        (.VirtualAssertWordAlignment rs1 imm
          (ExceptionType.E_Load_Addr_Align ()))).run js =
        .ok RETIRE_SUCCESS js := by
    exact JoltISA.virtual_assert_word_alignment_run_aligned rs1 imm
      (ExceptionType.E_Load_Addr_Align ()) js val hrx
      (by simpa only [load_effective_address] using halign)
  rcases alignAddrLdBlock rest v imm rs1 js hpriv hmprv val hrx
      hbytes hload_pmp hread_mmio hv with
    ⟨js_load, hrun, hsail, hvalue⟩
  refine ⟨js_load, ?_, hsail, hvalue⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js js hassert]
  exact hrun

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
    (v0 v1 : JoltISA.VReg) (imm : BitVec 12) (rs1 : regidx)
    (js : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (hbytes :
      MemBytesPresentAt js.sail (compute_aligned_dword_base_address val imm) 8)
    (hload_pmp :
      Assumptions.LoadPmpOk (compute_aligned_dword_base_address val imm) 8 js.sail)
    (hread_mmio :
      Assumptions.NotReadableMmio (compute_aligned_dword_base_address val imm) 8 js.sail)
    (hv0 : WritableVReg v0) (hv1 : WritableVReg v1)
    (hv0_ne_v1 : v0 ≠ v1) :
    ∃ js_load : SailJoltState,
      (JoltISA.execProgram
        (.instr (.ADDI (.vreg v0) (.xreg rs1) imm) <|
         .instr (.ANDI (.vreg v1) (.vreg v0) (-8 : BitVec 12)) <|
         .instr (.LD .normal (.vreg v1) (.vreg v1) 0) rest)).run js =
        (JoltISA.execProgram rest).run js_load ∧
      js_load.sail = js.sail ∧
      js_load.vregs v0 = load_effective_address val imm ∧
      js_load.vregs v1 =
        loaded_dword_at js.sail (compute_aligned_dword_base_address val imm)
          hbytes
          (aligned_dword_addr_is_aligned_dword_access val imm).no_ovf := by
  let ea := load_effective_address val imm
  let daddr := compute_aligned_dword_base_address val imm
  have h_daddr_aligned : AlignedDwordAccess daddr := by
    simpa [daddr, compute_aligned_dword_base_address, load_effective_address,
      aligned_dword_addr_eq] using
      (aligned_dword_addr_is_aligned_dword_access val imm)
  let dword := loaded_dword_at js.sail daddr (by simpa [daddr] using hbytes)
    h_daddr_aligned.no_ovf
  let js0 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = v0 then ea else js.vregs r }
  let js1 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = v1 then daddr else js0.vregs r }
  let js_load : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = v1 then dword else js1.vregs r }
  have haddi :
      (JoltISA.execInstr (.ADDI (.vreg v0) (.xreg rs1) imm)).run js =
        .ok RETIRE_SUCCESS js0 := by
    simpa [js0, ea, load_effective_address] using
      (JoltISA.addi_run_vreg_xreg v0 rs1 imm js val hrx hv0)
  have h8 : sign_extend (m := 64) (-8 : BitVec 12) = (-8 : BitVec 64) := by decide
  have handi :
      (JoltISA.execInstr (.ANDI (.vreg v1) (.vreg v0) (-8 : BitVec 12))).run js0 =
        .ok RETIRE_SUCCESS js1 := by
    simpa [js0, js1, ea, daddr, compute_aligned_dword_base_address,
      load_effective_address, h8] using
      (JoltISA.andi_run_vreg_vreg v1 v0 (-8 : BitVec 12) js0 hv1)
  have hld_read :
      vmem_read_addr (Virtaddr (js1.vregs v1 + sign_extend (m := 64) (0 : BitVec 12))) 0 8
        (Load Data) false false false js1.sail =
        .ok (Ok dword) js1.sail := by
    have h0 : sign_extend (m := 64) (0 : BitVec 12) = (0 : BitVec 64) := by decide
    have haddr0 : daddr + sign_extend (m := 64) (0 : BitVec 12) = daddr := by
      rw [h0]
      norm_num
    have hread := aligned_dword_vmem_read_reduces daddr js.sail hpriv hmprv
      h_daddr_aligned (by simpa [daddr] using hbytes)
      (by simpa [daddr] using hload_pmp)
      (by simpa [daddr] using hread_mmio)
    rw [show js1.sail = js.sail by rfl]
    have hv1_value : js1.vregs v1 = daddr := by
      simp only [js1]
      simp only [if_true]
    rw [hv1_value, haddr0]
    simpa [dword] using hread
  have hld :
      (JoltISA.execInstr (.LD .normal (.vreg v1) (.vreg v1) 0)).run js1 =
        .ok RETIRE_SUCCESS js_load := by
    have hld_align :
        (js1.vregs v1 + sign_extend (m := 64) (0 : BitVec 12)) &&&
            (7 : BitVec 64) =
          0 := by
      have h0 : sign_extend (m := 64) (0 : BitVec 12) = (0 : BitVec 64) := by
        decide
      have hv1_value : js1.vregs v1 = daddr := by
        simp only [js1]
        simp only [if_true]
      have haddr0 : daddr + (0 : BitVec 64) = daddr := by
        norm_num
      rw [hv1_value, h0, haddr0]
      exact h_daddr_aligned.align
    simpa [js_load, dword] using
      (JoltISA.ld_run_vreg_vreg_from_memory_read v1 v1
        (0 : BitVec 12) js1 dword hld_align hld_read hv1)
  refine ⟨js_load, ?_, rfl, ?_, ?_⟩
  · rw [JoltISA.execProgram_instr_run_retire _ _ js js0 haddi]
    rw [JoltISA.execProgram_instr_run_retire _ _ js0 js1 handi]
    rw [JoltISA.execProgram_instr_run_retire _ _ js1 js_load hld]
  · simp only [js_load, js1, js0, ea]
    rw [if_neg hv0_ne_v1]
    rw [if_neg hv0_ne_v1]
    simp only [if_true]
  · simp only [js_load, dword, daddr]
    simp only [if_true]

/-- The setup block with a successful leading halfword load-alignment assertion.

Halfword loads have an explicit virtual assertion before the common dword setup
block.  On the aligned path the assertion retires without changing state, so the
proof immediately reuses `setupBlock`. -/
theorem assertHalfwordSetupBlockAligned (rest : JoltISA.Program)
    (v0 v1 : JoltISA.VReg) (imm : BitVec 12) (rs1 : regidx)
    (js : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (halign : load_effective_address val imm &&& (1 : BitVec 64) = 0)
    (hbytes :
      MemBytesPresentAt js.sail (compute_aligned_dword_base_address val imm) 8)
    (hload_pmp :
      Assumptions.LoadPmpOk (compute_aligned_dword_base_address val imm) 8 js.sail)
    (hread_mmio :
      Assumptions.NotReadableMmio (compute_aligned_dword_base_address val imm) 8 js.sail)
    (hv0 : WritableVReg v0) (hv1 : WritableVReg v1)
    (hv0_ne_v1 : v0 ≠ v1) :
    ∃ js_load : SailJoltState,
      (JoltISA.execProgram
        (.instr (.VirtualAssertHalfwordAlignment rs1 imm (ExceptionType.E_Load_Addr_Align ())) <|
         .instr (.ADDI (.vreg v0) (.xreg rs1) imm) <|
         .instr (.ANDI (.vreg v1) (.vreg v0) (-8 : BitVec 12)) <|
         .instr (.LD .normal (.vreg v1) (.vreg v1) 0) rest)).run js =
        (JoltISA.execProgram rest).run js_load ∧
      js_load.sail = js.sail ∧
      js_load.vregs v0 = load_effective_address val imm ∧
      js_load.vregs v1 =
        loaded_dword_at js.sail (compute_aligned_dword_base_address val imm)
          hbytes
          (aligned_dword_addr_is_aligned_dword_access val imm).no_ovf := by
  have hassert :
      (JoltISA.execInstr
        (.VirtualAssertHalfwordAlignment rs1 imm (ExceptionType.E_Load_Addr_Align ()))).run js =
        .ok RETIRE_SUCCESS js := by
    exact JoltISA.virtual_assert_halfword_alignment_run_aligned rs1 imm
      (ExceptionType.E_Load_Addr_Align ()) js val hrx
      (by simpa [load_effective_address] using halign)
  rcases setupBlock rest v0 v1 imm rs1 js hpriv hmprv val hrx
      hbytes hload_pmp hread_mmio hv0 hv1 hv0_ne_v1 with
    ⟨js_load, hrun, hsail, hv0, hv1⟩
  refine ⟨js_load, ?_, hsail, hv0, hv1⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js js hassert]
  exact hrun

/-- The setup block with a successful leading word load-alignment assertion.

Word loads use the word-alignment variant of the virtual assertion.  On the
aligned path it also retires without changing state, then control passes to the
common dword setup block. -/
theorem assertWordSetupBlockAligned (rest : JoltISA.Program)
    (v0 v1 : JoltISA.VReg) (imm : BitVec 12) (rs1 : regidx)
    (js : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (halign : load_effective_address val imm &&& (3 : BitVec 64) = 0)
    (hbytes :
      MemBytesPresentAt js.sail (compute_aligned_dword_base_address val imm) 8)
    (hload_pmp :
      Assumptions.LoadPmpOk (compute_aligned_dword_base_address val imm) 8 js.sail)
    (hread_mmio :
      Assumptions.NotReadableMmio (compute_aligned_dword_base_address val imm) 8 js.sail)
    (hv0 : WritableVReg v0) (hv1 : WritableVReg v1)
    (hv0_ne_v1 : v0 ≠ v1) :
    ∃ js_load : SailJoltState,
      (JoltISA.execProgram
        (.instr (.VirtualAssertWordAlignment rs1 imm (ExceptionType.E_Load_Addr_Align ())) <|
         .instr (.ADDI (.vreg v0) (.xreg rs1) imm) <|
         .instr (.ANDI (.vreg v1) (.vreg v0) (-8 : BitVec 12)) <|
         .instr (.LD .normal (.vreg v1) (.vreg v1) 0) rest)).run js =
        (JoltISA.execProgram rest).run js_load ∧
      js_load.sail = js.sail ∧
      js_load.vregs v0 = load_effective_address val imm ∧
      js_load.vregs v1 =
        loaded_dword_at js.sail (compute_aligned_dword_base_address val imm)
          hbytes
          (aligned_dword_addr_is_aligned_dword_access val imm).no_ovf := by
  have hassert :
      (JoltISA.execInstr
        (.VirtualAssertWordAlignment rs1 imm (ExceptionType.E_Load_Addr_Align ()))).run js =
        .ok RETIRE_SUCCESS js := by
    exact JoltISA.virtual_assert_word_alignment_run_aligned rs1 imm
      (ExceptionType.E_Load_Addr_Align ()) js val hrx
      (by simpa [load_effective_address] using halign)
  rcases setupBlock rest v0 v1 imm rs1 js hpriv hmprv val hrx
      hbytes hload_pmp hread_mmio hv0 hv1 hv0_ne_v1 with
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
    (v0 v1 tmp : JoltISA.VReg) (imm xorImm : BitVec 12)
    (js js_load : SailJoltState) (val dword : BitVec 64)
    (hload_sail : js_load.sail = js.sail)
    (hload_v0 : js_load.vregs v0 = load_effective_address val imm)
    (hload_v1 : js_load.vregs v1 = dword)
    (hv0 : WritableVReg v0) (hv1 : WritableVReg v1) (htmp : WritableVReg tmp)
    (hv0_ne_v1 : v0 ≠ v1) (hv0_ne_tmp : v0 ≠ tmp) (hv1_ne_tmp : v1 ≠ tmp) :
    ∃ js_shift : SailJoltState,
      (JoltISA.execProgram
        (.instr (.XORI (.vreg v0) (.vreg v0) xorImm) <|
         JoltISA.slliBlock (.vreg v0) (.vreg v0) (3 : BitVec 6) <|
         JoltISA.sllBlock (.vreg v1) (.vreg v1) (.vreg v0) tmp rest)).run js_load =
        (JoltISA.execProgram rest).run js_shift ∧
      js_shift.sail = js.sail ∧
      js_shift.vregs v0 =
        shift_bits_left
          (load_effective_address val imm ^^^ sign_extend (m := 64) xorImm)
          (3 : BitVec 6) ∧
      js_shift.vregs v1 =
        shift_bits_left
          dword
          (Sail.BitVec.extractLsb
            (shift_bits_left
              (load_effective_address val imm ^^^ sign_extend (m := 64) xorImm)
              (3 : BitVec 6)) 5 0) := by
  let xorValue := load_effective_address val imm ^^^ sign_extend (m := 64) xorImm
  let shiftValue := shift_bits_left xorValue (3 : BitVec 6)
  let shiftedDword :=
    shift_bits_left
      dword
      (Sail.BitVec.extractLsb shiftValue 5 0)
  let js_xor : SailJoltState :=
    { sail := js_load.sail
      vregs := fun r => if r = v0 then js_load.vregs v0 ^^^ sign_extend (m := 64) xorImm else js_load.vregs r }
  have hxori :
      (JoltISA.execInstr (.XORI (.vreg v0) (.vreg v0) xorImm)).run js_load =
        .ok RETIRE_SUCCESS js_xor := by
    simpa [js_xor] using
      (JoltISA.execInstr_xori_vreg_vreg_run v0 v0 xorImm js_load hv0)
  have hxv0 : js_xor.vregs v0 = xorValue := by
    simp [js_xor, xorValue, hload_v0]
  have hxv1 : js_xor.vregs v1 = dword := by
    simp [js_xor, hv0_ne_v1.symm, hload_v1]
  obtain ⟨js_slli, hslli_sail, hslli_writes_v0, hslli_preserves, hslli_run⟩ :=
    JoltISA.exists_state_after_slli_block_run_vreg_vreg
      v0 v0 (3 : BitVec 6) js_xor hv0
  have hslli_v0_is_shiftValue : js_slli.vregs v0 = shiftValue := by
    rw [hslli_writes_v0, hxv0]
  have hslli_v1 :
      js_slli.vregs v1 = dword := by
    rw [hslli_preserves v1 hv0_ne_v1.symm]
    exact hxv1
  obtain ⟨js_shift, hsll_sail, hsll_v1, hsll_preserves, hsll_run⟩ :=
    JoltISA.exists_state_after_sll_block_run_vreg_vreg_vreg
      v1 v1 v0 tmp js_slli hv1_ne_tmp hv1 htmp
  refine ⟨js_shift, ?_, ?_, ?_, ?_⟩
  · rw [JoltISA.execProgram_instr_run_retire _ _ js_load js_xor hxori]
    rw [hslli_run
      (JoltISA.sllBlock (.vreg v1) (.vreg v1) (.vreg v0) tmp rest)]
    rw [hsll_run rest]
  · rw [hsll_sail, hslli_sail]
    simp [js_xor, hload_sail]
  · rw [hsll_preserves v0 hv0_ne_v1 hv0_ne_tmp]
    exact hslli_v0_is_shiftValue
  · rw [hsll_v1, hslli_v1, hslli_v0_is_shiftValue]

/-- Final signed extraction block for byte and halfword loads.

Given a boundary state whose `v1` already contains the dword shifted left so
the requested lane sits at the top, `VirtualSRAI rd, v1, shamt` writes the
sign-extended lane to the real destination and continues with `rest`. -/
theorem sraiWriteBlock (rest : JoltISA.Program)
    (rd : regidx) (v1 : JoltISA.VReg) (shamt : BitVec 6)
    (js js_shift : SailJoltState) (shiftedValue : BitVec 64)
    (hshift_sail : js_shift.sail = js.sail)
    (hshift_v1 : js_shift.vregs v1 = shiftedValue) :
    ∃ js_write : SailJoltState,
      (JoltISA.execProgram
        (.instr (.VirtualSRAI (JoltISA.loadDstFor rd) (.vreg v1) (JoltISA.sraiBitmask shamt))
          rest)).run js_shift =
        (JoltISA.execProgram rest).run js_write ∧
      js_write.sail =
        stateAfterWrite js.sail rd (shift_bits_right_arith shiftedValue shamt) := by
  let finalValue := shift_bits_right_arith shiftedValue shamt
  by_cases hx0 : JoltISA.isX0 rd = true
  · obtain ⟨js_write, hrun, _hvalue, _hpres, hsail⟩ :=
      JoltISA.srai_block_run_vreg_vreg_ex JoltISA.rdZeroRewriteVReg v1 shamt js_shift
        (by unfold JoltISA.rdZeroRewriteVReg WritableVReg; decide)
    refine ⟨js_write, ?_, ?_⟩
    · simpa [JoltISA.sraiBlock, JoltISA.loadDstFor, JoltISA.sideEffectingRdZeroDst, hx0]
        using hrun rest
    · rw [hsail, hshift_sail, JoltISA.stateAfterWrite_of_isX0_eq_true hx0 js.sail finalValue]
  · obtain ⟨s_write, hw_write⟩ := wX_shape rd finalValue js.sail
    let js_write : SailJoltState := { sail := s_write, vregs := js_shift.vregs }
    have hsrai :
        (JoltISA.execInstr
          (.VirtualSRAI (JoltISA.loadDstFor rd) (.vreg v1) (JoltISA.sraiBitmask shamt))).run js_shift =
          .ok RETIRE_SUCCESS js_write := by
      have hw_write' :
          wX_bits rd
            (jolt_virtual_srai_value (js_shift.vregs v1) (JoltISA.sraiBitmask shamt))
            js_shift.sail =
            .ok () s_write := by
        rw [hshift_sail, hshift_v1, JoltISA.srai_block_value_eq]
        exact hw_write
      simpa [js_write, JoltISA.loadDstFor, JoltISA.sideEffectingRdZeroDst, hx0] using
        (JoltISA.virtual_srai_run_xreg_vreg rd v1 (JoltISA.sraiBitmask shamt)
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
    (rd : regidx) (v1 : JoltISA.VReg) (shamt : BitVec 6)
    (js js_shift : SailJoltState) (shiftedValue : BitVec 64)
    (hshift_sail : js_shift.sail = js.sail)
    (hshift_v1 : js_shift.vregs v1 = shiftedValue) :
    ∃ js_write : SailJoltState,
      (JoltISA.execProgram
        (.instr (.VirtualSRLI (JoltISA.loadDstFor rd) (.vreg v1) (JoltISA.srliBitmask shamt))
          rest)).run js_shift =
        (JoltISA.execProgram rest).run js_write ∧
      js_write.sail =
        stateAfterWrite js.sail rd (shift_bits_right shiftedValue shamt) := by
  let finalValue := shift_bits_right shiftedValue shamt
  by_cases hx0 : JoltISA.isX0 rd = true
  · let js_write : SailJoltState :=
      { sail := js_shift.sail
        vregs := fun r => if r = JoltISA.rdZeroRewriteVReg then finalValue else js_shift.vregs r }
    have hsrli :
        (JoltISA.execInstr
          (.VirtualSRLI (JoltISA.loadDstFor rd) (.vreg v1) (JoltISA.srliBitmask shamt))).run js_shift =
          .ok RETIRE_SUCCESS js_write := by
      have hvalue :
          jolt_virtual_srli_value (js_shift.vregs v1) (JoltISA.srliBitmask shamt) =
            finalValue := by
        rw [hshift_v1, JoltISA.srli_block_value_eq]
      simpa [js_write, finalValue, JoltISA.loadDstFor, JoltISA.sideEffectingRdZeroDst,
        hx0, hvalue] using
        (JoltISA.virtual_srli_run_vreg_vreg JoltISA.rdZeroRewriteVReg v1
          (JoltISA.srliBitmask shamt) js_shift
          (by unfold JoltISA.rdZeroRewriteVReg WritableVReg; decide))
    refine ⟨js_write, ?_, ?_⟩
    · rw [JoltISA.execProgram_instr_run_retire _ _ js_shift js_write hsrli]
    · rw [hshift_sail, JoltISA.stateAfterWrite_of_isX0_eq_true hx0 js.sail finalValue]
  · obtain ⟨s_write, hw_write⟩ := wX_shape rd finalValue js.sail
    let js_write : SailJoltState := { sail := s_write, vregs := js_shift.vregs }
    have hsrli :
        (JoltISA.execInstr
          (.VirtualSRLI (JoltISA.loadDstFor rd) (.vreg v1) (JoltISA.srliBitmask shamt))).run js_shift =
          .ok RETIRE_SUCCESS js_write := by
      have hw_write' :
          wX_bits rd
            (jolt_virtual_srli_value (js_shift.vregs v1) (JoltISA.srliBitmask shamt))
            js_shift.sail =
            .ok () s_write := by
        rw [hshift_sail, hshift_v1, JoltISA.srli_block_value_eq]
        exact hw_write
      simpa [js_write, JoltISA.loadDstFor, JoltISA.sideEffectingRdZeroDst, hx0] using
        (JoltISA.virtual_srli_run_xreg_vreg rd v1 (JoltISA.srliBitmask shamt)
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
    (v0 v1 tmp : JoltISA.VReg) (imm : BitVec 12)
    (js js_load : SailJoltState) (val dword : BitVec 64)
    (hload_sail : js_load.sail = js.sail)
    (hload_v0 : js_load.vregs v0 = load_effective_address val imm)
    (hload_v1 : js_load.vregs v1 = dword)
    (hv0 : WritableVReg v0) (hv1 : WritableVReg v1) (htmp : WritableVReg tmp)
    (hv0_ne_v1 : v0 ≠ v1) (hv0_ne_tmp : v0 ≠ tmp) (hv1_ne_tmp : v1 ≠ tmp) :
    ∃ (js_logic : SailJoltState) (logic_val : BitVec 64),
      (JoltISA.execProgram
        (JoltISA.slliBlock (.vreg v0) (.vreg v0) (3 : BitVec 6) <|
         JoltISA.srlBlock (.vreg v1) (.vreg v1) (.vreg v0) tmp rest)).run js_load =
        (JoltISA.execProgram rest).run js_logic ∧
      logic_val =
        shift_bits_right
          dword
          (Sail.BitVec.extractLsb
            (shift_bits_left (load_effective_address val imm) (3 : BitVec 6)) 5 0) ∧
      js_logic.sail = js.sail ∧
      js_logic.vregs v1 = logic_val := by
  let logic_val :=
    shift_bits_right
      dword
      (Sail.BitVec.extractLsb
        (shift_bits_left (load_effective_address val imm) (3 : BitVec 6)) 5 0)
  obtain ⟨js_slli, hslli_sail, hslli_writes_v0, hslli_preserves, hslli_run⟩ :=
    JoltISA.exists_state_after_slli_block_run_vreg_vreg
      v0 v0 (3 : BitVec 6) js_load hv0
  have hslli_v0 :
      js_slli.vregs v0 =
        shift_bits_left (load_effective_address val imm) (3 : BitVec 6) := by
    rw [hslli_writes_v0, hload_v0]
  have hslli_v1 : js_slli.vregs v1 = dword := by
    rw [hslli_preserves v1 hv0_ne_v1.symm]
    exact hload_v1
  obtain ⟨js_logic, hsrl_sail, hsrl_v1, _hsrl_preserves, hsrl_run⟩ :=
    JoltISA.exists_state_after_srl_block_run_vreg_vreg_vreg
      v1 v1 v0 tmp js_slli hv1_ne_tmp hv1 htmp
  refine ⟨js_logic, logic_val, ?_, rfl, ?_, ?_⟩
  · rw [hslli_run
      (JoltISA.srlBlock (.vreg v1) (.vreg v1) (.vreg v0) tmp rest)]
    rw [hsrl_run rest]
  · rw [hsrl_sail, hslli_sail, hload_sail]
  · rw [hsrl_v1, hslli_v1, hslli_v0]

/-- Final `LW` sign-extension block.

At this boundary, the preceding virtual `SRL` has left the shifted word in
`v1`.  `VirtualSignExtendWord rd, v1` sign-extends the low 32 bits and writes
the final architectural value. -/
theorem sextwWriteBlock
    (rd : regidx) (v1 : JoltISA.VReg)
    (js js_logic : SailJoltState) (logic_val : BitVec 64)
    (hlogic_sail : js_logic.sail = js.sail)
    (hlogic_v1 : js_logic.vregs v1 = logic_val) :
    ∃ js' : SailJoltState,
      (JoltISA.execProgram
        (.instr (.VirtualSignExtendWord (JoltISA.loadDstFor rd) (.vreg v1)) (.done RETIRE_SUCCESS))).run js_logic =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail =
        stateAfterWrite js.sail rd
          (sign_extend (m := 64) ((Sail.BitVec.extractLsb logic_val 31 0) : BitVec 32)) := by
  let finalValue :=
    sign_extend (m := 64) ((Sail.BitVec.extractLsb logic_val 31 0) : BitVec 32)
  by_cases hx0 : JoltISA.isX0 rd = true
  · let js' : SailJoltState :=
      { sail := js_logic.sail
        vregs := fun r => if r = JoltISA.rdZeroRewriteVReg then finalValue else js_logic.vregs r }
    have hsextw :
        (JoltISA.execInstr (.VirtualSignExtendWord (JoltISA.loadDstFor rd) (.vreg v1))).run js_logic =
          .ok RETIRE_SUCCESS js' := by
      simpa [js', finalValue, JoltISA.loadDstFor, JoltISA.sideEffectingRdZeroDst,
        hx0, hlogic_v1] using
        (JoltISA.virtual_sign_extend_word_run_vreg_vreg JoltISA.rdZeroRewriteVReg v1
          js_logic (by unfold JoltISA.rdZeroRewriteVReg WritableVReg; decide))
    refine ⟨js', ?_, ?_⟩
    · rw [JoltISA.execProgram_instr_run_retire _ _ js_logic js' hsextw]
      rfl
    · rw [hlogic_sail, JoltISA.stateAfterWrite_of_isX0_eq_true hx0 js.sail finalValue]
  · obtain ⟨s_write, hw_write⟩ := wX_shape rd finalValue js.sail
    let js' : SailJoltState := { sail := s_write, vregs := js_logic.vregs }
    have hsextw :
        (JoltISA.execInstr (.VirtualSignExtendWord (JoltISA.loadDstFor rd) (.vreg v1))).run js_logic =
          .ok RETIRE_SUCCESS js' := by
      have hw_write' :
          wX_bits rd
            (sign_extend (m := 64)
              ((Sail.BitVec.extractLsb (js_logic.vregs v1) 31 0) : BitVec 32))
            js_logic.sail = .ok () s_write := by
        rw [hlogic_sail, hlogic_v1]
        exact hw_write
      simpa [js', JoltISA.loadDstFor, JoltISA.sideEffectingRdZeroDst, hx0] using
        (JoltISA.virtual_sign_extend_word_run_xreg_vreg rd v1 js_logic s_write hw_write')
    refine ⟨js', ?_, ?_⟩
    · rw [JoltISA.execProgram_instr_run_retire _ _ js_logic js' hsextw]
      rfl
    · exact wX_bits_eq_stateAfterWrite rd finalValue js.sail s_write hw_write

end LoadProgramBlocks

end
