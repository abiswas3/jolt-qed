import JoltBytecode.JoltISA.Expansions.Store
import JoltBytecode.JoltISA.Semantics.Instructions
import JoltBytecode.InstructionEquivalence.LoadDefUtils
import JoltBytecode.InstructionEquivalence.StoreFamily.Splice
import JoltBytecode.InstructionEquivalence.ProofSupport

/-!
# Program blocks for store-family Jolt-ISA proofs

The store-family programs have the same shape as load programs until the
middle dword operation:

* compute `ea = rs1 + imm` in virtual register `v0`;
* compute the enclosing dword address in virtual register `v1`;
* load the current dword into virtual register `v2`;
* splice the low byte/halfword/word of `rs2` into that dword; and
* write the spliced dword back with `SD`.

This file is the store analogue of `LoadFamily/ProgramBlocks.lean`.  The block
theorems are tail-parametric so the public instruction files can follow the
Rust program top-to-bottom while keeping each proof phase small enough to read.
-/

set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace StoreProgramBlocks

private theorem shift_bits_left_eq_shiftLeft_nat (x : BitVec 64) (sh : BitVec 6) :
    shift_bits_left x sh = x <<< sh.toNat := by
  rfl

private theorem setWidth6_eq_extractLsb_5_0 (v : BitVec 64) :
    v.setWidth 6 = Sail.BitVec.extractLsb v 5 0 := by
  unfold Sail.BitVec.extractLsb
  ext i
  simp

private theorem shift6_eq_of_offset_byte (ea base : BitVec 64)
    (hsetup : StoreSplice.ByteStoreSetup ea base) :
    Sail.BitVec.extractLsb (shift_bits_left ea (3 : BitVec 6)) 5 0 =
      BitVec.ofNat 6 (((ea - base).toNat) * 8) := by
  rw [← setWidth6_eq_extractLsb_5_0 (shift_bits_left ea (3 : BitVec 6))]
  rcases hsetup.offset_cases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · have hsub : ea - base = (0 : BitVec 64) := by
      apply BitVec.eq_of_toNat_eq
      simpa using h0
    have hea : ea = base := by
      have := hsub
      bv_decide
    rw [h0, hea, hsetup.base_is_aligned]
    unfold shift_bits_left
    bv_decide
  · have hsub : ea - base = (1 : BitVec 64) := by
      apply BitVec.eq_of_toNat_eq
      simpa using h1
    have hea : ea = base + (1 : BitVec 64) := by
      have := hsub
      bv_decide
    rw [h1, hea, hsetup.base_is_aligned]
    unfold shift_bits_left
    bv_decide
  · have hsub : ea - base = (2 : BitVec 64) := by
      apply BitVec.eq_of_toNat_eq
      simpa using h2
    have hea : ea = base + (2 : BitVec 64) := by
      have := hsub
      bv_decide
    rw [h2, hea, hsetup.base_is_aligned]
    unfold shift_bits_left
    bv_decide
  · have hsub : ea - base = (3 : BitVec 64) := by
      apply BitVec.eq_of_toNat_eq
      simpa using h3
    have hea : ea = base + (3 : BitVec 64) := by
      have := hsub
      bv_decide
    rw [h3, hea, hsetup.base_is_aligned]
    unfold shift_bits_left
    bv_decide
  · have hsub : ea - base = (4 : BitVec 64) := by
      apply BitVec.eq_of_toNat_eq
      simpa using h4
    have hea : ea = base + (4 : BitVec 64) := by
      have := hsub
      bv_decide
    rw [h4, hea, hsetup.base_is_aligned]
    unfold shift_bits_left
    bv_decide
  · have hsub : ea - base = (5 : BitVec 64) := by
      apply BitVec.eq_of_toNat_eq
      simpa using h5
    have hea : ea = base + (5 : BitVec 64) := by
      have := hsub
      bv_decide
    rw [h5, hea, hsetup.base_is_aligned]
    unfold shift_bits_left
    bv_decide
  · have hsub : ea - base = (6 : BitVec 64) := by
      apply BitVec.eq_of_toNat_eq
      simpa using h6
    have hea : ea = base + (6 : BitVec 64) := by
      have := hsub
      bv_decide
    rw [h6, hea, hsetup.base_is_aligned]
    unfold shift_bits_left
    bv_decide
  · have hsub : ea - base = (7 : BitVec 64) := by
      apply BitVec.eq_of_toNat_eq
      simpa using h7
    have hea : ea = base + (7 : BitVec 64) := by
      have := hsub
      bv_decide
    rw [h7, hea, hsetup.base_is_aligned]
    unfold shift_bits_left
    bv_decide

private theorem shift6_eq_of_offset_halfword (ea base : BitVec 64)
    (hsetup : StoreSplice.HalfwordStoreSetup ea base) :
    Sail.BitVec.extractLsb (shift_bits_left ea (3 : BitVec 6)) 5 0 =
      BitVec.ofNat 6 (((ea - base).toNat) * 8) := by
  have hbyte : StoreSplice.ByteStoreSetup ea base :=
    { base_is_aligned := hsetup.base_is_aligned
      no_ovf := hsetup.no_ovf
      ea_toNat := hsetup.ea_toNat
      offset_cases := by
        rcases hsetup.offset_cases with h0 | h2 | h4 | h6
        · exact Or.inl h0
        · exact Or.inr (Or.inr (Or.inl h2))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6))))))
    }
  exact shift6_eq_of_offset_byte ea base hbyte

private theorem shift6_eq_of_offset_word (ea base : BitVec 64)
    (hsetup : StoreSplice.WordStoreSetup ea base) :
    Sail.BitVec.extractLsb (shift_bits_left ea (3 : BitVec 6)) 5 0 =
      BitVec.ofNat 6 (((ea - base).toNat) * 8) := by
  have hbyte : StoreSplice.ByteStoreSetup ea base :=
    { base_is_aligned := hsetup.base_is_aligned
      no_ovf := hsetup.no_ovf
      ea_toNat := hsetup.ea_toNat
      offset_cases := by
        rcases hsetup.offset_cases with h0 | h4
        · exact Or.inl h0
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4))))
    }
  exact shift6_eq_of_offset_byte ea base hbyte

private theorem byteSplice_eq_sequence
    (dword_orig rs2_val : BitVec 64) (off : Nat)
    (hoff :
      off = 0 ∨ off = 1 ∨ off = 2 ∨ off = 3 ∨
      off = 4 ∨ off = 5 ∨ off = 6 ∨ off = 7) :
    dword_orig ^^^
        ((dword_orig ^^^ shift_bits_left rs2_val (BitVec.ofNat 6 (off * 8))) &&&
          shift_bits_left (0x00000000000000FF : BitVec 64) (BitVec.ofNat 6 (off * 8))) =
      StoreSplice.byteSplice dword_orig (Sail.BitVec.extractLsb rs2_val 7 0) (off * 8) := by
  rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [StoreSplice.byteSplice, shift_bits_left_eq_shiftLeft_nat, Sail.BitVec.extractLsb]
    bv_decide

private theorem halfwordSplice_eq_sequence
    (dword_orig rs2_val : BitVec 64) (off : Nat)
    (hoff : off = 0 ∨ off = 2 ∨ off = 4 ∨ off = 6) :
    dword_orig ^^^
        ((dword_orig ^^^ shift_bits_left rs2_val (BitVec.ofNat 6 (off * 8))) &&&
          shift_bits_left (0x000000000000FFFF : BitVec 64) (BitVec.ofNat 6 (off * 8))) =
      StoreSplice.halfwordSplice dword_orig (Sail.BitVec.extractLsb rs2_val 15 0) (off * 8) := by
  rcases hoff with rfl | rfl | rfl | rfl
  all_goals
    simp [StoreSplice.halfwordSplice, shift_bits_left_eq_shiftLeft_nat, Sail.BitVec.extractLsb]
    bv_decide

private theorem wordSplice_eq_sequence
    (dword_orig rs2_val : BitVec 64) (off : Nat)
    (hoff : off = 0 ∨ off = 4) :
    dword_orig ^^^
        ((dword_orig ^^^ shift_bits_left rs2_val (BitVec.ofNat 6 (off * 8))) &&&
          shift_bits_left (0x00000000FFFFFFFF : BitVec 64) (BitVec.ofNat 6 (off * 8))) =
      StoreSplice.wordSplice dword_orig (Sail.BitVec.extractLsb rs2_val 31 0) (off * 8) := by
  rcases hoff with rfl | rfl
  all_goals
    simp [StoreSplice.wordSplice, shift_bits_left_eq_shiftLeft_nat, Sail.BitVec.extractLsb]
    bv_decide

private theorem shift_bits_right_allOnes_32 :
    shift_bits_right (-1 : BitVec 64) (32 : BitVec 6) =
      (0x00000000FFFFFFFF : BitVec 64) := by
  native_decide

private theorem shift_bits_right_signExtend_neg_one_32 :
    shift_bits_right (sign_extend (m := 64) (-1 : BitVec 12)) (32 : BitVec 6) =
      (0x00000000FFFFFFFF : BitVec 64) := by
  native_decide

private theorem shift_bits_right_signExtend_4095_32 :
    shift_bits_right (sign_extend (m := 64) (4095#12)) (32#6) =
      (0x00000000FFFFFFFF : BitVec 64) := by
  native_decide

private theorem zero_or_signExtend_neg_one :
    (0#64) ||| sign_extend (m := 64) (-1 : BitVec 12) = (-1 : BitVec 64) := by
  native_decide

/-!
## The `SW` mask prefix

The Rust `SW` expansion does not use `LUI` to materialize the 32-bit mask.
Instead it runs the four-instruction prefix

```
SLLI v0, v0, 3
ORI  v3, x0, -1
SRLI v3, v3, 32
SLL  v3, v3, v0
```

The following private definitions name the exact intermediate states for this
prefix.  Naming the states keeps the public block theorem below readable and,
more importantly, prevents the proof from becoming one large monadic reduction
that is hard for Lean to elaborate.
-/

private def swWordShiftState (js : SailJoltState) : SailJoltState :=
  { sail := js.sail
    vregs := fun r =>
      if r = (0 : JoltISA.VReg) then
        shift_bits_left (js.vregs (0 : JoltISA.VReg)) (3 : BitVec 6)
      else js.vregs r }

private def swWordOnesState (js : SailJoltState) : SailJoltState :=
  { sail := js.sail
    vregs := fun r =>
      if r = (3 : JoltISA.VReg) then
        (0#64) ||| sign_extend (m := 64) (-1 : BitVec 12)
      else js.vregs r }

private def swWordBaseMaskState (js : SailJoltState) : SailJoltState :=
  { sail := js.sail
    vregs := fun r =>
      if r = (3 : JoltISA.VReg) then
        shift_bits_right (js.vregs (3 : JoltISA.VReg)) (32 : BitVec 6)
      else js.vregs r }

private def swWordMaskState (js : SailJoltState) : SailJoltState :=
  { sail := js.sail
    vregs := fun r =>
      if r = (3 : JoltISA.VReg) then
        shift_bits_left (js.vregs (3 : JoltISA.VReg))
          (Sail.BitVec.extractLsb (js.vregs (0 : JoltISA.VReg)) 5 0)
      else js.vregs r }

/-- First `SW` mask-prefix step: multiply the byte address by eight, leaving
the bit offset in `v0`. -/
private theorem swWordShiftStep (rest : JoltISA.Program) (js : SailJoltState) :
    (JoltISA.execProgram
      (.instr (.SLLI (.vreg 0) (.vreg 0) (3 : BitVec 6)) rest)).run js =
      (JoltISA.execProgram rest).run (swWordShiftState js) := by
  have h :
      (JoltISA.execInstr (.SLLI (.vreg 0) (.vreg 0) (3 : BitVec 6))).run js =
        .ok RETIRE_SUCCESS (swWordShiftState js) := by
    simpa [swWordShiftState] using
      (JoltISA.slli_run_vreg_vreg (0 : JoltISA.VReg) (0 : JoltISA.VReg)
        (3 : BitVec 6) js)
  exact JoltISA.execProgram_instr_run_retire _ _ js (swWordShiftState js) h

/-- Second `SW` mask-prefix step: read architectural `x0` and OR with `-1`,
materializing all ones in `v3`. -/
private theorem swWordOnesStep (rest : JoltISA.Program) (js : SailJoltState)
    (hx0 : rX_bits (regidx.Regidx 0) js.sail = .ok 0#64 js.sail) :
    (JoltISA.execProgram
      (.instr (.ORI (.vreg 3) (.xreg (regidx.Regidx 0)) (-1 : BitVec 12)) rest)).run js =
      (JoltISA.execProgram rest).run (swWordOnesState js) := by
  have h :
      (JoltISA.execInstr (.ORI (.vreg 3) (.xreg (regidx.Regidx 0)) (-1 : BitVec 12))).run js =
        .ok RETIRE_SUCCESS (swWordOnesState js) := by
    simpa [swWordOnesState] using
      (JoltISA.ori_run_vreg_xreg (3 : JoltISA.VReg) (regidx.Regidx 0)
        (-1 : BitVec 12) js (0#64) hx0)
  exact JoltISA.execProgram_instr_run_retire _ _ js (swWordOnesState js) h

/-- Third `SW` mask-prefix step: logical-right-shift all ones by 32, producing
the unshifted 32-bit store mask. -/
private theorem swWordBaseMaskStep (rest : JoltISA.Program) (js : SailJoltState) :
    (JoltISA.execProgram
      (.instr (.SRLI (.vreg 3) (.vreg 3) (32 : BitVec 6)) rest)).run js =
      (JoltISA.execProgram rest).run (swWordBaseMaskState js) := by
  have h :
      (JoltISA.execInstr (.SRLI (.vreg 3) (.vreg 3) (32 : BitVec 6))).run js =
        .ok RETIRE_SUCCESS (swWordBaseMaskState js) := by
    simpa [swWordBaseMaskState] using
      (JoltISA.execInstr_srli_vreg_vreg_run (3 : JoltISA.VReg) (3 : JoltISA.VReg)
        (32 : BitVec 6) js)
  exact JoltISA.execProgram_instr_run_retire _ _ js (swWordBaseMaskState js) h

/-- Fourth `SW` mask-prefix step: shift the 32-bit mask into the selected word
lane. -/
private theorem swWordMaskShiftStep (rest : JoltISA.Program) (js : SailJoltState) :
    (JoltISA.execProgram
      (.instr (.SLL (.vreg 3) (.vreg 3) (.vreg 0)) rest)).run js =
      (JoltISA.execProgram rest).run (swWordMaskState js) := by
  have h :
      (JoltISA.execInstr (.SLL (.vreg 3) (.vreg 3) (.vreg 0))).run js =
        .ok RETIRE_SUCCESS (swWordMaskState js) := by
    simpa [swWordMaskState] using
      (JoltISA.execInstr_sll_vreg_vreg_vreg_run (3 : JoltISA.VReg) (3 : JoltISA.VReg)
        (0 : JoltISA.VReg) js)
  exact JoltISA.execProgram_instr_run_retire _ _ js (swWordMaskState js) h

private theorem swWordMaskState_sail (js : SailJoltState) :
    (swWordMaskState (swWordBaseMaskState (swWordOnesState (swWordShiftState js)))).sail =
      js.sail := by
  rfl

private theorem swWordMaskState_v0 (js : SailJoltState) :
    (swWordMaskState (swWordBaseMaskState (swWordOnesState (swWordShiftState js)))).vregs
        (0 : JoltISA.VReg) =
      shift_bits_left (js.vregs (0 : JoltISA.VReg)) (3 : BitVec 6) := by
  simp [swWordMaskState, swWordBaseMaskState, swWordOnesState, swWordShiftState]

private theorem swWordMaskState_v1 (js : SailJoltState) :
    (swWordMaskState (swWordBaseMaskState (swWordOnesState (swWordShiftState js)))).vregs
        (1 : JoltISA.VReg) =
      js.vregs (1 : JoltISA.VReg) := by
  simp [swWordMaskState, swWordBaseMaskState, swWordOnesState, swWordShiftState]

private theorem swWordMaskState_v2 (js : SailJoltState) :
    (swWordMaskState (swWordBaseMaskState (swWordOnesState (swWordShiftState js)))).vregs
        (2 : JoltISA.VReg) =
      js.vregs (2 : JoltISA.VReg) := by
  simp [swWordMaskState, swWordBaseMaskState, swWordOnesState, swWordShiftState]

private theorem swWordMaskState_v3 (js : SailJoltState) :
    (swWordMaskState (swWordBaseMaskState (swWordOnesState (swWordShiftState js)))).vregs
        (3 : JoltISA.VReg) =
      shift_bits_left (0x00000000FFFFFFFF : BitVec 64)
        (Sail.BitVec.extractLsb
          (shift_bits_left (js.vregs (0 : JoltISA.VReg)) (3 : BitVec 6)) 5 0) := by
  simp [swWordMaskState, swWordBaseMaskState, swWordOnesState, swWordShiftState,
    shift_bits_right_signExtend_4095_32]

/-- Common setup block for store expansions.

`ADDI v0, rs1, imm; ANDI v1, v0, -8; LD v2, v1, 0` computes the effective
address, computes the enclosing dword base, and loads that dword into `v2`.
The boundary facts are exactly the store-side inputs needed by later splice
blocks. -/
theorem setupBlock (rest : JoltISA.Program)
    (imm : BitVec 12) (rs1 : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail) :
    ∃ js_load : SailJoltState,
      (JoltISA.execProgram
        (.instr (.ADDI (.vreg 0) (.xreg rs1) imm) <|
         .instr (.ANDI (.vreg 1) (.vreg 0) (-8 : BitVec 12)) <|
         .instr (.LD 2 1 0) rest)).run js =
        (JoltISA.execProgram rest).run js_load ∧
      js_load.sail = js.sail ∧
      js_load.vregs 0 = load_effective_address val imm ∧
      js_load.vregs 1 = compute_aligned_dword_base_address val imm ∧
      js_load.vregs 2 =
        loaded_dword_at js.sail (compute_aligned_dword_base_address val imm) := by
  let ea := load_effective_address val imm
  let base := compute_aligned_dword_base_address val imm
  let dword := loaded_dword_at js.sail base
  let js0 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (0 : JoltISA.VReg) then ea else js.vregs r }
  let js1 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (1 : JoltISA.VReg) then base else js0.vregs r }
  let js_load : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (2 : JoltISA.VReg) then dword else js1.vregs r }
  have haddi :
      (JoltISA.execInstr (.ADDI (.vreg 0) (.xreg rs1) imm)).run js =
        .ok RETIRE_SUCCESS js0 := by
    simpa [js0, ea, load_effective_address] using
      (JoltISA.addi_run_vreg_xreg (0 : JoltISA.VReg) rs1 imm js val hrx)
  have h8 : sign_extend (m := 64) (-8 : BitVec 12) = (-8 : BitVec 64) := by decide
  have handi :
      (JoltISA.execInstr (.ANDI (.vreg 1) (.vreg 0) (-8 : BitVec 12))).run js0 =
        .ok RETIRE_SUCCESS js1 := by
    simpa [js0, js1, ea, base, compute_aligned_dword_base_address,
      load_effective_address, h8] using
      (JoltISA.andi_run_vreg_vreg (1 : JoltISA.VReg) (0 : JoltISA.VReg)
        (-8 : BitVec 12) js0)
  have h_base_aligned : AlignedDwordAccess base := by
    simpa [base, compute_aligned_dword_base_address, load_effective_address,
      aligned_dword_addr_eq] using
      (aligned_dword_addr_is_aligned_dword_access val imm)
  have hd : DwordLoadAssumptions base js.sail :=
    { aligned := h_base_aligned
      translate := by simpa [base] using h_dword_translate
      phys := by simpa [base] using h_dword_phys }
  have hld_read :
      vmem_read_addr (Virtaddr (js1.vregs 1 + sign_extend (m := 64) (0 : BitVec 12))) 0 8
        (Load Data) false false false js1.sail =
        .ok (Ok dword) js1.sail := by
    have h0 : sign_extend (m := 64) (0 : BitVec 12) = (0 : BitVec 64) := by decide
    have haddr0 : base + sign_extend (m := 64) (0 : BitVec 12) = base := by
      rw [h0]
      bv_decide
    have hread := aligned_dword_vmem_read_reduces base js.sail hcfg hd
    rw [show js1.sail = js.sail by rfl]
    have hv1 : js1.vregs 1 = base := by
      simp [js1]
    rw [hv1, haddr0]
    simpa [dword] using hread
  have hld :
      (JoltISA.execInstr (.LD 2 1 0)).run js1 =
        .ok RETIRE_SUCCESS js_load := by
    simpa [js_load, dword] using
      (JoltISA.ld_run_vreg_vreg_from_memory_read (2 : JoltISA.VReg) (1 : JoltISA.VReg)
        (0 : BitVec 12) js1 dword hld_read)
  refine ⟨js_load, ?_, rfl, ?_, ?_, ?_⟩
  · rw [JoltISA.execProgram_instr_run_retire _ _ js js0 haddi]
    rw [JoltISA.execProgram_instr_run_retire _ _ js0 js1 handi]
    rw [JoltISA.execProgram_instr_run_retire _ _ js1 js_load hld]
  · simp [js_load, js1, js0, ea]
  · simp [js_load, js1, base]
  · simp [js_load, dword, base]

/-- Successful leading store-alignment assertion followed by the common setup
block.  The assertion does not change state on the aligned path. -/
theorem assertSetupBlockAligned (rest : JoltISA.Program)
    (mask : BitVec 64) (imm : BitVec 12) (rs1 : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (halign : load_effective_address val imm &&& mask = 0)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail) :
    ∃ js_load : SailJoltState,
      (JoltISA.execProgram
        (.instr (.VirtualAssertStoreAlignment rs1 imm mask) <|
         .instr (.ADDI (.vreg 0) (.xreg rs1) imm) <|
         .instr (.ANDI (.vreg 1) (.vreg 0) (-8 : BitVec 12)) <|
         .instr (.LD 2 1 0) rest)).run js =
        (JoltISA.execProgram rest).run js_load ∧
      js_load.sail = js.sail ∧
      js_load.vregs 0 = load_effective_address val imm ∧
      js_load.vregs 1 = compute_aligned_dword_base_address val imm ∧
      js_load.vregs 2 =
        loaded_dword_at js.sail (compute_aligned_dword_base_address val imm) := by
  have hassert :
      (JoltISA.execInstr (.VirtualAssertStoreAlignment rs1 imm mask)).run js =
        .ok RETIRE_SUCCESS js := by
    exact JoltISA.execInstr_VirtualAssertStoreAlignment_run_aligned rs1 imm mask
      js val hrx (by simpa [load_effective_address] using halign)
  rcases setupBlock rest imm rs1 js hcfg val hrx h_dword_translate h_dword_phys with
    ⟨js_load, hrun, hsail, hv0, hv1, hv2⟩
  refine ⟨js_load, ?_, hsail, hv0, hv1, hv2⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js js hassert]
  exact hrun

/-- A failed store-alignment assertion stops the structured program before any
read-modify-write work can occur. -/
theorem assertBlockMisaligned (tail : JoltISA.Program)
    (mask : BitVec 64) (imm : BitVec 12) (rs1 : regidx)
    (js : SailJoltState)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (hmis : load_effective_address val imm &&& mask ≠ 0) :
    (JoltISA.execProgram (.instr (.VirtualAssertStoreAlignment rs1 imm mask) tail)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (load_effective_address val imm), ExceptionType.E_SAMO_Addr_Align ())) js := by
  let e :=
    (Virtaddr (load_effective_address val imm), ExceptionType.E_SAMO_Addr_Align ())
  have hassert :
      (JoltISA.execInstr (.VirtualAssertStoreAlignment rs1 imm mask)).run js =
        .ok (ExecutionResult.Memory_Exception e) js := by
    simpa [e, load_effective_address] using
      (JoltISA.execInstr_VirtualAssertStoreAlignment_run_misaligned rs1 imm mask
        js val hrx (by simpa [load_effective_address] using hmis))
  simpa [e] using
    (JoltISA.execProgram_instr_run_memory_exception
      (.VirtualAssertStoreAlignment rs1 imm mask) tail js js e hassert)

/-- Byte-store splice block.

Starting from the setup boundary (`v0 = ea`, `v1 = base`, `v2 = dword`), the
Rust-faithful `SB` middle sequence materializes a one-byte mask, shifts the low
byte of `rs2` into the target lane, and leaves the spliced dword in `v2`. -/
theorem byteSpliceBlock (rest : JoltISA.Program)
    (imm : BitVec 12) (rs2 : regidx)
    (js js_load : SailJoltState) (val rs2_val : BitVec 64)
    (hsetup : StoreSplice.ByteStoreSetup
      (load_effective_address val imm)
      (compute_aligned_dword_base_address val imm))
    (hload_sail : js_load.sail = js.sail)
    (hload_v0 : js_load.vregs 0 = load_effective_address val imm)
    (hload_v1 : js_load.vregs 1 = compute_aligned_dword_base_address val imm)
    (hload_v2 : js_load.vregs 2 =
      loaded_dword_at js.sail (compute_aligned_dword_base_address val imm))
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail) :
    ∃ js_splice : SailJoltState,
      (JoltISA.execProgram
        (.instr (.SLLI (.vreg 3) (.vreg 0) (3 : BitVec 6)) <|
         .instr (.LUI (.vreg 0) (0xff : BitVec 64)) <|
         .instr (.SLL (.vreg 0) (.vreg 0) (.vreg 3)) <|
         .instr (.SLL (.vreg 3) (.xreg rs2) (.vreg 3)) <|
         .instr (.XOR (.vreg 3) (.vreg 2) (.vreg 3)) <|
         .instr (.AND (.vreg 3) (.vreg 3) (.vreg 0)) <|
         .instr (.XOR (.vreg 2) (.vreg 2) (.vreg 3)) rest)).run js_load =
        (JoltISA.execProgram rest).run js_splice ∧
      js_splice.sail = js.sail ∧
      js_splice.vregs 1 = compute_aligned_dword_base_address val imm ∧
      js_splice.vregs 2 =
        StoreSplice.byteSplice
          (loaded_dword_at js.sail (compute_aligned_dword_base_address val imm))
          (Sail.BitVec.extractLsb rs2_val 7 0)
          (((load_effective_address val imm -
              compute_aligned_dword_base_address val imm).toNat) * 8) := by
  let ea := load_effective_address val imm
  let base := compute_aligned_dword_base_address val imm
  let dword := loaded_dword_at js.sail base
  let shift64 := shift_bits_left ea (3 : BitVec 6)
  let shift6 := Sail.BitVec.extractLsb shift64 5 0
  let mask := shift_bits_left (0x00000000000000FF : BitVec 64) shift6
  let shifted := shift_bits_left rs2_val shift6
  let xored := dword ^^^ shifted
  let masked := xored &&& mask
  let spliced :=
    StoreSplice.byteSplice dword (Sail.BitVec.extractLsb rs2_val 7 0) (((ea - base).toNat) * 8)
  let js_slli : SailJoltState :=
    { sail := js_load.sail
      vregs := fun r =>
        if r = (3 : JoltISA.VReg) then
          shift_bits_left (js_load.vregs (0 : JoltISA.VReg)) (3 : BitVec 6)
        else js_load.vregs r }
  let js_lui : SailJoltState :=
    { sail := js_slli.sail
      vregs := fun r => if r = (0 : JoltISA.VReg) then (0xff : BitVec 64) else js_slli.vregs r }
  let js_mask : SailJoltState :=
    { sail := js_lui.sail
      vregs := fun r =>
        if r = (0 : JoltISA.VReg) then
          shift_bits_left (js_lui.vregs (0 : JoltISA.VReg))
            (Sail.BitVec.extractLsb (js_lui.vregs (3 : JoltISA.VReg)) 5 0)
        else js_lui.vregs r }
  let js_shift : SailJoltState :=
    { sail := js_mask.sail
      vregs := fun r =>
        if r = (3 : JoltISA.VReg) then
          shift_bits_left rs2_val
            (Sail.BitVec.extractLsb (js_mask.vregs (3 : JoltISA.VReg)) 5 0)
        else js_mask.vregs r }
  let js_xor : SailJoltState :=
    { sail := js_shift.sail
      vregs := fun r =>
        if r = (3 : JoltISA.VReg) then
          js_shift.vregs (2 : JoltISA.VReg) ^^^ js_shift.vregs (3 : JoltISA.VReg)
        else js_shift.vregs r }
  let js_and : SailJoltState :=
    { sail := js_xor.sail
      vregs := fun r =>
        if r = (3 : JoltISA.VReg) then
          js_xor.vregs (3 : JoltISA.VReg) &&& js_xor.vregs (0 : JoltISA.VReg)
        else js_xor.vregs r }
  let js_splice : SailJoltState :=
    { sail := js_and.sail
      vregs := fun r =>
        if r = (2 : JoltISA.VReg) then
          js_and.vregs (2 : JoltISA.VReg) ^^^ js_and.vregs (3 : JoltISA.VReg)
        else js_and.vregs r }
  have hslli :
      (JoltISA.execInstr (.SLLI (.vreg 3) (.vreg 0) (3 : BitVec 6))).run js_load =
        .ok RETIRE_SUCCESS js_slli := by
    simpa [js_slli] using
      (JoltISA.slli_run_vreg_vreg (3 : JoltISA.VReg) (0 : JoltISA.VReg)
        (3 : BitVec 6) js_load)
  have hslli_v3 : js_slli.vregs (3 : JoltISA.VReg) = shift64 := by
    change shift_bits_left (js_load.vregs (0 : JoltISA.VReg)) (3 : BitVec 6) = shift64
    rw [hload_v0]
  have hlui :
      (JoltISA.execInstr (.LUI (.vreg 0) (0xff : BitVec 64))).run js_slli =
        .ok RETIRE_SUCCESS js_lui := by
    simpa [js_lui] using
      (JoltISA.execInstr_lui_vreg_run (0 : JoltISA.VReg) (0xff : BitVec 64) js_slli)
  have hlui_v3 : js_lui.vregs (3 : JoltISA.VReg) = shift64 := by
    change js_slli.vregs (3 : JoltISA.VReg) = shift64
    exact hslli_v3
  have hsll_mask :
      (JoltISA.execInstr (.SLL (.vreg 0) (.vreg 0) (.vreg 3))).run js_lui =
        .ok RETIRE_SUCCESS js_mask := by
    simpa [js_mask] using
      (JoltISA.execInstr_sll_vreg_vreg_vreg_run (0 : JoltISA.VReg) (0 : JoltISA.VReg)
        (3 : JoltISA.VReg) js_lui)
  have hmask_v0 : js_mask.vregs (0 : JoltISA.VReg) = mask := by
    change shift_bits_left (js_lui.vregs (0 : JoltISA.VReg))
      (Sail.BitVec.extractLsb (js_lui.vregs (3 : JoltISA.VReg)) 5 0) = mask
    rw [hlui_v3]
    simp [js_lui, mask, shift6, shift64]
  have hmask_v3 : js_mask.vregs (3 : JoltISA.VReg) = shift64 := by
    change js_lui.vregs (3 : JoltISA.VReg) = shift64
    exact hlui_v3
  have hrs2_mask : rX_bits rs2 js_mask.sail = .ok rs2_val js_mask.sail := by
    simpa [js_mask, js_lui, js_slli, hload_sail] using hrs2
  have hsll_value :
      (JoltISA.execInstr (.SLL (.vreg 3) (.xreg rs2) (.vreg 3))).run js_mask =
        .ok RETIRE_SUCCESS js_shift := by
    simpa [js_shift] using
      (JoltISA.execInstr_sll_xreg_vreg_vreg_run (3 : JoltISA.VReg) rs2
        (3 : JoltISA.VReg) js_mask rs2_val hrs2_mask)
  have hshift_v0 : js_shift.vregs (0 : JoltISA.VReg) = mask := by
    change js_mask.vregs (0 : JoltISA.VReg) = mask
    exact hmask_v0
  have hshift_v2 : js_shift.vregs (2 : JoltISA.VReg) = dword := by
    change js_mask.vregs (2 : JoltISA.VReg) = dword
    change js_lui.vregs (2 : JoltISA.VReg) = dword
    change js_slli.vregs (2 : JoltISA.VReg) = dword
    change js_load.vregs (2 : JoltISA.VReg) = dword
    exact hload_v2
  have hshift_v3 : js_shift.vregs (3 : JoltISA.VReg) = shifted := by
    change shift_bits_left rs2_val
      (Sail.BitVec.extractLsb (js_mask.vregs (3 : JoltISA.VReg)) 5 0) = shifted
    rw [hmask_v3]
  have hxor1 :
      (JoltISA.execInstr (.XOR (.vreg 3) (.vreg 2) (.vreg 3))).run js_shift =
        .ok RETIRE_SUCCESS js_xor := by
    simpa [js_xor] using
      (JoltISA.xor_run_vreg_vreg_vreg (3 : JoltISA.VReg) (2 : JoltISA.VReg)
        (3 : JoltISA.VReg) js_shift)
  have hxor_v0 : js_xor.vregs (0 : JoltISA.VReg) = mask := by
    change js_shift.vregs (0 : JoltISA.VReg) = mask
    exact hshift_v0
  have hxor_v2 : js_xor.vregs (2 : JoltISA.VReg) = dword := by
    change js_shift.vregs (2 : JoltISA.VReg) = dword
    exact hshift_v2
  have hxor_v3 : js_xor.vregs (3 : JoltISA.VReg) = xored := by
    change js_shift.vregs (2 : JoltISA.VReg) ^^^ js_shift.vregs (3 : JoltISA.VReg) = xored
    rw [hshift_v2, hshift_v3]
  have hand :
      (JoltISA.execInstr (.AND (.vreg 3) (.vreg 3) (.vreg 0))).run js_xor =
        .ok RETIRE_SUCCESS js_and := by
    simpa [js_and] using
      (JoltISA.execInstr_and_vreg_vreg_vreg_run (3 : JoltISA.VReg) (3 : JoltISA.VReg)
        (0 : JoltISA.VReg) js_xor)
  have hand_v2 : js_and.vregs (2 : JoltISA.VReg) = dword := by
    change js_xor.vregs (2 : JoltISA.VReg) = dword
    exact hxor_v2
  have hand_v3 : js_and.vregs (3 : JoltISA.VReg) = masked := by
    change js_xor.vregs (3 : JoltISA.VReg) &&& js_xor.vregs (0 : JoltISA.VReg) = masked
    rw [hxor_v3, hxor_v0]
  have hshift6 :
      shift6 = BitVec.ofNat 6 (((ea - base).toNat) * 8) := by
    simpa [shift6, shift64, ea, base] using shift6_eq_of_offset_byte ea base hsetup
  have hspliced : dword ^^^ masked = spliced := by
    dsimp [masked, xored, shifted, mask, spliced]
    rw [hshift6]
    simpa using
      byteSplice_eq_sequence dword rs2_val ((ea - base).toNat) hsetup.offset_cases
  have hxor2 :
      (JoltISA.execInstr (.XOR (.vreg 2) (.vreg 2) (.vreg 3))).run js_and =
        .ok RETIRE_SUCCESS js_splice := by
    simpa [js_splice] using
      (JoltISA.xor_run_vreg_vreg_vreg (2 : JoltISA.VReg) (2 : JoltISA.VReg)
        (3 : JoltISA.VReg) js_and)
  refine ⟨js_splice, ?_, ?_, ?_, ?_⟩
  · rw [JoltISA.execProgram_instr_run_retire _ _ js_load js_slli hslli]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_slli js_lui hlui]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_lui js_mask hsll_mask]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_mask js_shift hsll_value]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_shift js_xor hxor1]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_xor js_and hand]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_and js_splice hxor2]
  · simp [js_splice, js_and, js_xor, js_shift, js_mask, js_lui, js_slli, hload_sail]
  · change js_load.vregs (1 : JoltISA.VReg) = compute_aligned_dword_base_address val imm
    exact hload_v1
  · change js_and.vregs (2 : JoltISA.VReg) ^^^ js_and.vregs (3 : JoltISA.VReg) = spliced
    rw [hand_v2, hand_v3]
    exact hspliced

/-- Halfword-store splice block.

This is the same instruction skeleton as `byteSpliceBlock`, with a two-byte
mask (`0xffff`) and the halfword setup facts.  The theorem boundary says only
what later phases need: `v1` still holds the dword base and `v2` now holds the
pure halfword splice. -/
theorem halfwordSpliceBlock (rest : JoltISA.Program)
    (imm : BitVec 12) (rs2 : regidx)
    (js js_load : SailJoltState) (val rs2_val : BitVec 64)
    (hsetup : StoreSplice.HalfwordStoreSetup
      (load_effective_address val imm)
      (compute_aligned_dword_base_address val imm))
    (hload_sail : js_load.sail = js.sail)
    (hload_v0 : js_load.vregs 0 = load_effective_address val imm)
    (hload_v1 : js_load.vregs 1 = compute_aligned_dword_base_address val imm)
    (hload_v2 : js_load.vregs 2 =
      loaded_dword_at js.sail (compute_aligned_dword_base_address val imm))
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail) :
    ∃ js_splice : SailJoltState,
      (JoltISA.execProgram
        (.instr (.SLLI (.vreg 3) (.vreg 0) (3 : BitVec 6)) <|
         .instr (.LUI (.vreg 0) (0xffff : BitVec 64)) <|
         .instr (.SLL (.vreg 0) (.vreg 0) (.vreg 3)) <|
         .instr (.SLL (.vreg 3) (.xreg rs2) (.vreg 3)) <|
         .instr (.XOR (.vreg 3) (.vreg 2) (.vreg 3)) <|
         .instr (.AND (.vreg 3) (.vreg 3) (.vreg 0)) <|
         .instr (.XOR (.vreg 2) (.vreg 2) (.vreg 3)) rest)).run js_load =
        (JoltISA.execProgram rest).run js_splice ∧
      js_splice.sail = js.sail ∧
      js_splice.vregs 1 = compute_aligned_dword_base_address val imm ∧
      js_splice.vregs 2 =
        StoreSplice.halfwordSplice
          (loaded_dword_at js.sail (compute_aligned_dword_base_address val imm))
          (Sail.BitVec.extractLsb rs2_val 15 0)
          (((load_effective_address val imm -
              compute_aligned_dword_base_address val imm).toNat) * 8) := by
  let ea := load_effective_address val imm
  let base := compute_aligned_dword_base_address val imm
  let dword := loaded_dword_at js.sail base
  let shift64 := shift_bits_left ea (3 : BitVec 6)
  let shift6 := Sail.BitVec.extractLsb shift64 5 0
  let mask := shift_bits_left (0x000000000000FFFF : BitVec 64) shift6
  let shifted := shift_bits_left rs2_val shift6
  let xored := dword ^^^ shifted
  let masked := xored &&& mask
  let spliced :=
    StoreSplice.halfwordSplice dword (Sail.BitVec.extractLsb rs2_val 15 0)
      (((ea - base).toNat) * 8)
  let js_slli : SailJoltState :=
    { sail := js_load.sail
      vregs := fun r =>
        if r = (3 : JoltISA.VReg) then
          shift_bits_left (js_load.vregs (0 : JoltISA.VReg)) (3 : BitVec 6)
        else js_load.vregs r }
  let js_lui : SailJoltState :=
    { sail := js_slli.sail
      vregs := fun r => if r = (0 : JoltISA.VReg) then (0xffff : BitVec 64) else js_slli.vregs r }
  let js_mask : SailJoltState :=
    { sail := js_lui.sail
      vregs := fun r =>
        if r = (0 : JoltISA.VReg) then
          shift_bits_left (js_lui.vregs (0 : JoltISA.VReg))
            (Sail.BitVec.extractLsb (js_lui.vregs (3 : JoltISA.VReg)) 5 0)
        else js_lui.vregs r }
  let js_shift : SailJoltState :=
    { sail := js_mask.sail
      vregs := fun r =>
        if r = (3 : JoltISA.VReg) then
          shift_bits_left rs2_val
            (Sail.BitVec.extractLsb (js_mask.vregs (3 : JoltISA.VReg)) 5 0)
        else js_mask.vregs r }
  let js_xor : SailJoltState :=
    { sail := js_shift.sail
      vregs := fun r =>
        if r = (3 : JoltISA.VReg) then
          js_shift.vregs (2 : JoltISA.VReg) ^^^ js_shift.vregs (3 : JoltISA.VReg)
        else js_shift.vregs r }
  let js_and : SailJoltState :=
    { sail := js_xor.sail
      vregs := fun r =>
        if r = (3 : JoltISA.VReg) then
          js_xor.vregs (3 : JoltISA.VReg) &&& js_xor.vregs (0 : JoltISA.VReg)
        else js_xor.vregs r }
  let js_splice : SailJoltState :=
    { sail := js_and.sail
      vregs := fun r =>
        if r = (2 : JoltISA.VReg) then
          js_and.vregs (2 : JoltISA.VReg) ^^^ js_and.vregs (3 : JoltISA.VReg)
        else js_and.vregs r }
  have hslli :
      (JoltISA.execInstr (.SLLI (.vreg 3) (.vreg 0) (3 : BitVec 6))).run js_load =
        .ok RETIRE_SUCCESS js_slli := by
    simpa [js_slli] using
      (JoltISA.slli_run_vreg_vreg (3 : JoltISA.VReg) (0 : JoltISA.VReg)
        (3 : BitVec 6) js_load)
  have hslli_v3 : js_slli.vregs (3 : JoltISA.VReg) = shift64 := by
    change shift_bits_left (js_load.vregs (0 : JoltISA.VReg)) (3 : BitVec 6) = shift64
    rw [hload_v0]
  have hlui :
      (JoltISA.execInstr (.LUI (.vreg 0) (0xffff : BitVec 64))).run js_slli =
        .ok RETIRE_SUCCESS js_lui := by
    simpa [js_lui] using
      (JoltISA.execInstr_lui_vreg_run (0 : JoltISA.VReg) (0xffff : BitVec 64) js_slli)
  have hlui_v3 : js_lui.vregs (3 : JoltISA.VReg) = shift64 := by
    change js_slli.vregs (3 : JoltISA.VReg) = shift64
    exact hslli_v3
  have hsll_mask :
      (JoltISA.execInstr (.SLL (.vreg 0) (.vreg 0) (.vreg 3))).run js_lui =
        .ok RETIRE_SUCCESS js_mask := by
    simpa [js_mask] using
      (JoltISA.execInstr_sll_vreg_vreg_vreg_run (0 : JoltISA.VReg) (0 : JoltISA.VReg)
        (3 : JoltISA.VReg) js_lui)
  have hmask_v0 : js_mask.vregs (0 : JoltISA.VReg) = mask := by
    change shift_bits_left (js_lui.vregs (0 : JoltISA.VReg))
      (Sail.BitVec.extractLsb (js_lui.vregs (3 : JoltISA.VReg)) 5 0) = mask
    rw [hlui_v3]
    simp [js_lui, mask, shift6, shift64]
  have hmask_v3 : js_mask.vregs (3 : JoltISA.VReg) = shift64 := by
    change js_lui.vregs (3 : JoltISA.VReg) = shift64
    exact hlui_v3
  have hrs2_mask : rX_bits rs2 js_mask.sail = .ok rs2_val js_mask.sail := by
    simpa [js_mask, js_lui, js_slli, hload_sail] using hrs2
  have hsll_value :
      (JoltISA.execInstr (.SLL (.vreg 3) (.xreg rs2) (.vreg 3))).run js_mask =
        .ok RETIRE_SUCCESS js_shift := by
    simpa [js_shift] using
      (JoltISA.execInstr_sll_xreg_vreg_vreg_run (3 : JoltISA.VReg) rs2
        (3 : JoltISA.VReg) js_mask rs2_val hrs2_mask)
  have hshift_v0 : js_shift.vregs (0 : JoltISA.VReg) = mask := by
    change js_mask.vregs (0 : JoltISA.VReg) = mask
    exact hmask_v0
  have hshift_v2 : js_shift.vregs (2 : JoltISA.VReg) = dword := by
    change js_mask.vregs (2 : JoltISA.VReg) = dword
    change js_lui.vregs (2 : JoltISA.VReg) = dword
    change js_slli.vregs (2 : JoltISA.VReg) = dword
    change js_load.vregs (2 : JoltISA.VReg) = dword
    exact hload_v2
  have hshift_v3 : js_shift.vregs (3 : JoltISA.VReg) = shifted := by
    change shift_bits_left rs2_val
      (Sail.BitVec.extractLsb (js_mask.vregs (3 : JoltISA.VReg)) 5 0) = shifted
    rw [hmask_v3]
  have hxor1 :
      (JoltISA.execInstr (.XOR (.vreg 3) (.vreg 2) (.vreg 3))).run js_shift =
        .ok RETIRE_SUCCESS js_xor := by
    simpa [js_xor] using
      (JoltISA.xor_run_vreg_vreg_vreg (3 : JoltISA.VReg) (2 : JoltISA.VReg)
        (3 : JoltISA.VReg) js_shift)
  have hxor_v0 : js_xor.vregs (0 : JoltISA.VReg) = mask := by
    change js_shift.vregs (0 : JoltISA.VReg) = mask
    exact hshift_v0
  have hxor_v2 : js_xor.vregs (2 : JoltISA.VReg) = dword := by
    change js_shift.vregs (2 : JoltISA.VReg) = dword
    exact hshift_v2
  have hxor_v3 : js_xor.vregs (3 : JoltISA.VReg) = xored := by
    change js_shift.vregs (2 : JoltISA.VReg) ^^^ js_shift.vregs (3 : JoltISA.VReg) = xored
    rw [hshift_v2, hshift_v3]
  have hand :
      (JoltISA.execInstr (.AND (.vreg 3) (.vreg 3) (.vreg 0))).run js_xor =
        .ok RETIRE_SUCCESS js_and := by
    simpa [js_and] using
      (JoltISA.execInstr_and_vreg_vreg_vreg_run (3 : JoltISA.VReg) (3 : JoltISA.VReg)
        (0 : JoltISA.VReg) js_xor)
  have hand_v2 : js_and.vregs (2 : JoltISA.VReg) = dword := by
    change js_xor.vregs (2 : JoltISA.VReg) = dword
    exact hxor_v2
  have hand_v3 : js_and.vregs (3 : JoltISA.VReg) = masked := by
    change js_xor.vregs (3 : JoltISA.VReg) &&& js_xor.vregs (0 : JoltISA.VReg) = masked
    rw [hxor_v3, hxor_v0]
  have hshift6 :
      shift6 = BitVec.ofNat 6 (((ea - base).toNat) * 8) := by
    simpa [shift6, shift64, ea, base] using shift6_eq_of_offset_halfword ea base hsetup
  have hspliced : dword ^^^ masked = spliced := by
    dsimp [masked, xored, shifted, mask, spliced]
    rw [hshift6]
    simpa using
      halfwordSplice_eq_sequence dword rs2_val ((ea - base).toNat) hsetup.offset_cases
  have hxor2 :
      (JoltISA.execInstr (.XOR (.vreg 2) (.vreg 2) (.vreg 3))).run js_and =
        .ok RETIRE_SUCCESS js_splice := by
    simpa [js_splice] using
      (JoltISA.xor_run_vreg_vreg_vreg (2 : JoltISA.VReg) (2 : JoltISA.VReg)
        (3 : JoltISA.VReg) js_and)
  refine ⟨js_splice, ?_, ?_, ?_, ?_⟩
  · rw [JoltISA.execProgram_instr_run_retire _ _ js_load js_slli hslli]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_slli js_lui hlui]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_lui js_mask hsll_mask]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_mask js_shift hsll_value]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_shift js_xor hxor1]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_xor js_and hand]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_and js_splice hxor2]
  · simp [js_splice, js_and, js_xor, js_shift, js_mask, js_lui, js_slli, hload_sail]
  · change js_load.vregs (1 : JoltISA.VReg) = compute_aligned_dword_base_address val imm
    exact hload_v1
  · change js_and.vregs (2 : JoltISA.VReg) ^^^ js_and.vregs (3 : JoltISA.VReg) = spliced
    rw [hand_v2, hand_v3]
    exact hspliced

/-- Word-store mask block for `SW`.

Rust does not materialize the 32-bit mask with `LUI`.  It emits
`ORI v3, x0, -1; SRLI v3, v3, 32`, then shifts that mask by the byte-lane
offset already computed in `v0`.  This block proves exactly that prefix and
exports the boundary facts needed by the value/splice block.  The `x0` read is
an explicit hypothesis, so this proof stays about the Jolt bytecode block rather
than unfolding Sail's architectural-register implementation. -/
theorem wordMaskBlock (rest : JoltISA.Program)
    (imm : BitVec 12)
    (js js_load : SailJoltState) (val : BitVec 64)
    (hload_sail : js_load.sail = js.sail)
    (hload_v0 : js_load.vregs 0 = load_effective_address val imm)
    (hload_v1 : js_load.vregs 1 = compute_aligned_dword_base_address val imm)
    (hload_v2 : js_load.vregs 2 =
      loaded_dword_at js.sail (compute_aligned_dword_base_address val imm))
    (hx0 : rX_bits (regidx.Regidx 0) js_load.sail = .ok 0#64 js_load.sail) :
    ∃ js_mask : SailJoltState,
      (JoltISA.execProgram
        (.instr (.SLLI (.vreg 0) (.vreg 0) (3 : BitVec 6)) <|
         .instr (.ORI (.vreg 3) (.xreg (regidx.Regidx 0)) (-1 : BitVec 12)) <|
         .instr (.SRLI (.vreg 3) (.vreg 3) (32 : BitVec 6)) <|
         .instr (.SLL (.vreg 3) (.vreg 3) (.vreg 0)) rest)).run js_load =
        (JoltISA.execProgram rest).run js_mask ∧
      js_mask.sail = js.sail ∧
      js_mask.vregs 0 =
        shift_bits_left (load_effective_address val imm) (3 : BitVec 6) ∧
      js_mask.vregs 1 = compute_aligned_dword_base_address val imm ∧
      js_mask.vregs 2 =
        loaded_dword_at js.sail (compute_aligned_dword_base_address val imm) ∧
      js_mask.vregs 3 =
        shift_bits_left (0x00000000FFFFFFFF : BitVec 64)
          (Sail.BitVec.extractLsb
            (shift_bits_left (load_effective_address val imm) (3 : BitVec 6)) 5 0) := by
  let ea := load_effective_address val imm
  let base := compute_aligned_dword_base_address val imm
  let dword := loaded_dword_at js.sail base
  let shift64 := shift_bits_left ea (3 : BitVec 6)
  let mask32 := (0x00000000FFFFFFFF : BitVec 64)
  let shiftedMask := shift_bits_left mask32 (Sail.BitVec.extractLsb shift64 5 0)
  let js_slli := swWordShiftState js_load
  let js_ori := swWordOnesState js_slli
  let js_srli := swWordBaseMaskState js_ori
  let js_mask := swWordMaskState js_srli
  have hx0_slli : rX_bits (regidx.Regidx 0) js_slli.sail = .ok 0#64 js_slli.sail := by
    change rX_bits (regidx.Regidx 0) js_load.sail = .ok 0#64 js_load.sail
    exact hx0
  refine ⟨js_mask, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [swWordShiftStep]
    rw [swWordOnesStep _ _ hx0_slli]
    rw [swWordBaseMaskStep]
    rw [swWordMaskShiftStep]
  · calc
      js_mask.sail = js_load.sail := by
        change (swWordMaskState (swWordBaseMaskState (swWordOnesState (swWordShiftState js_load)))).sail =
          js_load.sail
        exact swWordMaskState_sail js_load
      _ = js.sail := hload_sail
  · calc
      js_mask.vregs (0 : JoltISA.VReg) = shift_bits_left (js_load.vregs 0) (3 : BitVec 6) := by
        change (swWordMaskState (swWordBaseMaskState (swWordOnesState (swWordShiftState js_load)))).vregs
            (0 : JoltISA.VReg) =
          shift_bits_left (js_load.vregs 0) (3 : BitVec 6)
        exact swWordMaskState_v0 js_load
      _ = shift64 := by rw [hload_v0]
  · calc
      js_mask.vregs (1 : JoltISA.VReg) = js_load.vregs (1 : JoltISA.VReg) := by
        change (swWordMaskState (swWordBaseMaskState (swWordOnesState (swWordShiftState js_load)))).vregs
            (1 : JoltISA.VReg) =
          js_load.vregs (1 : JoltISA.VReg)
        exact swWordMaskState_v1 js_load
      _ = base := hload_v1
  · calc
      js_mask.vregs (2 : JoltISA.VReg) = js_load.vregs (2 : JoltISA.VReg) := by
        change (swWordMaskState (swWordBaseMaskState (swWordOnesState (swWordShiftState js_load)))).vregs
            (2 : JoltISA.VReg) =
          js_load.vregs (2 : JoltISA.VReg)
        exact swWordMaskState_v2 js_load
      _ = dword := hload_v2
  · calc
      js_mask.vregs (3 : JoltISA.VReg) =
          shift_bits_left mask32
            (Sail.BitVec.extractLsb
              (shift_bits_left (js_load.vregs 0) (3 : BitVec 6)) 5 0) := by
        change (swWordMaskState (swWordBaseMaskState (swWordOnesState (swWordShiftState js_load)))).vregs
            (3 : JoltISA.VReg) =
          shift_bits_left mask32
            (Sail.BitVec.extractLsb
              (shift_bits_left (js_load.vregs 0) (3 : BitVec 6)) 5 0)
        exact swWordMaskState_v3 js_load
      _ = shiftedMask := by rw [hload_v0]

/-- Word-store value/splice block for `SW`.

This is the second half of the Rust `SW` middle sequence.  It assumes the mask
block has already left the bit offset in `v0`, the aligned dword base in `v1`,
the original dword in `v2`, and the shifted 32-bit mask in `v3`.  The block then
shifts the low word of `rs2` into place and performs the standard
`dword ^ ((dword ^ shifted_value) & mask)` splice, leaving the modified dword in
`v2`. -/
theorem wordSpliceBlock (rest : JoltISA.Program)
    (imm : BitVec 12) (rs2 : regidx)
    (js js_mask : SailJoltState) (val rs2_val : BitVec 64)
    (hsetup : StoreSplice.WordStoreSetup
      (load_effective_address val imm)
      (compute_aligned_dword_base_address val imm))
    (hmask_sail : js_mask.sail = js.sail)
    (hmask_v0 :
      js_mask.vregs 0 =
        shift_bits_left (load_effective_address val imm) (3 : BitVec 6))
    (hmask_v1 : js_mask.vregs 1 = compute_aligned_dword_base_address val imm)
    (hmask_v2 : js_mask.vregs 2 =
      loaded_dword_at js.sail (compute_aligned_dword_base_address val imm))
    (hmask_v3 :
      js_mask.vregs 3 =
        shift_bits_left (0x00000000FFFFFFFF : BitVec 64)
          (Sail.BitVec.extractLsb
            (shift_bits_left (load_effective_address val imm) (3 : BitVec 6)) 5 0))
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail) :
    ∃ js_splice : SailJoltState,
      (JoltISA.execProgram
        (.instr (.SLL (.vreg 0) (.xreg rs2) (.vreg 0)) <|
         .instr (.XOR (.vreg 0) (.vreg 2) (.vreg 0)) <|
         .instr (.AND (.vreg 0) (.vreg 0) (.vreg 3)) <|
         .instr (.XOR (.vreg 2) (.vreg 2) (.vreg 0)) rest)).run js_mask =
        (JoltISA.execProgram rest).run js_splice ∧
      js_splice.sail = js.sail ∧
      js_splice.vregs 1 = compute_aligned_dword_base_address val imm ∧
      js_splice.vregs 2 =
        StoreSplice.wordSplice
          (loaded_dword_at js.sail (compute_aligned_dword_base_address val imm))
          (Sail.BitVec.extractLsb rs2_val 31 0)
          (((load_effective_address val imm -
              compute_aligned_dword_base_address val imm).toNat) * 8) := by
  let ea := load_effective_address val imm
  let base := compute_aligned_dword_base_address val imm
  let dword := loaded_dword_at js.sail base
  let shift64 := shift_bits_left ea (3 : BitVec 6)
  let shift6 := Sail.BitVec.extractLsb shift64 5 0
  let mask := shift_bits_left (0x00000000FFFFFFFF : BitVec 64) shift6
  let shifted := shift_bits_left rs2_val shift6
  let xored := dword ^^^ shifted
  let masked := xored &&& mask
  let spliced :=
    StoreSplice.wordSplice dword (Sail.BitVec.extractLsb rs2_val 31 0) (((ea - base).toNat) * 8)
  let js_shift : SailJoltState :=
    { sail := js_mask.sail
      vregs := fun r =>
        if r = (0 : JoltISA.VReg) then
          shift_bits_left rs2_val
            (Sail.BitVec.extractLsb (js_mask.vregs (0 : JoltISA.VReg)) 5 0)
        else js_mask.vregs r }
  let js_xor : SailJoltState :=
    { sail := js_shift.sail
      vregs := fun r =>
        if r = (0 : JoltISA.VReg) then
          js_shift.vregs (2 : JoltISA.VReg) ^^^ js_shift.vregs (0 : JoltISA.VReg)
        else js_shift.vregs r }
  let js_and : SailJoltState :=
    { sail := js_xor.sail
      vregs := fun r =>
        if r = (0 : JoltISA.VReg) then
          js_xor.vregs (0 : JoltISA.VReg) &&& js_xor.vregs (3 : JoltISA.VReg)
        else js_xor.vregs r }
  let js_splice : SailJoltState :=
    { sail := js_and.sail
      vregs := fun r =>
        if r = (2 : JoltISA.VReg) then
          js_and.vregs (2 : JoltISA.VReg) ^^^ js_and.vregs (0 : JoltISA.VReg)
        else js_and.vregs r }
  have hrs2_mask : rX_bits rs2 js_mask.sail = .ok rs2_val js_mask.sail := by
    simpa [hmask_sail] using hrs2
  have hsll_value :
      (JoltISA.execInstr (.SLL (.vreg 0) (.xreg rs2) (.vreg 0))).run js_mask =
        .ok RETIRE_SUCCESS js_shift := by
    simpa [js_shift] using
      (JoltISA.execInstr_sll_xreg_vreg_vreg_run (0 : JoltISA.VReg) rs2
        (0 : JoltISA.VReg) js_mask rs2_val hrs2_mask)
  have hshift_v0 : js_shift.vregs (0 : JoltISA.VReg) = shifted := by
    change shift_bits_left rs2_val
      (Sail.BitVec.extractLsb (js_mask.vregs (0 : JoltISA.VReg)) 5 0) = shifted
    rw [hmask_v0]
  have hshift_v2 : js_shift.vregs (2 : JoltISA.VReg) = dword := by
    change js_mask.vregs (2 : JoltISA.VReg) = dword
    exact hmask_v2
  have hshift_v3 : js_shift.vregs (3 : JoltISA.VReg) = mask := by
    change js_mask.vregs (3 : JoltISA.VReg) = mask
    exact hmask_v3
  have hxor1 :
      (JoltISA.execInstr (.XOR (.vreg 0) (.vreg 2) (.vreg 0))).run js_shift =
        .ok RETIRE_SUCCESS js_xor := by
    simpa [js_xor] using
      (JoltISA.xor_run_vreg_vreg_vreg (0 : JoltISA.VReg) (2 : JoltISA.VReg)
        (0 : JoltISA.VReg) js_shift)
  have hxor_v0 : js_xor.vregs (0 : JoltISA.VReg) = xored := by
    change js_shift.vregs (2 : JoltISA.VReg) ^^^ js_shift.vregs (0 : JoltISA.VReg) = xored
    rw [hshift_v2, hshift_v0]
  have hxor_v2 : js_xor.vregs (2 : JoltISA.VReg) = dword := by
    change js_shift.vregs (2 : JoltISA.VReg) = dword
    exact hshift_v2
  have hxor_v3 : js_xor.vregs (3 : JoltISA.VReg) = mask := by
    change js_shift.vregs (3 : JoltISA.VReg) = mask
    exact hshift_v3
  have hand :
      (JoltISA.execInstr (.AND (.vreg 0) (.vreg 0) (.vreg 3))).run js_xor =
        .ok RETIRE_SUCCESS js_and := by
    simpa [js_and] using
      (JoltISA.execInstr_and_vreg_vreg_vreg_run (0 : JoltISA.VReg) (0 : JoltISA.VReg)
        (3 : JoltISA.VReg) js_xor)
  have hand_v0 : js_and.vregs (0 : JoltISA.VReg) = masked := by
    change js_xor.vregs (0 : JoltISA.VReg) &&& js_xor.vregs (3 : JoltISA.VReg) = masked
    rw [hxor_v0, hxor_v3]
  have hand_v2 : js_and.vregs (2 : JoltISA.VReg) = dword := by
    change js_xor.vregs (2 : JoltISA.VReg) = dword
    exact hxor_v2
  have hshift6 :
      shift6 = BitVec.ofNat 6 (((ea - base).toNat) * 8) := by
    simpa [shift6, shift64, ea, base] using shift6_eq_of_offset_word ea base hsetup
  have hspliced : dword ^^^ masked = spliced := by
    dsimp [masked, xored, shifted, mask, spliced]
    rw [hshift6]
    simpa using
      wordSplice_eq_sequence dword rs2_val ((ea - base).toNat) hsetup.offset_cases
  have hxor2 :
      (JoltISA.execInstr (.XOR (.vreg 2) (.vreg 2) (.vreg 0))).run js_and =
        .ok RETIRE_SUCCESS js_splice := by
    simpa [js_splice] using
      (JoltISA.xor_run_vreg_vreg_vreg (2 : JoltISA.VReg) (2 : JoltISA.VReg)
        (0 : JoltISA.VReg) js_and)
  refine ⟨js_splice, ?_, ?_, ?_, ?_⟩
  · rw [JoltISA.execProgram_instr_run_retire _ _ js_mask js_shift hsll_value]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_shift js_xor hxor1]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_xor js_and hand]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_and js_splice hxor2]
  · simp [js_splice, js_and, js_xor, js_shift, hmask_sail]
  · simp [js_splice, js_and, js_xor, js_shift]
    exact hmask_v1
  · change js_and.vregs (2 : JoltISA.VReg) ^^^ js_and.vregs (0 : JoltISA.VReg) = spliced
    rw [hand_v2, hand_v0]
    exact hspliced

/-- Final dword-store block shared by all store expansions.

The preceding splice block leaves the aligned dword base in `v1` and the
modified dword in `v2`.  `SD v1, v2, 0` hands those values to Sail's memory
write pipeline and preserves the virtual registers. -/
theorem sdWriteBlock (rest : JoltISA.Program)
    (js_store : SailJoltState) (base dword_new : BitVec 64) (s' : SailState)
    (hbase : js_store.vregs 1 = base)
    (hdword : js_store.vregs 2 = dword_new)
    (hwrite :
      vmem_write_addr (Virtaddr base) 8 dword_new
        (Store Data) false false false js_store.sail =
      .ok (Ok true) s') :
    ∃ js_write : SailJoltState,
      (JoltISA.execProgram (.instr (.SD 1 2 0) rest)).run js_store =
        (JoltISA.execProgram rest).run js_write ∧
      js_write.sail = s' ∧
      js_write.vregs = js_store.vregs := by
  let js_write : SailJoltState := { sail := s', vregs := js_store.vregs }
  have hzero : sign_extend (m := 64) (0 : BitVec 12) = (0 : BitVec 64) := by decide
  have haddr : js_store.vregs 1 + sign_extend (m := 64) (0 : BitVec 12) = base := by
    rw [hzero, hbase]
    bv_decide
  have hwrite' :
      vmem_write_addr
        (Virtaddr (js_store.vregs (1 : JoltISA.VReg) + sign_extend (m := 64) (0 : BitVec 12)))
        8 (js_store.vregs (2 : JoltISA.VReg))
        (Store Data) false false false js_store.sail =
      .ok (Ok true) s' := by
    rw [haddr, hdword]
    exact hwrite
  have hsd :
      (JoltISA.execInstr (.SD 1 2 0)).run js_store =
        .ok RETIRE_SUCCESS js_write := by
    simpa [js_write] using
      (JoltISA.execInstr_sd_vreg_run_of_write
        (1 : JoltISA.VReg) (2 : JoltISA.VReg) (0 : BitVec 12) js_store s' hwrite')
  refine ⟨js_write, ?_, rfl, rfl⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js_store js_write hsd]

end StoreProgramBlocks

end
