import JoltBytecode.EmbeddedSailJoltState.JoltISA.Expansions.Store
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.StraightLine
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadDefUtils
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.StoreDefUtils
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.StoreFamily.ProgramBlocks
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.StoreFamily.Splice

/-!
# SW: top-down store-word equivalence

This file is deliberately organized like the program-level load proofs.
`JoltISA.swProgram` is the Rust-faithful bytecode expansion; the proof reduces
that program in phases, reduces Sail's native `execute_STORE`, and then bridges
the two final memory states with a pure splice lemma.

The current goal is architectural clarity before proof grinding.  The hard
phase facts are named explicitly, so the structure of the finished proof stays
visible:

* `swProgram_reduces_to_dword_store` is the monadic Jolt side:
  assertion/setup, dword load, SW splice logic, and final `SD`.
* `sw_spliced_dword_store_eq_word_store` is the pure memory bridge:
  writing the spliced enclosing dword has the same memory effect as a native
  four-byte word store.
* `execute_SW_reduces` is the Sail side:
  native `execute_STORE ... 4` reduces to the same word-store state.
-/

set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace SW_main

/-- Reading architectural register `x0` is always the pure zero read.

`SW`'s mask construction uses `ORI v3, x0, -1`, so the program-block proof
needs this fact at the point where the mask block begins. -/
private theorem read_x0_eq_zero (s : SailState) :
    rX_bits (regidx.Regidx 0) s = .ok 0#64 s := by
  unfold rX_bits rX regval_from_reg zero_reg zeros
  simp [Sail.BitVec.toNatInt, bind, EStateM.bind, pure, EStateM.pure]

/-- The exact dword value that the Rust `SW` inline sequence writes back.

The Jolt program first loads the enclosing dword, then replaces exactly the
four bytes selected by the effective address with the low word of `rs2`.
Keeping this expression named makes the theorem statements read top-down
instead of repeating the full splice expression everywhere. -/
def swSplicedDword (imm : BitVec 12) (rs1_val rs2_val : BitVec 64)
    (s : SailState) : BitVec 64 :=
  let ea := load_effective_address rs1_val imm
  let base := compute_aligned_dword_base_address rs1_val imm
  StoreSplice.wordSplice
    (loaded_dword_at s base)
    (Sail.BitVec.extractLsb rs2_val 31 0)
    (((ea - base).toNat) * 8)

/-- **Jolt-side reduction for SW.**

This is the store analogue of the load-side concrete program lemmas.  It says
that the structured Jolt-ISA program follows the Rust bytecode sequence and
ends by writing the spliced enclosing dword with `SD`.

Intended proof phases:
1. `VirtualAssertStoreAlignment; ADDI; ANDI; LD` establishes `ea`, `base`, and original
   dword.
2. The SW mask/value logic computes `swSplicedDword`.
3. `SD v1, v2, 0` writes that dword through Sail's store pipeline. -/
theorem swProgram_reduces_to_dword_store (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (rs1_val rs2_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (hsetup : StoreSplice.WordStoreSetup
      (load_effective_address rs1_val imm)
      (compute_aligned_dword_base_address rs1_val imm))
    (h_dword_translate :
      BareTranslation (compute_aligned_dword_base_address rs1_val imm) js.sail)
    (h_dword_phys :
      FlatPhysMem (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
    (hwrite_dword :
      vmem_write_addr
        (Virtaddr (compute_aligned_dword_base_address rs1_val imm)) 8
        (swSplicedDword imm rs1_val rs2_val js.sail)
        (Store Data) false false false js.sail =
      .ok (Ok true)
        (state_after_dword_store js.sail
          (compute_aligned_dword_base_address rs1_val imm)
          (swSplicedDword imm rs1_val rs2_val js.sail))) :
    ∃ js' : SailJoltState,
      (JoltISA.execProgram (JoltISA.swProgram imm rs2 rs1)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail =
        state_after_dword_store js.sail
          (compute_aligned_dword_base_address rs1_val imm)
          (swSplicedDword imm rs1_val rs2_val js.sail) := by
  let writeTail : JoltISA.Program :=
    .instr (.SD 1 2 0) <| .done RETIRE_SUCCESS
  let spliceTail : JoltISA.Program :=
    .instr (.SLL (.vreg 0) (.xreg rs2) (.vreg 0)) <|
    .instr (.XOR (.vreg 0) (.vreg 2) (.vreg 0)) <|
    .instr (.AND (.vreg 0) (.vreg 0) (.vreg 3)) <|
    .instr (.XOR (.vreg 2) (.vreg 2) (.vreg 0)) <|
    writeTail
  let maskTail : JoltISA.Program :=
    .instr (.SLLI (.vreg 0) (.vreg 0) (3 : BitVec 6)) <|
    .instr (.ORI (.vreg 3) (.xreg (regidx.Regidx 0)) (-1 : BitVec 12)) <|
    .instr (.SRLI (.vreg 3) (.vreg 3) (32 : BitVec 6)) <|
    .instr (.SLL (.vreg 3) (.vreg 3) (.vreg 0)) <|
    spliceTail
  let base := compute_aligned_dword_base_address rs1_val imm
  let dword_new := swSplicedDword imm rs1_val rs2_val js.sail
  let finalSail := state_after_dword_store js.sail base dword_new
  rcases StoreProgramBlocks.assertSetupBlockAligned maskTail
      (3 : BitVec 64) imm rs1 js hcfg rs1_val hrs1 hsetup.word_aligned
      h_dword_translate h_dword_phys with
    ⟨js_load, hsetup_run, hload_sail, hload_v0, hload_v1, hload_v2⟩
  have hx0 : rX_bits (regidx.Regidx 0) js_load.sail = .ok 0#64 js_load.sail :=
    read_x0_eq_zero js_load.sail
  rcases StoreProgramBlocks.wordMaskBlock spliceTail imm js js_load rs1_val
      hload_sail hload_v0 hload_v1 hload_v2 hx0 with
    ⟨js_mask, hmask_run, hmask_sail, hmask_v0, hmask_v1, hmask_v2, hmask_v3⟩
  rcases StoreProgramBlocks.wordSpliceBlock writeTail imm rs2 js js_mask
      rs1_val rs2_val hsetup hmask_sail hmask_v0 hmask_v1 hmask_v2 hmask_v3 hrs2 with
    ⟨js_splice, hsplice_run, hsplice_sail, hsplice_v1, hsplice_v2⟩
  have hdword_new : js_splice.vregs 2 = dword_new := by
    simpa [dword_new, swSplicedDword] using hsplice_v2
  have hwrite_for_sd :
      vmem_write_addr (Virtaddr base) 8 dword_new
        (Store Data) false false false js_splice.sail =
      .ok (Ok true) finalSail := by
    rw [hsplice_sail]
    simpa [base, dword_new, finalSail] using hwrite_dword
  rcases StoreProgramBlocks.sdWriteBlock (.done RETIRE_SUCCESS)
      js_splice base dword_new finalSail hsplice_v1 hdword_new hwrite_for_sd with
    ⟨js_write, hsd_run, hsail_write, _hvregs_write⟩
  refine ⟨js_write, ?_, ?_⟩
  · calc
      (JoltISA.execProgram (JoltISA.swProgram imm rs2 rs1)).run js =
          (JoltISA.execProgram maskTail).run js_load := by
            simpa [JoltISA.swProgram, maskTail, spliceTail, writeTail] using hsetup_run
      _ = (JoltISA.execProgram spliceTail).run js_mask := by
            simpa [maskTail, spliceTail, writeTail] using hmask_run
      _ = (JoltISA.execProgram writeTail).run js_splice := by
            simpa [spliceTail, writeTail] using hsplice_run
      _ = (JoltISA.execProgram (.done RETIRE_SUCCESS)).run js_write := by
            simpa [writeTail] using hsd_run
      _ = .ok RETIRE_SUCCESS js_write := by
            rfl
  · simpa [finalSail, base, dword_new] using hsail_write

/-- **Pure bridge for SW.**

Once the Jolt side has reduced to an enclosing-dword write, this lemma removes
the Jolt implementation detail.  It states that the specific dword produced by
the SW splice has exactly the same memory effect as Sail's native four-byte
store at the effective address. -/
theorem sw_spliced_dword_store_eq_word_store (imm : BitVec 12)
    (s : SailState) (rs1_val rs2_val : BitVec 64)
    (hsetup : StoreSplice.WordStoreSetup
      (load_effective_address rs1_val imm)
      (compute_aligned_dword_base_address rs1_val imm))
    (hmem : ∀ addr : Nat, s.mem.get? addr ≠ none) :
    state_after_dword_store s
        (compute_aligned_dword_base_address rs1_val imm)
        (swSplicedDword imm rs1_val rs2_val s) =
      state_after_word_store s
        (load_effective_address rs1_val imm)
        (Sail.BitVec.extractLsb rs2_val 31 0) := by
  let ea := load_effective_address rs1_val imm
  let base := compute_aligned_dword_base_address rs1_val imm
  let dword_orig := loaded_dword_at s base
  let word_val := Sail.BitVec.extractLsb rs2_val 31 0
  let dword_new := swSplicedDword imm rs1_val rs2_val s
  let off := (ea - base).toNat
  have hoff : off = 0 ∨ off = 4 := by
    simpa [off, ea, base] using hsetup.offset_cases
  have hspec : StoreSplice.IsWordSplice dword_orig dword_new word_val off := by
    simpa [dword_new, swSplicedDword, dword_orig, word_val, off, ea, base, Nat.mul_comm]
      using StoreSplice.wordSplice_spec dword_orig word_val off hoff
  have hpop : ∀ k : Nat, k < 8 -> s.mem.get? (base.toNat + k) ≠ none := by
    intro k _hk
    exact hmem (base.toNat + k)
  have hload : ∀ k : Nat, k < 8 →
      dword_byte dword_orig k = loaded_byte_at s (base + BitVec.ofNat 64 k) := by
    intro k hk
    interval_cases k <;> simp [dword_orig, loaded_dword_at, dword_byte] <;> bv_decide
  have hmem_eq :
      (state_after_dword_store s base dword_new).mem =
      (state_after_word_store s ea word_val).mem := by
    dsimp [StoreSplice.IsWordSplice] at hspec
    exact StoreSplice.dword_store_splice_eq_word_store_populated'
      s ea base word_val dword_orig dword_new hsetup hpop hload hspec.1 hspec.2
  have hstate :
      state_after_dword_store s base dword_new =
      state_after_word_store s ea word_val := by
    simpa [state_after_dword_store, state_after_word_store] using hmem_eq
  simpa [ea, base, dword_new, word_val] using hstate

/-- **Concrete aligned SW execution on the Jolt side.**

This composes the Jolt monadic reduction with the pure splice bridge.  After
this theorem, the Jolt side is expressed in the same canonical memory state as
the Sail side: `state_after_word_store`. -/
theorem swProgram_concrete_aligned (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (rs1_val rs2_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (hsetup : StoreSplice.WordStoreSetup
      (load_effective_address rs1_val imm)
      (compute_aligned_dword_base_address rs1_val imm))
    (h_dword_translate :
      BareTranslation (compute_aligned_dword_base_address rs1_val imm) js.sail)
    (h_dword_phys :
      FlatPhysMem (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
    (hwrite_dword :
      vmem_write_addr
        (Virtaddr (compute_aligned_dword_base_address rs1_val imm)) 8
        (swSplicedDword imm rs1_val rs2_val js.sail)
        (Store Data) false false false js.sail =
      .ok (Ok true)
        (state_after_dword_store js.sail
          (compute_aligned_dword_base_address rs1_val imm)
          (swSplicedDword imm rs1_val rs2_val js.sail))) :
    ∃ js' : SailJoltState,
      (JoltISA.execProgram (JoltISA.swProgram imm rs2 rs1)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail =
        state_after_word_store js.sail
          (load_effective_address rs1_val imm)
          (Sail.BitVec.extractLsb rs2_val 31 0) := by
  rcases swProgram_reduces_to_dword_store imm rs2 rs1 js hcfg rs1_val rs2_val
      hrs1 hrs2 hsetup h_dword_translate h_dword_phys hwrite_dword with
    ⟨js', hjolt, hjolt_sail⟩
  refine ⟨js', hjolt, ?_⟩
  rw [hjolt_sail]
  exact sw_spliced_dword_store_eq_word_store imm js.sail rs1_val rs2_val
    hsetup hcfg.mem_populated

/-- **Sail-side SW reduction.**

The native Sail instruction is a single store step.  Under an explicit
successful `vmem_write` assumption, it reduces to the same canonical
`state_after_word_store` used by the Jolt-side theorem. -/
theorem execute_SW_reduces (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (rs1_val rs2_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (hsetup : StoreSplice.WordStoreSetup
      (load_effective_address rs1_val imm)
      (compute_aligned_dword_base_address rs1_val imm))
    (hwrite_word :
      vmem_write rs1 (sign_extend (m := 64) imm) 4
        (Sail.BitVec.extractLsb rs2_val 31 0)
        (Store Data) false false false js.sail =
      .ok (Ok true)
        (state_after_word_store js.sail
          (load_effective_address rs1_val imm)
          (Sail.BitVec.extractLsb rs2_val 31 0))) :
    (execute_STORE imm rs2 rs1 4).run js.sail =
      .ok RETIRE_SUCCESS
        (state_after_word_store js.sail
          (load_effective_address rs1_val imm)
          (Sail.BitVec.extractLsb rs2_val 31 0)) := by
  have hrs1_exists :
      ∃ v : BitVec 64,
        rX_bits rs1 js.sail = .ok v js.sail ∧
        load_effective_address rs1_val imm = v + sign_extend (m := 64) imm := by
    exact ⟨rs1_val, hrs1, rfl⟩
  have hsetup_old :
      DwordStoreSetup
        (load_effective_address rs1_val imm)
        (compute_aligned_dword_base_address rs1_val imm) :=
    { word_aligned := hsetup.word_aligned
      base_is_aligned := hsetup.base_is_aligned
      no_ovf := hsetup.no_ovf }
  exact execute_STORE_word_eq_state_after_word_store imm rs2 rs1 js
    rs2_val (load_effective_address rs1_val imm)
    (compute_aligned_dword_base_address rs1_val imm)
    hrs1_exists hrs2 hsetup_old hcfg hwrite_word

/-- **Aligned public SW theorem.**

This is the load-family proof pattern applied to stores: reduce the Jolt
program, reduce the Sail instruction, and observe that both sides produce the
same canonical Sail state. -/
theorem swProgram_eq_sail_aligned (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (rs1_val rs2_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (hsetup : StoreSplice.WordStoreSetup
      (load_effective_address rs1_val imm)
      (compute_aligned_dword_base_address rs1_val imm))
    (h_dword_translate :
      BareTranslation (compute_aligned_dword_base_address rs1_val imm) js.sail)
    (h_dword_phys :
      FlatPhysMem (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
    (hwrite_dword :
      vmem_write_addr
        (Virtaddr (compute_aligned_dword_base_address rs1_val imm)) 8
        (swSplicedDword imm rs1_val rs2_val js.sail)
        (Store Data) false false false js.sail =
      .ok (Ok true)
        (state_after_dword_store js.sail
          (compute_aligned_dword_base_address rs1_val imm)
          (swSplicedDword imm rs1_val rs2_val js.sail)))
    (hwrite_word :
      vmem_write rs1 (sign_extend (m := 64) imm) 4
        (Sail.BitVec.extractLsb rs2_val 31 0)
        (Store Data) false false false js.sail =
      .ok (Ok true)
        (state_after_word_store js.sail
          (load_effective_address rs1_val imm)
          (Sail.BitVec.extractLsb rs2_val 31 0))) :
    projectResult ((JoltISA.execProgram (JoltISA.swProgram imm rs2 rs1)).run js) =
      (execute_STORE imm rs2 rs1 4).run js.sail := by
  rcases swProgram_concrete_aligned imm rs2 rs1 js hcfg rs1_val rs2_val
      hrs1 hrs2 hsetup h_dword_translate h_dword_phys hwrite_dword with
    ⟨js', hjolt, hjolt_sail⟩
  have hsail := execute_SW_reduces imm rs2 rs1 js hcfg rs1_val rs2_val
    hrs1 hrs2 hsetup hwrite_word
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail, hsail]

/-- **Jolt-side misaligned SW skeleton.**

The leading `VirtualAssertStoreAlignment` should stop the Jolt program before setup,
returning Sail's store/AMO alignment exception. -/
theorem swProgram_concrete_misaligned (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState) (rs1_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
    (hmis : load_effective_address rs1_val imm &&& 3 ≠ 0) :
    (JoltISA.execProgram (JoltISA.swProgram imm rs2 rs1)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (load_effective_address rs1_val imm),
          ExceptionType.E_SAMO_Addr_Align ())) js := by
  let e :=
    (Virtaddr (load_effective_address rs1_val imm),
      ExceptionType.E_SAMO_Addr_Align ())
  have hassert :
      (JoltISA.execInstr (.VirtualAssertStoreAlignment rs1 imm (3 : BitVec 64))).run js =
        .ok (ExecutionResult.Memory_Exception e) js := by
    simpa [e, load_effective_address] using
      (JoltISA.execInstr_VirtualAssertStoreAlignment_run_misaligned rs1 imm (3 : BitVec 64)
        js rs1_val hrs1 (by simpa [load_effective_address] using hmis))
  unfold JoltISA.swProgram
  simpa [e] using
    (JoltISA.execProgram_instr_run_memory_exception
      (.VirtualAssertStoreAlignment rs1 imm (3 : BitVec 64))
      (.instr (.ADDI (.vreg 0) (.xreg rs1) imm) <|
       .instr (.ANDI (.vreg 1) (.vreg 0) (-8 : BitVec 12)) <|
       .instr (.LD 2 1 0) <|
       .instr (.SLLI (.vreg 0) (.vreg 0) (3 : BitVec 6)) <|
       .instr (.ORI (.vreg 3) (.xreg (regidx.Regidx 0)) (-1 : BitVec 12)) <|
       .instr (.SRLI (.vreg 3) (.vreg 3) (32 : BitVec 6)) <|
       .instr (.SLL (.vreg 3) (.vreg 3) (.vreg 0)) <|
       .instr (.SLL (.vreg 0) (.xreg rs2) (.vreg 0)) <|
       .instr (.XOR (.vreg 0) (.vreg 2) (.vreg 0)) <|
       .instr (.AND (.vreg 0) (.vreg 0) (.vreg 3)) <|
       .instr (.XOR (.vreg 2) (.vreg 2) (.vreg 0)) <|
       .instr (.SD 1 2 0) <|
       .done RETIRE_SUCCESS)
      js js e hassert)

/-- **Sail-side misaligned SW skeleton.**

The native Sail store should fail at the same alignment check, producing the
same store/AMO alignment exception. -/
theorem execute_SW_misaligned (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (rs1_val rs2_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (hmis : load_effective_address rs1_val imm &&& 3 ≠ 0) :
    (execute_STORE imm rs2 rs1 4).run js.sail =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (load_effective_address rs1_val imm),
          ExceptionType.E_SAMO_Addr_Align ())) js.sail := by
  let ea := load_effective_address rs1_val imm
  unfold execute_STORE
  simp only [bind, pure]
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  simp (config := { decide := true }) only []
  simp (config := { decide := true }) only [PreSail.assert, EStateM.bind, pure, EStateM.pure,
       EStateM.run, if_true]
  unfold vmem_write
  unfold SailME.run PreSail.PreSailME.run
  have hmis' :
      access_causes_misaligned_exception (Virtaddr ea) 4 false = true := by
    simpa [ea] using access_misaligned_4_unaligned_true ea hmis
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
        ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
        ExceptT.pure, ExceptT.lift,
        MonadLift.monadLift, liftM, monadLift, Functor.map,
        ext_data_get_addr, hrs1, hrs2,
        vmem_write_addr, hmis', ea]
  rfl

/-- **Misaligned public SW theorem.**

This mirrors the load-family misaligned theorem: both interpreters stop at the
alignment check and return the same exception. -/
theorem swProgram_eq_sail_misaligned (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (rs1_val rs2_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (hmis : load_effective_address rs1_val imm &&& 3 ≠ 0) :
    projectResult ((JoltISA.execProgram (JoltISA.swProgram imm rs2 rs1)).run js) =
      (execute_STORE imm rs2 rs1 4).run js.sail := by
  have hjolt := swProgram_concrete_misaligned imm rs2 rs1 js rs1_val hrs1 hmis
  have hsail := execute_SW_misaligned imm rs2 rs1 js hcfg rs1_val rs2_val hrs1 hrs2 hmis
  rw [hjolt]
  simp only [projectResult, project]
  symm
  exact hsail

end SW_main

end
