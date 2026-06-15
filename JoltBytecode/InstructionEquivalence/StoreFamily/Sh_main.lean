import JoltBytecode.JoltISA.Expansions.Store
import JoltBytecode.JoltISA.Semantics.Instructions
import JoltBytecode.InstructionEquivalence.LoadDefUtils
import JoltBytecode.InstructionEquivalence.StoreDefUtils
import JoltBytecode.InstructionEquivalence.StoreFamily.ProgramBlocks
import JoltBytecode.InstructionEquivalence.StoreFamily.MemoryPipeline
import JoltBytecode.InstructionEquivalence.StoreFamily.Derived

/-!
# SH: top-down store-halfword equivalence

`SH` has the same read-modify-write skeleton as `SB`, but it has a leading
alignment assertion and replaces two bytes of the enclosing dword.  This file
keeps the same proof architecture visible:

* aligned Jolt execution reduces to a dword write of a pure halfword splice;
* the pure bridge identifies that dword write with a native halfword store;
* native Sail execution reduces to the same canonical state; and
* the misaligned path stops before setup and matches Sail's alignment error.
-/

set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace SH_main

/-- The exact dword value that the Rust `SH` inline sequence writes back.

The bytecode loads the enclosing dword and replaces the selected two-byte lane
with the low sixteen bits of `rs2`. -/
def shSplicedDword (imm : BitVec 12) (rs1_val rs2_val : BitVec 64)
    (s : SailState) : BitVec 64 :=
  let ea := load_effective_address rs1_val imm
  let base := compute_aligned_dword_base_address rs1_val imm
  StoreSplice.halfwordSplice
    (loaded_dword_at s base)
    (Sail.BitVec.extractLsb rs2_val 15 0)
    (((ea - base).toNat) * 8)

/-- **Jolt-side aligned reduction for SH.**

The leading assertion succeeds, so the rest of the program is the common setup
block followed by the halfword splice block and final `SD`. -/
theorem shProgram_reduces_to_dword_store (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (rs1_val rs2_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (hsetup : StoreSplice.HalfwordStoreSetup
      (load_effective_address rs1_val imm)
      (compute_aligned_dword_base_address rs1_val imm))
    (h_dword_phys :
      FlatPhysMem (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
    (hwrite_dword :
      vmem_write_addr
        (Virtaddr (compute_aligned_dword_base_address rs1_val imm)) 8
        (shSplicedDword imm rs1_val rs2_val js.sail)
        (Store Data) false false false js.sail =
      .ok (Ok true)
        (state_after_dword_store js.sail
          (compute_aligned_dword_base_address rs1_val imm)
          (shSplicedDword imm rs1_val rs2_val js.sail))) :
    ∃ js' : SailJoltState,
      (JoltISA.execProgram (JoltISA.shProgram imm rs2 rs1)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail =
        state_after_dword_store js.sail
          (compute_aligned_dword_base_address rs1_val imm)
          (shSplicedDword imm rs1_val rs2_val js.sail) := by
  let writeTail : JoltISA.Program :=
    .instr (.SD (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp2) 0) <| .done RETIRE_SUCCESS
  let spliceTail : JoltISA.Program :=
    JoltISA.slliBlock (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp0) (3 : BitVec 6) <|
    .instr (.LUI (.vreg JoltISA.inlineTmp0) (0xffff : BitVec 64)) <|
    JoltISA.sllBlock (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp3) JoltISA.inlineTmp4 <|
    JoltISA.sllBlock (.vreg JoltISA.inlineTmp3) (.xreg rs2) (.vreg JoltISA.inlineTmp3) JoltISA.inlineTmp4 <|
    .instr (.XOR (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp3)) <|
    .instr (.AND (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp0)) <|
    .instr (.XOR (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp3)) <|
    writeTail
  let base := compute_aligned_dword_base_address rs1_val imm
  let dword_new := shSplicedDword imm rs1_val rs2_val js.sail
  let finalSail := state_after_dword_store js.sail base dword_new
  rcases StoreProgramBlocks.assertHalfwordSetupBlockAligned spliceTail
      imm rs1 js hcfg rs1_val hrs1 hsetup.halfword_aligned
      h_dword_phys with
    ⟨js_load, hsetup_run, hload_sail, hload_v0, hload_v1, hload_v2⟩
  rcases StoreProgramBlocks.halfwordSpliceBlock writeTail imm rs2 js js_load
      rs1_val rs2_val hsetup hload_sail hload_v0 hload_v1 hload_v2 hrs2 with
    ⟨js_splice, hsplice_run, hsplice_sail, hsplice_v1, hsplice_v2⟩
  have hdword_new : js_splice.vregs JoltISA.inlineTmp2 = dword_new := by
    simpa [dword_new, shSplicedDword] using hsplice_v2
  have hwrite_for_sd :
      vmem_write_addr (Virtaddr base) 8 dword_new
        (Store Data) false false false js_splice.sail =
      .ok (Ok true) finalSail := by
    rw [hsplice_sail]
    simpa [base, dword_new, finalSail] using hwrite_dword
  rcases StoreProgramBlocks.sdWriteBlock (.done RETIRE_SUCCESS)
      js_splice base dword_new finalSail hsplice_v1 hdword_new
      (by simpa [base] using StoreFamily.store_dword_base_aligns rs1_val imm)
      hwrite_for_sd with
    ⟨js_write, hsd_run, hsail_write, _hvregs_write⟩
  refine ⟨js_write, ?_, ?_⟩
  · calc
      (JoltISA.execProgram (JoltISA.shProgram imm rs2 rs1)).run js =
          (JoltISA.execProgram spliceTail).run js_load := by
            simpa [JoltISA.shProgram, spliceTail, writeTail] using hsetup_run
      _ = (JoltISA.execProgram writeTail).run js_splice := by
            simpa [spliceTail, writeTail] using hsplice_run
      _ = (JoltISA.execProgram (.done RETIRE_SUCCESS)).run js_write := by
            simpa [writeTail] using hsd_run
      _ = .ok RETIRE_SUCCESS js_write := by
            rfl
  · simpa [finalSail, base, dword_new] using hsail_write

/-- **Pure bridge for SH.**

The Jolt dword write is equivalent to a native halfword store because the
spliced dword changes exactly the two target bytes and preserves all other
bytes in the enclosing dword. -/
theorem sh_spliced_dword_store_eq_halfword_store (imm : BitVec 12)
    (s : SailState) (rs1_val rs2_val : BitVec 64)
    (hsetup : StoreSplice.HalfwordStoreSetup
      (load_effective_address rs1_val imm)
      (compute_aligned_dword_base_address rs1_val imm))
    (hbytes : DwordBytesPresent
      (compute_aligned_dword_base_address rs1_val imm) s) :
    state_after_dword_store s
        (compute_aligned_dword_base_address rs1_val imm)
        (shSplicedDword imm rs1_val rs2_val s) =
      state_after_halfword_store s
        (load_effective_address rs1_val imm)
        (Sail.BitVec.extractLsb rs2_val 15 0) := by
  let ea := load_effective_address rs1_val imm
  let base := compute_aligned_dword_base_address rs1_val imm
  let dword_orig := loaded_dword_at s base
  let halfword_val := Sail.BitVec.extractLsb rs2_val 15 0
  let dword_new := shSplicedDword imm rs1_val rs2_val s
  let off := (ea - base).toNat
  have hspec : StoreSplice.IsHalfwordSplice dword_orig dword_new halfword_val off := by
    simpa [dword_new, shSplicedDword, dword_orig, halfword_val, off, ea, base, Nat.mul_comm]
      using StoreSplice.halfwordSplice_spec dword_orig halfword_val off hsetup.offset_cases
  have hpop : ∀ k : Nat, k < 8 -> s.mem.get? (base.toNat + k) ≠ none := by
    intro k hk
    exact hbytes.present k hk
  have hload : ∀ k : Nat, k < 8 →
      dword_byte dword_orig k = loaded_byte_at s (base + BitVec.ofNat 64 k) := by
    intro k hk
    interval_cases k <;> simp [dword_orig, loaded_dword_at, dword_byte] <;> bv_decide
  have hmem_eq :
      (state_after_dword_store s base dword_new).mem =
      (state_after_halfword_store s ea halfword_val).mem := by
    dsimp [StoreSplice.IsHalfwordSplice] at hspec
    exact StoreSplice.dword_store_splice_eq_halfword_store_populated
      s ea base halfword_val dword_orig dword_new hsetup hpop hload hspec.1 hspec.2
  have hstate :
      state_after_dword_store s base dword_new =
      state_after_halfword_store s ea halfword_val := by
    simpa [state_after_dword_store, state_after_halfword_store] using hmem_eq
  simpa [ea, base, dword_new, halfword_val] using hstate

/-- **Concrete aligned SH execution on the Jolt side.** -/
theorem shProgram_concrete_aligned (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (rs1_val rs2_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (hsetup : StoreSplice.HalfwordStoreSetup
      (load_effective_address rs1_val imm)
      (compute_aligned_dword_base_address rs1_val imm))
    (h_dword_phys :
      FlatPhysMem (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
    (hwrite_dword :
      vmem_write_addr
        (Virtaddr (compute_aligned_dword_base_address rs1_val imm)) 8
        (shSplicedDword imm rs1_val rs2_val js.sail)
        (Store Data) false false false js.sail =
      .ok (Ok true)
        (state_after_dword_store js.sail
          (compute_aligned_dword_base_address rs1_val imm)
          (shSplicedDword imm rs1_val rs2_val js.sail))) :
    ∃ js' : SailJoltState,
      (JoltISA.execProgram (JoltISA.shProgram imm rs2 rs1)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail =
        state_after_halfword_store js.sail
          (load_effective_address rs1_val imm)
          (Sail.BitVec.extractLsb rs2_val 15 0) := by
  rcases shProgram_reduces_to_dword_store imm rs2 rs1 js hcfg rs1_val rs2_val
      hrs1 hrs2 hsetup h_dword_phys hwrite_dword with
    ⟨js', hjolt, hjolt_sail⟩
  refine ⟨js', hjolt, ?_⟩
  rw [hjolt_sail]
  exact sh_spliced_dword_store_eq_halfword_store imm js.sail rs1_val rs2_val
    hsetup h_dword_phys.bytes

/-- **Sail-side aligned SH reduction.** -/
theorem execute_SH_reduces (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState)
    (rs1_val rs2_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (hwrite_halfword :
      vmem_write rs1 (sign_extend (m := 64) imm) 2
        (Sail.BitVec.extractLsb rs2_val 15 0)
        (Store Data) false false false js.sail =
      .ok (Ok true)
        (state_after_halfword_store js.sail
          (load_effective_address rs1_val imm)
          (Sail.BitVec.extractLsb rs2_val 15 0))) :
    (execute_STORE imm rs2 rs1 2).run js.sail =
      .ok RETIRE_SUCCESS
        (state_after_halfword_store js.sail
          (load_effective_address rs1_val imm)
          (Sail.BitVec.extractLsb rs2_val 15 0)) := by
  have hrs1_exists :
      ∃ v : BitVec 64,
        rX_bits rs1 js.sail = .ok v js.sail ∧
        load_effective_address rs1_val imm = v + sign_extend (m := 64) imm := by
    exact ⟨rs1_val, hrs1, rfl⟩
  exact execute_STORE_halfword_eq_state_after_halfword_store imm rs2 rs1 js
    rs2_val (load_effective_address rs1_val imm) hrs1_exists hrs2 hwrite_halfword

/-- **Aligned public SH theorem.** -/
theorem shProgram_eq_sail_aligned (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (rs1_val rs2_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (hmem : StoreFamily.StoreMemoryContext
      (load_effective_address rs1_val imm)
      (compute_aligned_dword_base_address rs1_val imm) 2 js.sail)
    (halign : load_effective_address rs1_val imm &&& (1 : BitVec 64) = 0) :
    projectResult ((JoltISA.execProgram (JoltISA.shProgram imm rs2 rs1)).run js) =
      (execute_STORE imm rs2 rs1 2).run js.sail := by
  have hsetup : StoreSplice.HalfwordStoreSetup
      (load_effective_address rs1_val imm)
      (compute_aligned_dword_base_address rs1_val imm) :=
    StoreFamily.halfwordStoreSetup_of_effective_address
      rs1_val imm halign
  have h_dword_phys :
      FlatPhysMem (compute_aligned_dword_base_address rs1_val imm) 8 js.sail :=
    hmem.jolt_load_mem
  have hwrite_dword :
      vmem_write_addr
        (Virtaddr (compute_aligned_dword_base_address rs1_val imm)) 8
        (shSplicedDword imm rs1_val rs2_val js.sail)
        (Store Data) false false false js.sail =
      .ok (Ok true)
        (state_after_dword_store js.sail
          (compute_aligned_dword_base_address rs1_val imm)
          (shSplicedDword imm rs1_val rs2_val js.sail)) :=
    StoreFamily.vmem_write_addr_store_dword_base_reduces
      rs1_val imm (shSplicedDword imm rs1_val rs2_val js.sail)
      js.sail hcfg hmem
  have hwrite_halfword :
      vmem_write rs1 (sign_extend (m := 64) imm) 2
        (Sail.BitVec.extractLsb rs2_val 15 0)
        (Store Data) false false false js.sail =
      .ok (Ok true)
        (state_after_halfword_store js.sail
          (load_effective_address rs1_val imm)
          (Sail.BitVec.extractLsb rs2_val 15 0)) :=
    StoreFamily.vmem_write_halfword_store_reduces imm rs1 js.sail hcfg
      rs1_val hrs1 (Sail.BitVec.extractLsb rs2_val 15 0)
      halign hmem.sail_store_mem
  rcases shProgram_concrete_aligned imm rs2 rs1 js hcfg rs1_val rs2_val
      hrs1 hrs2 hsetup h_dword_phys hwrite_dword with
    ⟨js', hjolt, hjolt_sail⟩
  have hsail := execute_SH_reduces imm rs2 rs1 js rs1_val rs2_val
    hrs1 hrs2 hwrite_halfword
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail, hsail]

/-- **Jolt-side misaligned SH reduction.**

The leading `VirtualAssertHalfwordAlignment` is the whole proof: it returns the
Sail store/AMO alignment exception and does not run the setup block. -/
theorem shProgram_concrete_misaligned (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState) (rs1_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
    (hmis : load_effective_address rs1_val imm &&& 1 ≠ 0) :
    (JoltISA.execProgram (JoltISA.shProgram imm rs2 rs1)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (load_effective_address rs1_val imm),
          ExceptionType.E_SAMO_Addr_Align ())) js := by
  let tail : JoltISA.Program :=
    .instr (.ADDI (.vreg JoltISA.inlineTmp0) (.xreg rs1) imm) <|
    .instr (.ANDI (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp0) (-8 : BitVec 12)) <|
    .instr (.LD (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp1) 0) <|
    JoltISA.slliBlock (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp0) (3 : BitVec 6) <|
    .instr (.LUI (.vreg JoltISA.inlineTmp0) (0xffff : BitVec 64)) <|
    JoltISA.sllBlock (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp3) JoltISA.inlineTmp4 <|
    JoltISA.sllBlock (.vreg JoltISA.inlineTmp3) (.xreg rs2) (.vreg JoltISA.inlineTmp3) JoltISA.inlineTmp4 <|
    .instr (.XOR (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp3)) <|
    .instr (.AND (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp0)) <|
    .instr (.XOR (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp3)) <|
    .instr (.SD (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp2) 0) <|
    .done RETIRE_SUCCESS
  have h := StoreProgramBlocks.assertHalfwordBlockMisaligned tail
    imm rs1 js rs1_val hrs1 hmis
  simpa [JoltISA.shProgram, tail] using h

/-- **Sail-side misaligned SH reduction.**

Sail reads `rs2` before it reaches the memory alignment check, so the source
register read remains an explicit hypothesis on the misaligned path. -/
theorem execute_SH_misaligned (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState)
    (rs1_val rs2_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (hmis : load_effective_address rs1_val imm &&& 1 ≠ 0) :
    (execute_STORE imm rs2 rs1 2).run js.sail =
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
      access_causes_misaligned_exception (Virtaddr ea) 2 false = true := by
    simpa [ea] using access_misaligned_2_unaligned_true ea hmis
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
        ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
        ExceptT.pure, ExceptT.lift,
        MonadLift.monadLift, liftM, monadLift, Functor.map,
        ext_data_get_addr, hrs1, hrs2,
        vmem_write_addr, hmis', ea]
  rfl

/-- **Misaligned public SH theorem.** -/
theorem shProgram_eq_sail_misaligned (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState)
    (rs1_val rs2_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (hmis : load_effective_address rs1_val imm &&& 1 ≠ 0) :
    projectResult ((JoltISA.execProgram (JoltISA.shProgram imm rs2 rs1)).run js) =
      (execute_STORE imm rs2 rs1 2).run js.sail := by
  have hjolt := shProgram_concrete_misaligned imm rs2 rs1 js rs1_val hrs1 hmis
  have hsail := execute_SH_misaligned imm rs2 rs1 js rs1_val rs2_val hrs1 hrs2 hmis
  rw [hjolt]
  simp only [projectResult, project]
  symm
  exact hsail

/-- **Main public SH theorem.**

The caller supplies only the compact memory bundle. The proof cases on the
halfword alignment guard and reuses the aligned or misaligned branch theorem. -/
theorem shProgram_eq_sail (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState)
    (h : StoreFamily.StoreProgramEqSailAssumptions imm rs2 rs1 js) :
    projectResult ((JoltISA.execProgram (JoltISA.shProgram imm rs2 rs1)).run js) =
      (execute_STORE imm rs2 rs1 2).run js.sail := by
  let ea := load_effective_address h.rs1_val imm
  by_cases halign :
      ea &&& (1 : BitVec 64) = 0
  · have hmem : StoreFamily.StoreMemoryContext
        (load_effective_address h.rs1_val imm)
        (compute_aligned_dword_base_address h.rs1_val imm) 2 js.sail :=
      h.accessContext 2
        (h.halfwordStore (by simpa [ea] using halign))
    exact shProgram_eq_sail_aligned imm rs2 rs1 js h.cfg h.rs1_val h.rs2_val
      h.rs1_read.value_eq h.rs2_read.value_eq hmem
      (by simpa [ea] using halign)
  · exact shProgram_eq_sail_misaligned imm rs2 rs1 js h.rs1_val h.rs2_val
      h.rs1_read.value_eq h.rs2_read.value_eq (by simpa [ea] using halign)

end SH_main

end
