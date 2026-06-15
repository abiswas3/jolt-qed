import JoltBytecode.JoltISA.Expansions.Store
import JoltBytecode.JoltISA.Semantics.Instructions
import JoltBytecode.InstructionEquivalence.LoadDefUtils
import JoltBytecode.InstructionEquivalence.StoreDefUtils
import JoltBytecode.InstructionEquivalence.StoreFamily.ProgramBlocks
import JoltBytecode.InstructionEquivalence.StoreFamily.Assumptions

/-!
# SB: top-down store-byte equivalence

`SB` is the simplest store-family proof in the new architecture.  There is no
leading alignment assertion, because every byte address is byte-aligned.  The
proof still has the same three visible phases as `SW`:

1. compute `ea`, compute the enclosing dword base, and load that dword;
2. run the Rust-faithful byte splice sequence; and
3. write the spliced dword back with `SD`.

The final bridge removes the implementation detail: writing the enclosing
spliced dword is the same hashmap update as Sail's native one-byte store.
-/

set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace SB_main

/-- The exact dword value that the Rust `SB` inline sequence writes back.

The bytecode loads the enclosing dword and replaces exactly one byte: the byte
selected by the effective address receives the low eight bits of `rs2`. -/
def sbSplicedDword (imm : BitVec 12) (rs1_val rs2_val : BitVec 64)
    (s : SailState) : BitVec 64 :=
  let ea := load_effective_address rs1_val imm
  let base := compute_aligned_dword_base_address rs1_val imm
  StoreSplice.byteSplice
    (loaded_dword_at s base)
    (Sail.BitVec.extractLsb rs2_val 7 0)
    (((ea - base).toNat) * 8)

/-- **Jolt-side reduction for SB.**

This theorem follows the program exactly as written in `JoltISA.sbProgram`.
The statement hides all scratch-register churn and exposes only the semantic
boundary: after the program retires, Sail has performed an `SD` of the spliced
enclosing dword. -/
theorem sbProgram_reduces_to_dword_store (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (rs1_val rs2_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (hsetup : StoreSplice.ByteStoreSetup
      (load_effective_address rs1_val imm)
      (compute_aligned_dword_base_address rs1_val imm))
    (h_dword_phys :
      FlatPhysMem (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
    (hwrite_dword :
      vmem_write_addr
        (Virtaddr (compute_aligned_dword_base_address rs1_val imm)) 8
        (sbSplicedDword imm rs1_val rs2_val js.sail)
        (Store Data) false false false js.sail =
      .ok (Ok true)
        (state_after_dword_store js.sail
          (compute_aligned_dword_base_address rs1_val imm)
          (sbSplicedDword imm rs1_val rs2_val js.sail))) :
    ∃ js' : SailJoltState,
      (JoltISA.execProgram (JoltISA.sbProgram imm rs2 rs1)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail =
        state_after_dword_store js.sail
          (compute_aligned_dword_base_address rs1_val imm)
          (sbSplicedDword imm rs1_val rs2_val js.sail) := by
  let writeTail : JoltISA.Program :=
    .instr (.SD (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp2) 0) <| .done RETIRE_SUCCESS
  let spliceTail : JoltISA.Program :=
    JoltISA.slliBlock (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp0) (3 : BitVec 6) <|
    .instr (.LUI (.vreg JoltISA.inlineTmp0) (0xff : BitVec 64)) <|
    JoltISA.sllBlock (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp3) JoltISA.inlineTmp4 <|
    JoltISA.sllBlock (.vreg JoltISA.inlineTmp3) (.xreg rs2) (.vreg JoltISA.inlineTmp3) JoltISA.inlineTmp4 <|
    .instr (.XOR (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp3)) <|
    .instr (.AND (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp3) (.vreg JoltISA.inlineTmp0)) <|
    .instr (.XOR (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp2) (.vreg JoltISA.inlineTmp3)) <|
    writeTail
  let base := compute_aligned_dword_base_address rs1_val imm
  let dword_new := sbSplicedDword imm rs1_val rs2_val js.sail
  let finalSail := state_after_dword_store js.sail base dword_new
  rcases StoreProgramBlocks.setupBlock spliceTail imm rs1 js hcfg rs1_val hrs1
      h_dword_phys with
    ⟨js_load, hsetup_run, hload_sail, hload_v0, hload_v1, hload_v2⟩
  rcases StoreProgramBlocks.byteSpliceBlock writeTail imm rs2 js js_load
      rs1_val rs2_val hsetup hload_sail hload_v0 hload_v1 hload_v2 hrs2 with
    ⟨js_splice, hsplice_run, hsplice_sail, hsplice_v1, hsplice_v2⟩
  have hdword_new : js_splice.vregs JoltISA.inlineTmp2 = dword_new := by
    simpa [dword_new, sbSplicedDword] using hsplice_v2
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
      (JoltISA.execProgram (JoltISA.sbProgram imm rs2 rs1)).run js =
          (JoltISA.execProgram spliceTail).run js_load := by
            simpa [JoltISA.sbProgram, spliceTail, writeTail] using hsetup_run
      _ = (JoltISA.execProgram writeTail).run js_splice := by
            simpa [spliceTail, writeTail] using hsplice_run
      _ = (JoltISA.execProgram (.done RETIRE_SUCCESS)).run js_write := by
            simpa [writeTail] using hsd_run
      _ = .ok RETIRE_SUCCESS js_write := by
            rfl
  · simpa [finalSail, base, dword_new] using hsail_write

/-- **Pure bridge for SB.**

The Jolt implementation writes a whole enclosing dword, but the dword was
constructed to differ from the original only at the target byte.  This lemma
turns that dword write into the canonical native byte-store state. -/
theorem sb_spliced_dword_store_eq_byte_store (imm : BitVec 12)
    (s : SailState) (rs1_val rs2_val : BitVec 64)
    (hsetup : StoreSplice.ByteStoreSetup
      (load_effective_address rs1_val imm)
      (compute_aligned_dword_base_address rs1_val imm))
    (hmem : ∀ addr : Nat, s.mem.get? addr ≠ none) :
    state_after_dword_store s
        (compute_aligned_dword_base_address rs1_val imm)
        (sbSplicedDword imm rs1_val rs2_val s) =
      state_after_byte_store s
        (load_effective_address rs1_val imm)
        (Sail.BitVec.extractLsb rs2_val 7 0) := by
  let ea := load_effective_address rs1_val imm
  let base := compute_aligned_dword_base_address rs1_val imm
  let dword_orig := loaded_dword_at s base
  let byte_val := Sail.BitVec.extractLsb rs2_val 7 0
  let dword_new := sbSplicedDword imm rs1_val rs2_val s
  let off := (ea - base).toNat
  have hspec : StoreSplice.IsByteSplice dword_orig dword_new byte_val off := by
    simpa [dword_new, sbSplicedDword, dword_orig, byte_val, off, ea, base, Nat.mul_comm]
      using StoreSplice.byteSplice_spec dword_orig byte_val off hsetup.offset_cases
  have hpop : ∀ k : Nat, k < 8 -> s.mem.get? (base.toNat + k) ≠ none := by
    intro k _hk
    exact hmem (base.toNat + k)
  have hload : ∀ k : Nat, k < 8 →
      dword_byte dword_orig k = loaded_byte_at s (base + BitVec.ofNat 64 k) := by
    intro k hk
    interval_cases k <;> simp [dword_orig, loaded_dword_at, dword_byte] <;> bv_decide
  have hmem_eq :
      (state_after_dword_store s base dword_new).mem =
      (state_after_byte_store s ea byte_val).mem := by
    dsimp [StoreSplice.IsByteSplice] at hspec
    exact StoreSplice.dword_store_splice_eq_byte_store_populated
      s ea base byte_val dword_orig dword_new hsetup hpop hload hspec.1 hspec.2
  have hstate :
      state_after_dword_store s base dword_new =
      state_after_byte_store s ea byte_val := by
    simpa [state_after_dword_store, state_after_byte_store] using hmem_eq
  simpa [ea, base, dword_new, byte_val] using hstate

/-- **Concrete SB execution on the Jolt side.**

After the pure bridge, the Jolt result is phrased in the same state expression
as the native Sail byte-store theorem. -/
theorem sbProgram_concrete (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (rs1_val rs2_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (hsetup : StoreSplice.ByteStoreSetup
      (load_effective_address rs1_val imm)
      (compute_aligned_dword_base_address rs1_val imm))
    (h_dword_phys :
      FlatPhysMem (compute_aligned_dword_base_address rs1_val imm) 8 js.sail)
    (hwrite_dword :
      vmem_write_addr
        (Virtaddr (compute_aligned_dword_base_address rs1_val imm)) 8
        (sbSplicedDword imm rs1_val rs2_val js.sail)
        (Store Data) false false false js.sail =
      .ok (Ok true)
        (state_after_dword_store js.sail
          (compute_aligned_dword_base_address rs1_val imm)
          (sbSplicedDword imm rs1_val rs2_val js.sail))) :
    ∃ js' : SailJoltState,
      (JoltISA.execProgram (JoltISA.sbProgram imm rs2 rs1)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail =
        state_after_byte_store js.sail
          (load_effective_address rs1_val imm)
          (Sail.BitVec.extractLsb rs2_val 7 0) := by
  rcases sbProgram_reduces_to_dword_store imm rs2 rs1 js hcfg rs1_val rs2_val
      hrs1 hrs2 hsetup h_dword_phys hwrite_dword with
    ⟨js', hjolt, hjolt_sail⟩
  refine ⟨js', hjolt, ?_⟩
  rw [hjolt_sail]
  exact sb_spliced_dword_store_eq_byte_store imm js.sail rs1_val rs2_val
    hsetup hcfg.mem_populated

/-- **Sail-side SB reduction.**

Native Sail `execute_STORE ... 1` reduces directly to the same canonical
byte-store state under an explicit successful `vmem_write` assumption. -/
theorem execute_SB_reduces (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState)
    (rs1_val rs2_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (hwrite_byte :
      vmem_write rs1 (sign_extend (m := 64) imm) 1
        (Sail.BitVec.extractLsb rs2_val 7 0)
        (Store Data) false false false js.sail =
      .ok (Ok true)
        (state_after_byte_store js.sail
          (load_effective_address rs1_val imm)
          (Sail.BitVec.extractLsb rs2_val 7 0))) :
    (execute_STORE imm rs2 rs1 1).run js.sail =
      .ok RETIRE_SUCCESS
        (state_after_byte_store js.sail
          (load_effective_address rs1_val imm)
          (Sail.BitVec.extractLsb rs2_val 7 0)) := by
  have hrs1_exists :
      ∃ v : BitVec 64,
        rX_bits rs1 js.sail = .ok v js.sail ∧
        load_effective_address rs1_val imm = v + sign_extend (m := 64) imm := by
    exact ⟨rs1_val, hrs1, rfl⟩
  exact execute_STORE_byte_eq_state_after_byte_store imm rs2 rs1 js
    rs2_val (load_effective_address rs1_val imm) hrs1_exists hrs2 hwrite_byte

/-- **Public SB theorem.**

Both interpreters start from the same `SailJoltState`; after projection, the
Jolt bytecode expansion and native Sail store step produce the same Sail state. -/
theorem sbProgram_eq_sail (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (rs1_val rs2_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (hmem : StoreFamily.StoreMemoryAssumptions
      (load_effective_address rs1_val imm)
      (compute_aligned_dword_base_address rs1_val imm) 1 js.sail) :
    projectResult ((JoltISA.execProgram (JoltISA.sbProgram imm rs2 rs1)).run js) =
      (execute_STORE imm rs2 rs1 1).run js.sail := by
  have hsetup : StoreSplice.ByteStoreSetup
      (load_effective_address rs1_val imm)
      (compute_aligned_dword_base_address rs1_val imm) :=
    StoreFamily.byteStoreSetup_of_effective_address rs1_val imm
  have h_dword_phys :
      FlatPhysMem (compute_aligned_dword_base_address rs1_val imm) 8 js.sail :=
    hmem.jolt_load_mem
  have hwrite_dword :
      vmem_write_addr
        (Virtaddr (compute_aligned_dword_base_address rs1_val imm)) 8
        (sbSplicedDword imm rs1_val rs2_val js.sail)
        (Store Data) false false false js.sail =
      .ok (Ok true)
        (state_after_dword_store js.sail
          (compute_aligned_dword_base_address rs1_val imm)
          (sbSplicedDword imm rs1_val rs2_val js.sail)) :=
    StoreFamily.vmem_write_addr_store_dword_base_reduces
      rs1_val imm (sbSplicedDword imm rs1_val rs2_val js.sail)
      js.sail hcfg hmem
  have hwrite_byte :
      vmem_write rs1 (sign_extend (m := 64) imm) 1
        (Sail.BitVec.extractLsb rs2_val 7 0)
        (Store Data) false false false js.sail =
      .ok (Ok true)
        (state_after_byte_store js.sail
          (load_effective_address rs1_val imm)
          (Sail.BitVec.extractLsb rs2_val 7 0)) :=
    StoreFamily.vmem_write_byte_store_reduces imm rs1 js.sail hcfg
      rs1_val hrs1 (Sail.BitVec.extractLsb rs2_val 7 0) hmem.sail_store_mem
  rcases sbProgram_concrete imm rs2 rs1 js hcfg rs1_val rs2_val
      hrs1 hrs2 hsetup h_dword_phys hwrite_dword with
    ⟨js', hjolt, hjolt_sail⟩
  have hsail := execute_SB_reduces imm rs2 rs1 js rs1_val rs2_val
    hrs1 hrs2 hwrite_byte
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail, hsail]

end SB_main

end
