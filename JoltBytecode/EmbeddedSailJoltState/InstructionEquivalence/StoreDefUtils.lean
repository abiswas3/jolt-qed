import JoltBytecode.EmbeddedSailJoltState.MemoryWriteReasoning
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.MonadReduction

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

/-!
# Shared Sail store-definition helpers

These lemmas collapse the relevant part of Sail's store pipeline to explicit
hashmap updates. The instruction-specific proofs should use these results and
return immediately to the pure memory model.
-/

-- Under the standard store assumptions, Sail's `execute_STORE` for width 4
-- reduces to the corresponding hashmap update.
theorem execute_STORE_word_eq_state_after_word_store
    (imm : BitVec 12) (rs2 rs1 : regidx) (js : SailJoltState)
    (rs2_val ea base : BitVec 64)
    (hrs1 : ∃ rs1_val : BitVec 64,
      rX_bits rs1 js.sail = .ok rs1_val js.sail ∧
      ea = rs1_val + sign_extend (m := 64) imm)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (hsetup : DwordStoreSetup ea base)
    (hcfg : JoltConfig js.sail)
    (hwrite :
      vmem_write rs1 (sign_extend (m := 64) imm) 4 (Sail.BitVec.extractLsb rs2_val 31 0)
        (Store Data) false false false js.sail =
      .ok (Ok true)
        (state_after_word_store js.sail ea (Sail.BitVec.extractLsb rs2_val 31 0))) :
    (execute_STORE imm rs2 rs1 4).run js.sail =
      .ok RETIRE_SUCCESS
        (state_after_word_store js.sail ea (Sail.BitVec.extractLsb rs2_val 31 0)) := by
  unfold execute_STORE
  rw [show (4 ≤b _root_.LeanRV64D.Functions.xlen_bytes) = true by rfl]
  have hassert :
      EStateM.run (Sail.assert true "extensions/I/base_insts.sail:320.28-320.29") js.sail =
      .ok () js.sail := by
    rfl
  have hrs2' : EStateM.run (rX_bits rs2) js.sail = .ok rs2_val js.sail := by
    simpa using hrs2
  change EStateM.run
      ((Sail.assert true "extensions/I/base_insts.sail:320.28-320.29").bind fun _ =>
        (rX_bits rs2).bind fun rs2_val' =>
          (EStateM.pure (Sail.BitVec.extractLsb rs2_val' 31 0)).bind fun y =>
            (vmem_write rs1 (sign_extend (m := 64) imm) 4 y (Store Data) false false false).bind fun res =>
              match res with
              | Ok _ => EStateM.pure RETIRE_SUCCESS
              | Err e => EStateM.pure e)
      js.sail =
    .ok RETIRE_SUCCESS
      (state_after_word_store js.sail ea (Sail.BitVec.extractLsb rs2_val 31 0))
  rw [run_bind_eq_ok hassert]
  rw [run_bind_eq_ok hrs2']
  have hwrite' :
      EStateM.run
        (vmem_write rs1 (sign_extend (m := 64) imm) 4 (Sail.BitVec.extractLsb rs2_val 31 0)
          (Store Data) false false false)
        js.sail =
      .ok (Ok true)
        (state_after_word_store js.sail ea (Sail.BitVec.extractLsb rs2_val 31 0)) := by
    simpa using hwrite
  rw [run_bind_pure]
  rw [run_bind_eq_ok hwrite']
  rfl

end
