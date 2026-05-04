import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Atomics.Common

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace Atomics

def jolt_amominuw (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  match ← jolt_amo_word_pre64 rs1 0 3 4 with
  | .Retire_Success () =>
      let _ ← vreg_zero_extend_word_from_real 1 rs2
      let _ ← vreg_zero_extend_word 2 0
      let _ ← vreg_SLTU 2 1 2
      let _ ← vreg_SUB_from_real_vs1 1 rs2 0
      let _ ← vreg_MUL 1 1 2
      let _ ← vreg_ADD 1 1 0
      jolt_amo_word_post64 rs1 rd 1 3 4 2 0
  | other => pure other

theorem jolt_amominuw_eq_sail_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (addr rs2_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (h_jolt_load_translate : BareTranslation (addr &&& (-8 : BitVec 64)) js.sail)
    (h_jolt_load_mem : FlatPhysMem (addr &&& (-8 : BitVec 64)) 8 js.sail)
    (h_jolt_store_translate : StoreBareTranslation (addr &&& (-8 : BitVec 64)) js.sail)
    (h_jolt_store_mem : FlatStoreMem (addr &&& (-8 : BitVec 64)) 8 js.sail)
    (h_amo_translate : AtomicBareTranslation amoop.AMOMINU addr js.sail)
    (h_amo_mem : FlatAtomicMem amoop.AMOMINU addr 4 js.sail)
    (h_word_no_ovf : addr.toNat + 3 < 2 ^ 64)
    (h_align : addr &&& 3 = 0) :
    projectResult ((jolt_amominuw rs2 rs1 rd).run js) =
      (execute_AMO amoop.AMOMINU false false rs2 rs1 4 rd).run js.sail := by
  sorry

end Atomics
