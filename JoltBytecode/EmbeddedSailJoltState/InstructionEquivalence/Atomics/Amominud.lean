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

def jolt_amominud (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  match ← vreg_LD_from_real 0 rs1 0 with
  | .Retire_Success () =>
      let _ ← vreg_SLTU_from_real_vs1 1 rs2 0
      let _ ← vreg_SUB_from_real_vs1 2 rs2 0
      let _ ← vreg_MUL 2 2 1
      let _ ← vreg_ADD 1 0 2
      match ← vreg_SD_from_real rs1 1 0 with
      | .Retire_Success () => vreg_ADDI_to_real rd 0 0
      | other => pure other
  | other => pure other

theorem jolt_amominud_eq_sail_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (addr rs2_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (h_jolt_load_translate : BareTranslation addr js.sail)
    (h_jolt_load_mem : FlatPhysMem addr 8 js.sail)
    (h_jolt_store_translate : StoreBareTranslation addr js.sail)
    (h_jolt_store_mem : FlatStoreMem addr 8 js.sail)
    (h_amo_translate : AtomicBareTranslation amoop.AMOMINU addr js.sail)
    (h_amo_mem : FlatAtomicMem amoop.AMOMINU addr 8 js.sail)
    (h_no_ovf : addr.toNat + 7 < 2 ^ 64)
    (h_align : addr &&& 7 = 0) :
    projectResult ((jolt_amominud rs2 rs1 rd).run js) =
      (execute_AMO amoop.AMOMINU false false rs2 rs1 8 rd).run js.sail := by
  sorry

end Atomics
