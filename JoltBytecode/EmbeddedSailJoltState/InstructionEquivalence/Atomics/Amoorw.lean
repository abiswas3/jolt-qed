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

def jolt_amoorw (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult :=
  jolt_amo_w_binop vreg_OR_from_real_vs2 rs2 rs1 rd

theorem jolt_amoorw_eq_sail_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (addr rs2_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (h_jolt_load_translate : BareTranslation (addr &&& (-8 : BitVec 64)) js.sail)
    (h_jolt_load_mem : FlatPhysMem (addr &&& (-8 : BitVec 64)) 8 js.sail)
    (h_jolt_store_translate : StoreBareTranslation (addr &&& (-8 : BitVec 64)) js.sail)
    (h_jolt_store_mem : FlatStoreMem (addr &&& (-8 : BitVec 64)) 8 js.sail)
    (h_amo_translate : AtomicBareTranslation amoop.AMOOR addr js.sail)
    (h_amo_mem : FlatAtomicMem amoop.AMOOR addr 4 js.sail)
    (h_word_no_ovf : addr.toNat + 3 < 2 ^ 64)
    (h_align : addr &&& 3 = 0) :
    projectResult ((jolt_amoorw rs2 rs1 rd).run js) =
      (execute_AMO amoop.AMOOR false false rs2 rs1 4 rd).run js.sail := by
  sorry

end Atomics
