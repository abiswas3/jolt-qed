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

/-!
# AMOADD.D bytecode expansion statement
-/

/-- Jolt's `AMOADD.D` expansion:

```text
LD   v1, rs1, 0
ADD  v0, v1, rs2
SD   rs1, v0, 0
ADDI rd, v1, 0
```
-/
def jolt_amoaddd (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  match ← vreg_LD_from_real 1 rs1 0 with
  | .Retire_Success () =>
      let _ ← vreg_ADD_from_real_vs2 0 1 rs2
      match ← vreg_SD_from_real rs1 0 0 with
      | .Retire_Success () => vreg_ADDI_to_real rd 1 0
      | other => pure other
  | other => pure other

/-- Aligned successful-case theorem statement for `AMOADD.D`.

The proof should show that the normal Jolt `LD`/`SD` read-modify-write is
equivalent to Sail's atomic read-modify-write with `aq = false`, `rl = false`.
-/
theorem jolt_amoaddd_eq_sail_aligned
    (rs2 rs1 rd : regidx)
    (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (h_jolt_load_translate : BareTranslation addr js.sail)
    (h_jolt_load_mem : FlatPhysMem addr 8 js.sail)
    (h_jolt_store_translate : StoreBareTranslation addr js.sail)
    (h_jolt_store_mem : FlatStoreMem addr 8 js.sail)
    (h_amo_translate : AtomicBareTranslation amoop.AMOADD addr js.sail)
    (h_amo_mem : FlatAtomicMem amoop.AMOADD addr 8 js.sail)
    (h_no_ovf : addr.toNat + 7 < 2 ^ 64)
    (h_align : addr &&& 7 = 0) :
    projectResult ((jolt_amoaddd rs2 rs1 rd).run js) =
      (execute_AMO amoop.AMOADD false false rs2 rs1 8 rd).run js.sail := by
  sorry

end Atomics
