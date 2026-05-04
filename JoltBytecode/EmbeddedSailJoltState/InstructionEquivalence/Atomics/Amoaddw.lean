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
# AMOADD.W bytecode expansion statement
-/

/-- Jolt's RV64 `AMOADD.W` expansion:

```text
VirtualAssertWordAlignment rs1, 0
ANDI  v4, rs1, -8
LD    v3, v4, 0
SLLI  v4, rs1, 3
SRL   v0, v3, v4
ADD   v1, v0, rs2
ORI   v2, x0, -1
SRLI  v2, v2, 32
SLL   v2, v2, v4
SLL   v4, v1, v4
XOR   v4, v3, v4
AND   v4, v4, v2
XOR   v3, v3, v4
ANDI  v2, rs1, -8
SD    v2, v3, 0
VirtualSignExtendWord rd, v0, 0
```
-/
def jolt_amoaddw (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let addr ← liftSail (rX_bits rs1)
  if addr &&& 3 ≠ 0 then
    throw (Error.Assertion "AMOADDW: address not word-aligned")
  else do
    writeVReg 4 addr
    let _ ← vreg_ANDI 4 4 (-8 : BitVec 12)
    match ← vreg_LD 3 4 0 with
    | .Retire_Success () =>
        let _ ← vreg_SLLI_from_real 4 rs1 3
        let _ ← vreg_SRL 0 3 4
        let _ ← vreg_ADD_from_real_vs2 1 0 rs2
        writeVReg 2 0
        let _ ← vreg_ORI 2 2 (-1 : BitVec 12)
        let _ ← vreg_SRLI 2 2 32
        let _ ← vreg_SLL 2 2 4
        let _ ← vreg_SLL 4 1 4
        let _ ← vreg_XOR 4 3 4
        let _ ← vreg_AND 4 4 2
        let _ ← vreg_XOR 3 3 4
        writeVReg 2 addr
        let _ ← vreg_ANDI 2 2 (-8 : BitVec 12)
        match ← vreg_SD 2 3 0 with
        | .Retire_Success () => vreg_sign_extend_word_to_real rd 0
        | other => pure other
    | other => pure other

/-- Aligned successful-case theorem statement for RV64 `AMOADD.W`.

The Jolt side reads and writes the containing dword; the Sail side performs a
width-4 AMO at `addr`. The proof should factor the byte-splice memory lemma out
before touching this top-level theorem.
-/
theorem jolt_amoaddw_eq_sail_aligned
    (rs2 rs1 rd : regidx)
    (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail)
    (h_jolt_load_translate : BareTranslation (addr &&& (-8 : BitVec 64)) js.sail)
    (h_jolt_load_mem : FlatPhysMem (addr &&& (-8 : BitVec 64)) 8 js.sail)
    (h_jolt_store_translate : StoreBareTranslation (addr &&& (-8 : BitVec 64)) js.sail)
    (h_jolt_store_mem : FlatStoreMem (addr &&& (-8 : BitVec 64)) 8 js.sail)
    (h_amo_translate : AtomicBareTranslation amoop.AMOADD addr js.sail)
    (h_amo_mem : FlatAtomicMem amoop.AMOADD addr 4 js.sail)
    (h_word_no_ovf : addr.toNat + 3 < 2 ^ 64)
    (h_align : addr &&& 3 = 0) :
    projectResult ((jolt_amoaddw rs2 rs1 rd).run js) =
      (execute_AMO amoop.AMOADD false false rs2 rs1 4 rd).run js.sail := by
  sorry

end Atomics
