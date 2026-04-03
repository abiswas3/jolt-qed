import JoltBytecode.SailJoltState.Defs
import JoltBytecode.SailJoltState.RegisterOps
import JoltBytecode.SailJoltState.JoltOps
import JoltBytecode.SailJoltState.BitVecLemmas

/-!
# Common infrastructure for Jolt ↔ SailM equivalence proofs

Re-exports all modules needed by instruction proofs.
Split into:
- Defs.lean: types, project/inject, liftSail, structural lemmas
- RegisterOps.lean: reg_cases tactic, wX_shape, wX_wX_collapse, wX_regs_spec
- JoltOps.lean: virtual registers, sail_cases, jolt_virtual_sign_extend_word
- BitVecLemmas.lean: extractLsb_add, extractLsb_sub
- RegisterLemmas.lean: wX_rX_roundtrip, readReg_insert_self, rX_after_wX
-/
