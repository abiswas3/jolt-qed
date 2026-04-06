import JoltBytecode.SailJoltState.Defs
import JoltBytecode.SailJoltState.RegisterOps
import JoltBytecode.SailJoltState.JoltOps

/-!
# Common infrastructure for Jolt ↔ SailM equivalence proofs

Re-exports all modules needed by instruction proofs.
Split into:
- Defs.lean: types, project/inject, liftSail, structural lemmas
- RegisterOps.lean: reg_cases tactic, wX_shape, wX_wX_collapse, wX_regs_spec
- JoltOps.lean: virtual registers, sail_cases, jolt_virtual_sign_extend_word
- RegisterLemmas.lean: wX_rX_roundtrip, readReg_insert_self, rX_after_wX

BitVec lemmas (extractLsb_add, extractLsb_sub) live in their respective
instruction files (Addw.lean, Subw.lean) since they are the mathematical
core of each specific proof.

-/
