import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.W.Family

/-!
# R-type shift family plumbing

The uniform equivalence closer `rtype_eq_sail_uniform` is shape-based
(read 2 registers, write 1, return `RETIRE_SUCCESS`) and serves both
W-variant and non-W R-type instructions. It lives in
`ALUFamily/Rtype/W/Family.lean`. This file re-imports so that per-shift
files depend on a file inside their own directory tree.
-/
