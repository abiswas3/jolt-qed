import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Itype.W.Family

/-!
# I-type shift family plumbing

The uniform equivalence closer `itype_eq_sail_uniform` is shape-based
(read 1 register, write 1, return `RETIRE_SUCCESS`) and serves both
W-variant and non-W I-type instructions. Defined in
`ALUFamily/Itype/W/Family.lean`; re-imported here so per-shift files
depend on a file inside their own directory tree.
-/
