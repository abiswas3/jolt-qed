# Non-negotiable: NEVER re-create instruction semantics

- Instruction execution MUST use `JoltISA.execInstr`. Never introduce a second interpreter or implement instruction behavior in `JoltConstraints`.
- Instruction semantics and semantic helpers MUST live in `JoltBytecode/JoltISA`. Witness construction, tracing, and metadata code MUST NOT duplicate operand comparisons, arithmetic behavior, jump decisions, or other instruction semantics.
- When witness extraction needs a semantic calculation already performed by execution, reuse the ISA implementation. If necessary, extract that calculation into a shared helper in `JoltBytecode/JoltISA/semantic_helpers.lean` and make BOTH `execInstr` and witness extraction call it. Merely placing a duplicate helper in the ISA directory is NOT sufficient: execution must actually use the same helper.
- Rust is the reference for witness encoding, not permission to create an alternative Lean execution semantics. Reading ISA pre/post states, encoding values into fields, padding, and indexing witness arrays belong to witness construction; reimplementing instruction behavior does not.
- This prohibition concerns duplicated executable semantics, not the mathematical statements of constraints or correctness theorems. An equivalence proof is not a substitute for sharing the implementation.
- Preserve ISA behavior when extracting helpers; check the existing equivalence proofs and build. Do not expand to unrelated instructions or change the state type without approval.

## Concrete mistake and correction: `ShouldBranch`

BAD: we implemented `HonestWitness.branchDecision` in `JoltConstraints/witness_helpers/branch.lean` with its own comparisons, for example:

```lean
| .BEQ lhs rhs _ => do
    return (← JoltISA.readSrc lhs) == (← JoltISA.readSrc rhs)
```

At the same time, `JoltISA.execInstr` separately read those operands and compared them in its BEQ case. Calling ISA register-read helpers did NOT make this acceptable: the branch decision itself was duplicated. Matching Rust or proving that read errors propagate did NOT remove that duplication.

FIX: move the comparisons into the single ISA-owned `JoltISA.branchDecision` in `JoltBytecode/JoltISA/semantic_helpers.lean`. It covers `BEQ`, `BNE`, `BLT`, `BGE`, `BLTU`, and `BGEU`. Each corresponding `execInstr` case calls it, for example:

```lean
| .BEQ lhs rhs imm => do
    if ← branchDecision (.BEQ lhs rhs imm) then
      let pc ← liftSail (Sail.readReg Register.PC)
      liftSail (jump_to (pc + sign_extend (m := 64) imm))
    else
      pure RETIRE_SUCCESS
```

`HonestWitness.ShouldBranch` calls that SAME helper on the recorded pre-state:

```lean
JoltISA.branchDecision program.expandedBytecode[row.rowIndex].instruction row.preState
```

The witness code only encodes the returned Boolean as field `1` or `0`, handles padding, and proves the error case impossible using the row's successful ISA execution. There is NO witness-side branch comparison. The read-only predicate is evaluated again, but its semantics are defined only once; the instruction is not executed again.

Do NOT replace this with a PC-change heuristic: a taken branch can target the normal fallthrough address, so the PC transition alone does not always reveal whether its condition held.

# Modelling Jolt Sumchecks as Explicit Constraints

For this project the PCS is out of scope. We will treat polynomial openings as exact.

[Jolt](/Users/ari.biswas/Work-with-A16z/jolt) can be thought to be made of two components.
1. A tracer that takes a program written in the Jolt ISA, and lazily computes evaluations of multilinear polynomials. 
These evaluations of course fully define the  coefficients of the polynomial (via interpolation).
These polynomials can be viewed as the NP witness. 
So you can think of the output of the tracer in many views (1) Arrays with numbers (2) Basis polynomial evaluations (3) NP witness. 
Now the HONEST tracer creates a specific set of polynomials. 
That is given any program written in the Jolt ISA - this corresponds to a unique set of polynomials. 
Thus, there is a map (not necessarily injective or surjective (though could be), but a function) from Jolt programs to these polynomials.
2. The map is specified by the ISA, and then a rust code that builds these polynomials from pre-post state of running program. Now we already have a way to get post state from pre-state, we have the ISA semantics. 
So there is no reason why we cannot define this map in Lean. 
3. The question is which polynomials should we compute. Well everyone in Jolt, but before we do, where do we start, do we start with the sum-checks and write them down, and then fill in the remaining in the tracer? Or start with modelling the tracer. 
We have done a very very poor job of this in the present constraints (`JoltConstraints`) (so the goal is to interactively, add new files and remove the old ones).
We also do not directly want to write things as polynomials. 
4. These arrays/columns which are secretly just evaluations of polynomials (we should find the best most efficient representation for them), if you think of them as variables, then Jolt is just a constraint system on these variables. 
The sum-checks and all other mallarkey is simply a randomised test for this constraint, very similar to Frievald's algorithm.

So far read the above, and we will have a discussion, and then we will further discuss. 

## Validation

Run commands from `/Users/ari.biswas/Lean/lz-qed`:

```sh
lake build
```

Both `JoltBytecode` and `JoltConstraints` are default targets in
`lakefile.toml`, so the bare build includes the complete constraint suite.

For a focused change, first compile the edited leaf file with
`lake env lean JoltConstraints/<file>.lean`, then compile the importing theorem
file or run `lake build JoltConstraints.ConstraintCompleteness`. Keep imports
explicit and preserve the package's `autoImplicit := false` discipline.
