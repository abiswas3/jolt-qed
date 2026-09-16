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
