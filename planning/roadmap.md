# Roadmap

## Project 1: Bytecode Exapansion 

Update: Between March 1st - June 1st, we have been working on formally verifying jolt bytecode expansions. 
When a user submits a guest program written in RISC-V assembly to the Jolt prover, it receives a proof that the Jolt tracer ran every instruction of a Jolt program correctly. 
The program being executed is **not** the original guest program, but an "equivalent" program written in the Jolt ISA. 


The formal verification task here to show equivalence. 


## Workstreams

### 1. Compositional Lowering

Status: planned.

Goal: prove lowering theorems once for recursively expanding instructions, then
reuse them in caller proofs instead of expanding every caller manually.

See: `planning/JOLT_COMPOSITIONAL_LOWERING_PLAN.md`

### 2. Loads and Special Memory Regions

Status: planned.

Goal: make the ordinary-RAM theorem envelope explicit, then later add coverage
for readable JoltDevice regions such as input/advice/output/panic/termination.

See: `planning/JOLT_SPECIAL_MEMORY_REGION_PLAN.md`

### 3. Stores

Status: incomplete.

Goal: finish `SW`, `SH`, and `SB` expansion proofs, including read-modify-write
splice lemmas and the relevant memory envelope.

### 4. Atomics

Status: missing.

Goal: add bytecode expansion models and equivalence theorems for the atomic
instruction family used by the Rust tracer.

### 5. `rd = x0` Policy

Status: planned.

Goal: model Rust's dispatch policy for `rd = x0`: no-op replacement for pure
writeback instructions, virtual-register remapping for side-effecting
instructions, and special-case handling where needed.

### 6. Advice Tape

Status: later.

Goal: connect explicit Lean advice values to Rust's byte-oriented advice/device
state.

### 7. Trace Metadata

Status: later.

Goal: separately verify row metadata such as `virtual_sequence_remaining`,
`is_first_in_sequence`, compression flags, and address metadata.

See: `planning/JOLT_TRACE_METADATA_PLAN.md`

### 8. Virtual Register Renaming

Status: later.

Goal: prove a renaming-invariance theorem connecting fixed Lean virtual-register
templates to Rust allocator-chosen virtual registers.

See: `planning/JOLT_VIRTUAL_REGISTER_RENAMING_PLAN.md`

## Milestones


# Next Block 

## Lookup Table Verification

First target: the `AND` table.

1. Prove Boolean-hypercube agreement:

   ```rust
   evaluate_mle_AND(bits(index)) = materialize_entry_AND(index)
   ```

   In words: on every Boolean point of the lookup-table hypercube, the verifier
   polynomial agrees with the finite AND table.

2. Prove the full MLE theorem:

   ```rust
   evaluate_mle_AND(r)
     = multilinear extension of materialize_entry_AND
   ```

   In words: the Rust `evaluate_mle` code really evaluates the multilinear
   extension of the AND lookup table, not just an arbitrary polynomial that
   happens to agree on tested points.
