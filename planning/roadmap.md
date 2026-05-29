# Roadmap

## Project 1: Bytecode Exapansion 

Update: Between March 1st - June 1st, we have been working on formally verifying jolt bytecode expansions. 
When a user submits a guest program written in RISC-V assembly to the Jolt prover, it receives a proof that the Jolt tracer ran every instruction of a Jolt program correctly. 
The program being executed is **not** the original guest program, but an "equivalent" program written in the Jolt ISA. 


The formal verification task here to show equivalence. 


## Workstreams

### 1. Compositional Lowering

Status: closed.

2026-05-19: Closed the recursive inline-expansion issue by restricting
`JoltISA.Instr` to final trace-row instructions and using expansion blocks for
source instructions that themselves inline.

### 2. Loads and Special Memory Regions

Status: planned.

Goal: make the ordinary-RAM theorem envelope explicit, then later add coverage
for readable JoltDevice regions such as input/advice/output/panic/termination.

See: `planning/JOLT_SPECIAL_MEMORY_REGION_PLAN.md`

### 3. Stores

Status: closed

Goal: finish `SW`, `SH`, and `SB` expansion proofs, including read-modify-write
splice lemmas and the relevant memory envelope.

### 4. Atomics

Status: missing.

Goal: add bytecode expansion models and equivalence theorems for the atomic
instruction family used by the Rust tracer.

### 5. `rd = x0` Policy

Status: partially closed.

Goal: model Rust's dispatch policy for `rd = x0`: no-op replacement for pure
writeback instructions, virtual-register remapping for side-effecting
instructions, and special-case handling where needed.

2026-05-19: Closed the `rd = x0` policy for pure writeback instructions with
no side effects by using Rust's no-op `ADDI x0, x0, 0` replacement path. The
side-effecting cases remain open because they need the Rust-style
virtual-register remapping rather than the pure no-op rule.

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

See: `docs/JOLT_VIRTUAL_REGISTER_RENAMING_PLAN.md`
