# JoltBytecode

Lean 4 proofs for instruction-level correctness of the Jolt ISA expansion
semantics.

The core claim is intentionally narrow: for each covered source instruction, a
Lean `JoltISA.Program` models the corresponding Jolt expansion semantics, and
the proof shows that executing that expansion has the same architectural effect
as the trusted Sail RISC-V semantics, under the stated assumptions.

The intended Rust-facing obligation is faithfulness of the modeled expansion
semantics to Jolt's Rust `cpu_exec` / inline-sequence behavior. This repository
does not prove line-by-line equivalence to the current Rust implementation, nor
does it prove that the Rust code emits exactly these Lean definitions. Exact
Rust implementation conformance is a separate downstream claim.

> [!WARNING]
> This project uses `leanprover/lean4:v4.29.0-rc4` to be compatible with both
> Mathlib and [lean-sail](https://github.com/rems-project/lean-sail) (v3). The
> lean-sail dependency targets `nightly-2026-03-05`, but that nightly has no
> cached Mathlib build. We use `v4.29.0-rc4` as the closest stable toolchain
> with Mathlib cache available. Lean-sail compiles under this toolchain despite
> the minor version mismatch.

## File Structure 

`Assumptions.lean` : Contains all the program pre-conditions. These are the list of all assumptions we make when running jolt.

### JoltISA

NOTE: This contains right now theorems and lemmas for proof suppport but 
it should not they need to be moved to InstructionEquivalence.

`JoltISA/Core.lean`: The definition of state. 
`JoltISA/Instruction.lean`: The Jolt instructions opcodes and defintion of a Jolt program
`JoltISA/RegisterAcess.lean`: How to access Jolt registers (virtual or real)
`JoltISA/MemoryAcess.lean`: How to access Jolt memory (not yet implemented, the code is scattered all across)
`JoltISA/Semntics.lean`: How the instructions update the Jolt state. This uses Instruction and RegisterAcesss
`JoltISA/VirtualRegisters`: How the virtual registers in Jolt are modelled and how they connect to sail registers
`JoltISA/Values`: Helper methods to define Semantics  (should be re-named)
`JoltISA/SystemCSR`: These help model csrs and can be be merged later.

