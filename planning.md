
# Jolt-QED: State of the World

This project proves Jolt bytecode expansions are equivalent to RISC-V
instructions as specified by the Sail formal model.

## Architecture

There are three layers of proof, each using a different state model:

### 1. BytecodeExpansions/ (pure-function equivalence, 65 instructions)

**State model**: `State` — a simple record with `reg : RegFile`, `mem : Memory`,
`csr : CsrFile`, `pc : BitVec 64`, `error : Bool`. Registers are `BitVec 5 → BitVec 64`.
Read/write are plain functions (no monads, no hash maps).

**What it proves**: For each instruction, the Jolt decomposition (as a pure function
on `State`) equals the RISC-V reference semantics (also a pure function on `State`).
For example, `srai_eq_sraiJolt : Riscv.srai64 = sraiJolt`.

**65 instructions proved** in `BytecodeExpansions/Instructions/`:
Addiw, Addw, Advicelb, Adviceld, Advicelh, Advicelw,
Amoaddd, Amoaddw, Amoandd, Amoandw, Amomaxd, Amomaxud, Amomaxuw, Amomaxw,
Amomind, Amominud, Amominuw, Amominw, Amoord, Amoorw, Amoswapd, Amoswapw,
Amoxord, Amoxorw, Csrrs, Csrrw, Div, Divu, Divuw, Divw, Ecall,
Lb, Lbu, Lh, Lhu, Lrd, Lrw, Lw, Lwu, Mret, Mulh, Mulhsu, Mulw,
Rem, Remu, Remuw, Remw, Sb, Scd, Scw, Sh, Sll, Slli, Slliw, Sllw,
Sra, Srai, Sraiw, Sraw, Srl, Srli, Srliw, Srlw, Subw, Sw

### 2. SailJoltState/ (manual monadic proofs, 5 instructions)

**State model**: `SailJoltState` — duplicates all 6 fields of `SailState`
(the Sail model's `SequentialState`) plus `vregs`. `project`/`inject` manually
copy fields between JoltState and SailState.

**What it proves**: `projectResult (jolt_instr.run js) = sail_instr.run (project js)`.
This is the full monadic equivalence — Jolt's decomposition, lifted into the
Sail monadic framework, produces the same result as the native Sail instruction.

**Proof style**: Manual `sail_cases` on each monadic read, `wX_shape`/`wX_rX_roundtrip`/
`wX_wX_collapse` for register writes. ~20 lines of plumbing per instruction.

**5 instructions**: Addw, Subw, Addiw, Srai, Sraiw

### 3. EmbeddedSailJoltState/ (mvcgen proofs, 5 instructions)

**State model**: `SailJoltState` embeds `SailState` directly as a field:
`structure SailJoltState where sail : SailState; vregs : ...`.
`project js = js.sail`. Much cleaner than field duplication.

**What it proves**: Same theorem as (2), but with `WellFormed js` precondition
(all register reads succeed — true for any real RISC-V state).

**Proof style**: `@[spec]` Hoare triples + `mvcgen` tactic. The monadic plumbing
is automated. Each instruction file provides only:
- The Jolt decomposition definition (`jolt_addw`, `jolt_srai`, etc.)
- A factoring lemma (how `execute_RTYPE`/`execute_ITYPE` decomposes)
- A math bridge lemma (e.g., `extractLsb_add`, `srai_bitmask_eq_arith_shift`)

Shared infrastructure in `RtypeW.lean`:
- `WellFormed` predicate
- Primitive specs: `liftSail_rX_spec`, `liftSail_wX_spec`
- Generic R-type W framework: `liftSail_RTYPE_spec`, `vsew_spec`,
  `jolt_rtype_w_concrete`, `jolt_rtype_w_eq_sail`

**5 instructions**: Addw, Subw, Addiw, Srai, Sraiw
**Zero sorries.**

## What remains

The 65 pure-function proofs in `BytecodeExpansions/` need to be lifted to
monadic Sail equivalences (layer 3). Currently only 5 have been lifted.

The lifting pattern depends on the instruction type:
- **R-type W** (Addw, Subw, Sllw, Srlw, Sraw): generic framework in `RtypeW.lean`.
  Each new instruction needs only a factoring lemma and a math lemma.
- **I-type W** (Addiw, Slliw, Srliw, Sraiw): similar pattern, one register read + immediate.
- **Shift instructions** (Srai, Slli, Srli, Sra, Sll, Srl): read-compute-write with
  bitmask bridge. Uses primitive specs.
- **Load/store** (Lb, Lbu, Lh, Lhu, Lw, Lwu, Sb, Sh, Sw): memory operations — will
  need new specs for `liftSail(read_mem)` and `liftSail(write_mem)`.
- **Mul/Div/Rem**: similar to R-type but different Sail functions.
- **Atomic** (Amo*, Lr*, Sc*): memory + atomics — more complex Sail semantics.
- **CSR** (Csrrs, Csrrw): CSR read/write operations.
- **System** (Ecall, Mret): trap/return semantics.

The `BytecodeExpansions/` pure-function proofs provide the math bridge for each
instruction. The mvcgen framework handles the monadic plumbing. The main work
per instruction is:
1. Writing the Jolt decomposition definition
2. A factoring lemma for the Sail instruction
3. Connecting the pure-function proof to the Sail types (bridge lemma)

## File structure

```
JoltBytecode/
  BytecodeExpansions/
    Common/           -- State, read/write, format helpers
    Instructions/     -- 65 pure-function equivalence proofs

  SailJoltState/      -- manual proofs (field duplication, no WellFormed)
    Defs.lean
    RegisterOps.lean
    RegisterLemmas.lean
    JoltOps.lean
    Common.lean
    InstructionEquivalence/

  EmbeddedSailJoltState/  -- mvcgen proofs (embedded arch, WellFormed)
    Defs.lean             -- SailJoltState, liftSail, project, inject
    RegisterOps.lean      -- register lemmas, stateAfterWrite
    RtypeW.lean           -- mvcgen specs + generic W-type framework
    InstructionEquivalence/
      Addw.lean, Subw.lean, Addiw.lean, Srai.lean, Sraiw.lean
```

The two SailJolt systems are fully independent — zero cross-imports.
