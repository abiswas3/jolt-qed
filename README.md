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

## Theorem Shape

For ordinary instruction families, the public theorem shape is:

```lean
projectResult ((JoltISA.execProgram (JoltISA.someProgram ...)).run js) =
  (execute_SAIL_INSTRUCTION ...).run js.sail
```

Some families use a more precise projection or relation:

- system instructions use `systemProjectResult` where persistent Jolt virtual
  CSR state must be overlaid onto Sail CSR state;
- `EBREAK` uses an explicit relation because Jolt's self-loop termination marker
  and Sail's architectural breakpoint trap are intentionally different result
  constructors;
- memory and AMO proofs carry ordinary-memory, alignment, and byte-population
  assumptions where needed;
- advice-backed instructions quantify over explicit advice/oracle values.

## Coverage

This table describes the current `lake build JoltBytecode` proof surface, plus
explicit deferred and out-of-scope areas.

| Area | Instructions | Status | Claim and assumptions |
| --- | --- | --- | --- |
| R-type ALU shifts and word ops | `SLL`, `SRL`, `SRA`, `ADDW`, `SUBW`, `MULW`, `SLLW`, `SRLW`, `SRAW` | Proved | Jolt expansion equals Sail architectural semantics via `*_Program_eq_sail`. |
| I-type ALU shifts and word ops | `SLLI`, `SRLI`, `SRAI`, `ADDIW`, `SLLIW`, `SRLIW`, `SRAIW` | Proved | Jolt expansion equals Sail architectural semantics via `*_Program_eq_sail`. |
| High multiplication | `MULH`, `MULHSU` | Proved | Jolt expansion modeled as `JoltISA.Program`; proved against Sail multiply semantics. |
| Division and remainder with advice | `DIV`, `DIVU`, `DIVW`, `DIVUW`, `REM`, `REMU`, `REMW`, `REMUW` | Proved with explicit advice | The expansion is proved equivalent when supplied honest quotient/remainder advice. Proofs also expose soundness facts for successful guarded runs. |
| Ordinary loads | `LB`, `LBU`, `LH`, `LHU`, `LW`, `LWU` | Proved under memory assumptions | Covers ordinary Sail memory, including aligned and misaligned branches according to the Jolt/Sail platform envelope. Does not prove Jolt special memory regions. |
| Ordinary stores | `SB`, `SH`, `SW` | Proved under memory assumptions | Covers ordinary Sail memory and read-modify-write splice reasoning. Does not prove Jolt special memory regions. |
| AMO dword operations | `AMOADD.D`, `AMOAND.D`, `AMOOR.D`, `AMOXOR.D`, `AMOSWAP.D`, `AMOMIN.D`, `AMOMAX.D`, `AMOMINU.D`, `AMOMAXU.D` | Proved under memory assumptions | Jolt AMO expansion equals Sail AMO semantics in the ordinary-memory envelope. |
| AMO word operations | `AMOADD.W`, `AMOAND.W`, `AMOOR.W`, `AMOXOR.W`, `AMOSWAP.W`, `AMOMIN.W`, `AMOMAX.W`, `AMOMINU.W`, `AMOMAXU.W` | Proved under memory assumptions | Jolt AMO expansion equals Sail AMO semantics in the ordinary-memory envelope. |
| Advice loads | `ADVICELB`, `ADVICELH`, `ADVICELW`, `ADVICELD` | Proved with explicit advice | Formal advice values are explicit inputs to the Jolt ISA. Rust byte-tape packing/cursor behavior is not part of this theorem. |
| System trap/control | `ECALL`, `EBREAK`, `MRET` | Proved with system projection/relation | `ECALL` and `MRET` use system CSR projection assumptions. `EBREAK` is related to Sail's breakpoint trap through an explicit result relation, not raw equality. |
| CSR | `CSRRW` | Proved with system CSR assumptions | Proves the supported ZeroOS machine CSR path against Sail CSR semantics under explicit access/legalizer assumptions. |
| CSR read-set | `CSRRS` | Not in root build | Deferred for now. Expected to use the same system CSR projection discipline as `CSRRW`. |
| Load-reserved | `LR.W`, `LR.D` | Deferred | Current Sail exposes reservation behavior through opaque hooks such as `load_reservation`; no closed equivalence theorem is claimed. |
| Store-conditional | `SC.W`, `SC.D` | Deferred | Current Sail exposes reservation behavior through opaque hooks such as `match_reservation` and `cancel_reservation`; no closed equivalence theorem is claimed. |
| Jolt special memory regions | N/A | Out of scope | This version does not prove Jolt runtime/device/special-memory behavior. The memory theorems are about ordinary Sail memory. |
| Trace metadata | N/A | Out of scope for semantic equivalence | Current theorems prove architectural effects, not exact row metadata such as virtual-sequence counters, first-row flags, compression flags, or PC metadata. |
| Exact Rust implementation conformance | N/A | Out of scope | The Lean proof does not prove that current Rust source code emits or executes exactly these definitions. A future conformance layer would need generated manifests, golden tests, extraction, or Rust verification. |

## Trusted Base

Sail/lean-sail is the trusted RISC-V reference semantics. The `LeanRV64D/`
directory is treated as trusted/generated code, except for the platform behavior
change described below.

## Misaligned Memory Accesses

Jolt's inline memory instructions do not implement native split misaligned loads
or stores. They compute an effective address, check the required alignment for
the access width, and stop with an alignment failure when the address is
misaligned.

The imported Sail platform can otherwise permit ordinary misaligned accesses to
continue through the virtual-memory pipeline. To match Jolt's expansion
semantics, the platform constant is set to disable split misaligned accesses:

```lean
def plat_enable_misaligned_access : Bool := false
```

With that setting, Sail's memory path raises the same immediate alignment
exception on the misaligned branch instead of continuing through split access
logic.

## Building

```bash
lake build JoltBytecode
```

Current project policy is that `JoltBytecode/` should not rely on large
`maxHeartbeats` overrides. The trusted generated `LeanRV64D/` tree is not part
of that cleanup policy.
