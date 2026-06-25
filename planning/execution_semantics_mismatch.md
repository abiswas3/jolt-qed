# Execution Semantics Mismatch

This is the row-level audit snapshot for `JoltBytecode/JoltISA`.

Scope notes:

- The audit covers every current `JoltISA.Instr` constructor in `JoltBytecode/JoltISA/Instruction.lean`.
- The audit covers every current `JoltISA.Expanded` constructor in `JoltBytecode/JoltISA/Instruction.lean`.
- The parts of the code that need to be rust aligned are the semantics/cpu execution behaviour of native/unexpanded/instructions modelled in `Instruction.lean`, and the expansion modelled by the Expansion in Rust. 
- Additionally, we must model Jolts usage of virtual register faithfully, and any sail state it might touch, like PC.
- Assertion panic in Rust versus `Error.Assertion` in Lean is treated as aligned when the pass/fail predicate is the same.
- Rust panic/assertion on invalid memory paths versus Lean `Memory_Exception` is treated as the Sail-facing modeling boundary described under `# Notes`.
- LR/SC source expansions are explicitly out of proof scope for now, per audit direction.
- Immediate alignment assumes a translator maps Rust normalized operands into the Lean constructor's immediate convention.

Status markers:

- `NEXT:` minor issue; can almost be left alone for now.
- `WARNING:` not major, but should be fixed.
- `FIXME:` major issue.

# Notes

## LD fault classes :

Rust/Jolt uses the same `load_doubleword` pathway for ordinary loads and for
the read side of AMO expansions. Sail does not: ordinary load faults and AMO
faults use different exception constructors.

- Normal Sail load alignment faults use `E_Load_Addr_Align`.
- Sail store and AMO alignment faults use `E_SAMO_Addr_Align`.

Lean therefore gives `Instr.LD` a `LoadFaultClass` marker:

- `.normal` is used for native loads, source load expansions, store helper
  loads, and LR-related load rows.
- `.amo` is used when an `LD` row is serving as the read side of an AMO
  expansion.

This marker is Lean proof metadata for Sail comparison, not a Rust-emitted
opcode bit. It only selects the structured exception constructor on the Lean
misalignment branch; the successful path still uses the same
`vmem_read_addr ... (Load Data)` read shape. `SD` does not need the same marker
because both ordinary stores and AMO write-side failures already fall under
Sail's `E_SAMO_Addr_Align` class.

## Rust panic versus Lean memory exceptions :

Rust Jolt tracer rows often treat invalid memory paths as host-side failures:
`load_doubleword` / `store_doubleword` assert alignment or unwrap/panic on MMU
errors. Sail does not model those paths as host panics; it returns structured
architectural exceptions such as `ExecutionResult.Memory_Exception`.

A panic/assert is outside the modeled CPU state: the host Rust program fails.
`Memory_Exception` is inside the modeled CPU state: the instruction step returns
a structured architectural result.

Lean follows the Sail-facing model for `LD`, `SD`, and explicit alignment
assert rows. That means the successful row behavior is still checked against
Rust, but failure behavior is intentionally structured so instruction proofs can
compare against Sail. When native entries below mention Rust assert/panic versus
Lean `Memory_Exception`, this is a modeling-boundary caveat rather than a claim
that the successful Rust row semantics are wrong.

## AMO `rd=x0` source rewrite :

Rust treats AMO source instructions as side-effecting even when `rd = x0`: the
load/store side effect remains, but the destination write is redirected to a
temporary virtual register and the later scratch allocation moves up by one
slot.

Lean now mirrors that rule for AMO expansions with `amoDstFor rd` and
`amoVRegFor rd n`. When `rd = x0`, `amoDstFor` writes the old value to the
same temporary destination shape as Rust, and `amoVRegFor` shifts AMO scratch
registers so the expansion rows line up with the Rust allocator order.

The former AMO `rd=x0` entries are therefore closed and omitted from the
remaining issue list.

## VirtualHostIO provenance :

`VirtualHostIO` is primarily a Jolt SDK/platform guest-code hook. The
`jolt-platform` print and cycle-tracking helpers, and the `jolt-sdk` advice
writer, emit the custom instruction directly with inline assembly during
RISC-V compilation:

```asm
.insn i 0x5B, 2, x0, x0, 0
```

The Jolt program builder consumes existing ELF bytes, decodes this custom
encoding as `VirtualHostIO`, and passes it through as a final Jolt row because
it is not a source-only instruction. I did not find a Jolt stage that edits an
arbitrary native RISC-V ELF to insert `VirtualHostIO` after the fact. If a user
manually authors or patches an ELF to contain that encoding, Jolt's decoder
will recognize it, but the normal pipeline appears to rely on the instruction
already being present in the guest ELF.

## This Advice Business

Jolt's ELF reader is not reading only plain standard RISC-V. It accepts the
supported RV64 instruction subset plus a small Jolt custom instruction surface
encoded in RISC-V custom opcode space.

RV64 means the architectural register width is 64 bits; it does not mean these
instruction words are 64 bits. The custom Jolt SDK instructions discussed here
are ordinary 32-bit RISC-V instruction words using an I-format layout:

```text
31          20 19    15 14  12 11     7 6       0
+-------------+--------+------+---------+---------+
| imm[11:0]   | rs1    |funct3| rd      | opcode  |
+-------------+--------+------+---------+---------+
```

For example, an `AdviceLB` into `x10` is emitted as an I-format custom
instruction with `opcode = 0x5B`, `funct3 = 0b011`, `rd = x10`, `rs1 = x0`,
and `imm = 0`:

```text
.insn i 0x5B, 3, x10, x0, 0

imm[11:0]    rs1    funct3  rd     opcode
000000000000 00000  011     01010  1011011

full 32-bit word:
00000000000000000011010101011011
0x0000355B
```

The ELF stores bytes; Jolt's decoder reads them back as 32-bit instruction
words and dispatches on the opcode/funct fields.

The custom source opcodes currently recognized by the Rust decoder are:

- `0x0B` / `0b0001011`: built-in inline/precompile space, decoded as `Inline`.
- `0x2B` / `0b0101011`: external inline space, decoded as `Inline`.
- `0x5B` / `0b1011011`: Jolt custom/virtual instruction space.

For opcode `0x5B`, `funct3` selects:

- `0b000`: `VirtualRev8W` -- native/pass-through final row.
- `0b001`: `VirtualAssertEQ` -- native/pass-through final row.
- `0b010`: `VirtualHostIO` -- native/pass-through final row.
- `0b011`: `AdviceLB` -- expanded/source-only.
- `0b100`: `AdviceLH` -- expanded/source-only.
- `0b101`: `AdviceLW` -- expanded/source-only.
- `0b110`: `AdviceLD` -- expanded/source-only.
- `0b111`: `VirtualAdviceLen` -- native/pass-through final row.

These are not standard RISC-V instructions, but they can be present in the
guest ELF because Jolt SDK/platform code emits them with inline assembly using
RISC-V custom encodings. Jolt's decoder recognizes those encodings as source
instructions, then the expansion layer lowers source-only forms. In particular,
the ELF contains `AdviceLB` / `AdviceLH` / `AdviceLW` / `AdviceLD`; the final
row `VirtualAdviceLoad` is introduced by expansion with byte width `1`, `2`,
`4`, or `8`. `VirtualAdviceLoad` is native as a final Jolt bytecode row, but it
is not directly decoded from the guest ELF custom opcode table above.

There is a second opcode/tag layer after ELF decoding. Some virtual
instructions are not SDK-emitted machine words at all; they are introduced by
the bytecode expander as final Jolt rows. At that point they are Rust data
structures, not raw 32-bit RISC-V instruction words waiting to be decoded
again.

```text
guest ELF bytes
  -> 32-bit RISC-V/custom machine words
  -> SourceInstruction { kind, row }
  -> expansion
  -> JoltInstructionRow {
       instruction_kind : JoltInstructionKind,
       address          : usize,
       operands         : NormalizedOperands,
       virtual_sequence_remaining : Option<u16>,
       is_first_in_sequence       : bool,
       is_compressed              : bool
     }
  -> typed tracer instruction, e.g. JoltInstruction::VirtualAdvice(...)
```

The internal Jolt row tags include, for example:

- `0x0061`: `jolt.virtual.advice`
- `0x0062`: `jolt.virtual.advice_len`
- `0x0063`: `jolt.virtual.advice_load`
- `0x0064`: `jolt.virtual.assert_eq`
- `0x0068`: `jolt.virtual.host_io`
- `0x0069`: `jolt.virtual.assert_valid_div0`
- `0x006c`: `jolt.virtual.change_divisor`

`VirtualAdvice` is the clearest example of this distinction. It is produced by
expansions such as the DIV/REM advice-verified families and then patched by the
tracer with runtime witness values. Rust explicitly rejects building it from a
guest machine word: `VirtualAdvice::new` panics with
`virtual instruction 'VirtualAdvice' cannot be built from a machine word`.

# Natives

Native audit convention:

- `Final row` means executing the concrete `JoltISA.Instr` constructor against the Jolt CPU model.
- `Source parity` means the same opcode can arrive from guest ELF as a Rust `SourceInstruction`.
- Rust handles `rd = x0` before pass-through or source-only expansion. Pure writeback rows become `ADDI x0, x0, 0`; side-effecting rows rewrite `rd` to a temporary virtual register.
- Pure `rd = x0` source rewrites are not marked as issues below when the visible CPU state is unchanged. Side-effecting `rd = x0` rewrites are marked when Lean does not model the temporary destination row shape.

## VirtualAdviceLoad

Status: WARNING: advice tape state not modeled

Surface: tracer-generated final row.

Issues found:

- Rust consumes `imm` bytes from the mutable advice tape, then writes the loaded value.
- Lean takes the loaded value as an explicit operand and has no byte-count immediate, tape cursor, or tape-consumption effect.

## VirtualAdviceLen

Status: WARNING: advice tape state not modeled

Surface: custom-elf native/pass-through.

Issues found:

- Rust reads the current remaining byte length of the advice tape.
- Lean takes the remaining length as an explicit operand and does not model the tape state.

## VirtualHostIO

Status: FIXME: host IO side effects missing

Surface: custom-elf native/pass-through.

Issues found:

- Rust dispatches on registers `x10` through `x13` and may mutate host/advice/output/cycle-marker state.
- Lean treats `VirtualHostIO` as a no-op.

# Expanded

Expanded audit convention:

- These entries compare Lean expansion programs in `JoltBytecode/JoltISA/Expansions` with Rust recipes under `crates/jolt-program/src/expand`.
- For source-only pure writeback instructions, `rd=x0` should become `ADDI x0, x0, 0`; Lean programs that use `pureWritebackTraceProgram` match that rule.
- For source-only side-effecting instructions, Rust rewrites `rd=x0` to a temporary virtual register before expanding. Lean programs that take `rd` literally are marked below.
- The LR/SC family remains out of proof scope by audit direction.

## AdviceLB

Status: WARNING: advice tape state and `rd=x0` rewrite missing

Surface: custom-elf source-only.

Issues found: Lean takes explicit advice instead of modeling advice-tape consumption, and currently no-ops `rd=x0` through `pureWritebackTraceProgram` while Rust rewrites `rd=x0` to a temporary to preserve the tape read.

## AdviceLH

Status: WARNING: advice tape state and `rd=x0` rewrite missing

Surface: custom-elf source-only.

Issues found: Lean takes explicit advice instead of modeling advice-tape consumption, and currently no-ops `rd=x0` through `pureWritebackTraceProgram` while Rust rewrites `rd=x0` to a temporary to preserve the tape read.

## AdviceLW

Status: WARNING: advice tape state and `rd=x0` rewrite missing

Surface: custom-elf source-only.

Issues found: Lean takes explicit advice instead of modeling advice-tape consumption, and currently no-ops `rd=x0` through `pureWritebackTraceProgram` while Rust rewrites `rd=x0` to a temporary to preserve the tape read.

## AdviceLD

Status: WARNING: advice tape state and `rd=x0` rewrite missing

Surface: custom-elf source-only.

Issues found: Lean takes explicit advice instead of modeling advice-tape consumption, and currently no-ops `rd=x0` through `pureWritebackTraceProgram` while Rust rewrites `rd=x0` to a temporary to preserve the tape read.

## LRD

Status: WARNING: LR family out of current proof scope

Surface: riscv-atomic source-only.

Issues found:

- Rust prepends the RAM-region assertion before reservation handling; Lean's `lrdProgram` does not include that prelude.
- Rust rewrites source `rd=x0` to a temporary before expansion; Lean's LR program takes `rd` literally.
- Per audit direction, LR/SC is not being proven yet.

## LRW

Status: WARNING: LR family out of current proof scope

Surface: riscv-atomic source-only.

Issues found:

- Rust prepends the RAM-region assertion before reservation handling; Lean's `lrwProgram` does not include that prelude.
- Rust rewrites source `rd=x0` to a temporary before expansion; Lean's LR program takes `rd` literally.
- Per audit direction, LR/SC is not being proven yet.

## SCD

Status: WARNING: SC family out of current proof scope

Surface: riscv-atomic source-only.

Issues found:

- Rust has an expansion with RAM-region assertion, reservation checks, store/update path, and `VirtualAdvice` success patching.
- There is no current `SCD` program under `JoltBytecode/JoltISA/Expansions`.
- Per audit direction, LR/SC is not being proven yet.

## SCW

Status: WARNING: SC family out of current proof scope

Surface: riscv-atomic source-only.

Issues found:

- Rust has an expansion with RAM-region assertion, reservation checks, store/update path, and `VirtualAdvice` success patching.
- There is no current `SCW` program under `JoltBytecode/JoltISA/Expansions`.
- Per audit direction, LR/SC is not being proven yet.
