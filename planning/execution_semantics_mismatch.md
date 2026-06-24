# Execution Semantics Mismatch

This is the row-level audit snapshot for `JoltBytecode/JoltISA`.

Scope notes:

- The `# Natives` entries below cover every current `JoltISA.Instr` constructor in `JoltBytecode/JoltISA/Instruction.lean`.
- The `# Expanded` section records the audit pass over `JoltBytecode/JoltISA/Expansions` against Rust's `crates/jolt-program/src/expand` recipes.
- "Perfectly aligned" means no row-body mismatch was found against the Rust tracer instruction semantics for the audited architectural/proof-visible state.
- The normal Rust fetch-stage PC increment, trace stamping, lookup-table behavior, and trace-only call metadata are not counted as row-body mismatches here.
- Assertion panic in Rust versus `Error.Assertion` in Lean is treated as aligned when the pass/fail predicate is the same.
- LR/SC source expansions are explicitly out of proof scope for now, per audit direction.
- Immediate alignment assumes a translator maps Rust normalized operands into the Lean constructor's immediate convention.

Status markers:

- `DONE:` perfectly aligned.
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

# Natives

## NoOp :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Standalone `NoOp` is a no-op on both sides. Note that Rust's ordinary pure `rd = x0` rewrite materializes `ADDI x0, x0, 0`, not necessarily a `NoOp` row.

## ADDI :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Lean uses wrapping 64-bit addition with a sign-extended 12-bit immediate, matching Rust `ADDI`.

## ANDI :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Lean sign-extends the immediate and bitwise-ands, matching Rust.

## ORI :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Lean sign-extends the immediate and bitwise-ors, matching Rust.

## XORI :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Lean sign-extends the immediate and bitwise-xors, matching Rust.

## SLTI :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Signed comparison and 0/1 writeback align with Rust.

## SLTIU :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Unsigned comparison against the sign-extended immediate aligns with Rust.

## LUI :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None, under the Lean convention that `LUI` receives the already-normalized 64-bit immediate value to write.

## AUIPC :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None, under the Lean convention that the constructor receives the decoded 20-bit U-immediate and shifts it left by 12. A translator must not pass Rust's already-shifted normalized U-immediate directly without adapting it.

## JAL :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None for architectural row semantics. Lean uses Sail `nextPC` as the link and jumps to `PC + imm`, matching Rust's pre-incremented-link convention. Rust's `track_call` side effect for `rd = x1` is trace/profiling metadata and is outside this row-state scope.

## JALR :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None for architectural row semantics. Lean uses Sail `nextPC` as the link, computes `base + imm`, clears bit 0, and jumps, matching Rust. Rust's `track_call` side effect for `rd = x1` is trace/profiling metadata and is outside this row-state scope.

## BEQ :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None under the PC convention in the scope note. The taken predicate and target computation align with Rust.

## BNE :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None under the PC convention in the scope note. The taken predicate and target computation align with Rust.

## BLT :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None under the PC convention in the scope note. Signed comparison and taken target align with Rust.

## BGE :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None under the PC convention in the scope note. Signed comparison and taken target align with Rust.

## BLTU :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None under the PC convention in the scope note. Unsigned comparison and taken target align with Rust.

## BGEU :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None under the PC convention in the scope note. Unsigned comparison and taken target align with Rust.

## FENCE :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Both models treat it as a no-op row.

## ADD :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Wrapping 64-bit addition aligns with Rust.

## SUB :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Wrapping 64-bit subtraction aligns with Rust.

## MUL :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Low 64 bits of wrapping multiplication align with Rust.

## MULHU :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Lean computes the high 64 bits of the unsigned 64 by 64 product, matching Rust.

## ANDN :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. `rs1 & !rs2` aligns with Rust.

## VirtualMULI :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Wrapping multiplication by the immediate bit pattern aligns with Rust.

## VirtualPow2 :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Computes `1 << (src & 0x3f)`, matching Rust.

## VirtualPow2W :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Computes `1 << (src & 0x1f)`, matching Rust.

## VirtualPow2I :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Computes `1 << (imm % 64)`, matching Rust.

## VirtualPow2IW :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Computes `1 << (imm % 32)`, matching Rust.

## VirtualShiftRightBitmask :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. The six-bit masked shift and generated trailing-zero bitmask align with Rust.

## VirtualShiftRightBitmaskI :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. The immediate `% 64` shift and generated trailing-zero bitmask align with Rust.

## VirtualSRLI :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Logical right shift by `ctz(bitmask)` aligns with Rust.

## VirtualSRAI :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Arithmetic right shift by `ctz(bitmask)` aligns with Rust.

## VirtualSRL :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Logical right shift by `ctz(rs2)` aligns with Rust.

## VirtualSRA :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Arithmetic right shift by `ctz(rs2)` aligns with Rust.

## VirtualROTRI :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Rotate-right by `ctz(bitmask)` aligns with Rust.

## VirtualROTRIW :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Rotate-right of the low word by `min(ctz(bitmask), 32)` with zero-extension aligns with Rust.

## VirtualRev8W :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Per-word byte reversal aligns with Rust.

## VirtualXORROT32 :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. XOR followed by rotate-right 32 aligns with Rust.

## VirtualXORROT24 :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. XOR followed by rotate-right 24 aligns with Rust.

## VirtualXORROT16 :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. XOR followed by rotate-right 16 aligns with Rust.

## VirtualXORROT63 :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. XOR followed by rotate-right 63 aligns with Rust.

## VirtualXORROTW16 :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Low-word XOR followed by rotate-right 16 and zero-extension aligns with Rust.

## VirtualXORROTW12 :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Low-word XOR followed by rotate-right 12 and zero-extension aligns with Rust.

## VirtualXORROTW8 :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Low-word XOR followed by rotate-right 8 and zero-extension aligns with Rust.

## VirtualXORROTW7 :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Low-word XOR followed by rotate-right 7 and zero-extension aligns with Rust.

## OR :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Bitwise-or aligns with Rust.

## XOR :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Bitwise-xor aligns with Rust.

## AND :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Bitwise-and aligns with Rust.

## SLT :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Signed less-than and 0/1 writeback align with Rust.

## SLTU :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Unsigned less-than and 0/1 writeback align with Rust.

## VirtualSignExtendWord :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Sign-extension of the low 32 bits aligns with Rust.

## VirtualZeroExtendWord :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Zero-extension of the low 32 bits aligns with Rust.

## VirtualMovsign :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. Writes all ones for a set sign bit and zero otherwise, matching Rust.

## VirtualAssertHalfwordAlignment :

Status: WARNING: issues found

Perfectly aligned: no

Issues found:

- Pass condition and wrapping address arithmetic align with Rust.
- Failure behavior does not exactly align with Rust `cpu_exec`: Rust asserts/panics and has no fault operand, while Lean returns `ExecutionResult.Memory_Exception` with a caller-supplied `ExceptionType`.
- This is intentional for source-instruction equivalence against Sail exceptions, but it is not exact Rust row execution semantics.

## VirtualAssertWordAlignment :

Status: WARNING: issues found

Perfectly aligned: no

Issues found:

- Pass condition and wrapping address arithmetic align with Rust.
- Failure behavior does not exactly align with Rust `cpu_exec`: Rust asserts/panics and has no fault operand, while Lean returns `ExecutionResult.Memory_Exception` with a caller-supplied `ExceptionType`.
- This is intentional for source-instruction equivalence against Sail exceptions, but it is not exact Rust row execution semantics.

## LD :

Status: WARNING: issues found

Perfectly aligned: no

Issues found:

- Rust's `LD` path calls `load_doubleword`; unaligned or failing MMU paths assert/panic rather than returning a structured `ExecutionResult`. Lean is using Sail-style structured memory results.

Resolved:

- The previous normal-load versus AMO-read-side alignment-class split is now explicit in `Instr.LD` via `LoadFaultClass`. Successful `LD` still uses the same `vmem_read_addr ... (Load Data)` path; the flag only selects the structured exception class on the Lean misalignment branch.

## SD :

Status: WARNING: issues found

Perfectly aligned: no

Issues found:

- Successful aligned store semantics align with Rust.
- Failure behavior is not exact Rust `cpu_exec`: Rust `store_doubleword` asserts/unwraps on failing MMU paths, while Lean returns Sail-style `ExecutionResult.Memory_Exception`.
- The alignment fault class itself is consistent with Sail store/AMO behavior (`E_SAMO_Addr_Align`).

## VirtualAdvice :

Status: NEXT: issues found

Perfectly aligned: no

Issues found:

- For current built-in division-style uses, Lean's explicit oracle value matches Rust's patched `VirtualAdvice.advice` field.
- The Lean constructor only permits a virtual-register destination (`VReg`). Rust `VirtualAdvice` is a final row with a general `rd` field and `cpu.write_register`, so the Rust row can write any register index, including architectural registers.
- This is a representational narrowing rather than a mismatch for the current built-in expansion uses.

## VirtualAdviceLoad :

Status: WARNING: issues found

Perfectly aligned: no

Issues found:

- Rust consumes 1, 2, 4, or 8 bytes from the mutable advice tape using the row immediate, then writes the loaded value.
- Lean takes the loaded value as an explicit operand and has no byte-count immediate, tape cursor, or tape-consumption effect.
- This is an oracle abstraction, not exact `cpu_exec` semantics.

## VirtualAdviceLen :

Status: WARNING: issues found

Perfectly aligned: no

Issues found:

- Rust reads the current remaining byte length of the advice tape.
- Lean takes the remaining length as an explicit operand and does not model the tape state.
- This is an oracle abstraction, not exact `cpu_exec` semantics.

## VirtualHostIO :

Status: FIXME: issues found

Perfectly aligned: no

Issues found:

- Rust dispatches on registers `x10` through `x13` and may mutate host/advice/output/cycle-marker state.
- Lean treats `VirtualHostIO` as a no-op.
- This is a real side-effect mismatch if host IO is in the claimed CPU state surface. If host IO remains out of proof scope, that exclusion should stay explicit.

## VirtualAssertEQ :

Status: WARNING: issues found

Perfectly aligned: no

Issues found:

- Rust uses the row immediate as a mode: `imm = 0` is a hard assertion, while nonzero immediate is "spoil" mode that warns but does not panic.
- Lean has no immediate/mode field and always asserts equality.
- Current built-in expansion uses found in the audit pass use `imm = 0`, so this does not appear to break those expansions, but the final row semantics are not complete for arbitrary Rust `VirtualAssertEQ` rows.

## VirtualAssertValidDiv0 :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. The divisor-zero quotient check aligns with Rust: if divisor is zero, quotient must be all ones.

## VirtualChangeDivisor :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. The 64-bit signed overflow case `(INT64_MIN, -1)` maps the divisor to `1`; otherwise the divisor passes through, matching Rust.

## VirtualChangeDivisorW :

Status: NEXT: issues found

Perfectly aligned: no

Issues found:

- Rust casts both operands to `i32`, checks `(INT32_MIN, -1)`, and writes the divisor sign-extended back to 64 bits.
- Lean assumes both operands are already sign-extended 32-bit values stored in 64-bit words. It compares full 64-bit values and otherwise returns the original 64-bit divisor.
- Current `DIVW`/`REMW` expansion paths sign-extend operands before this row, so those uses align. As a standalone final row over arbitrary register states, Lean is narrower than Rust.

## VirtualAssertValidUnsignedRemainder :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. The unsigned remainder bound check aligns with Rust.

## VirtualAssertMulUNoOverflow :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. The unsigned multiplication overflow predicate aligns with Rust.

## VirtualAssertLTE :

Status: DONE: perfectly aligned

Perfectly aligned: yes

Issues found: None. The unsigned less-than-or-equal assertion aligns with Rust.

# Expanded

Checked: yes.

The expansion pass checked the Lean expansion files under `JoltBytecode/JoltISA/Expansions` against Rust's built-in expander under `crates/jolt-program/src/expand`. This was a shape/semantics audit, not a proof pass and not a lookup-table audit.

## ALU / Shifts / Mul / DivRem :

Status: DONE: expansion shape aligned

Perfectly aligned: yes, modulo the row-level caveats already listed under `# Natives`.

Issues found: None. The fixed scratch-register layout, recursive lowering shape, word sign/zero extension, shift bitmask conventions, and division advice-verifier sequences line up with Rust.

## Loads :

Status: NEXT: issues found

Perfectly aligned: no

Issues found:

- Normal byte/halfword/word extraction shape aligns with Rust.
- Source load instructions with `rd = x0` do not exactly match Rust materialization: Rust rewrites the discarded destination to a temporary, while Lean load programs take `rd` literally and let the final write to `x0` be a no-op. The load sequence still runs, so this is row-parity drift rather than a dropped memory effect.

## Stores :

Status: DONE: expansion shape aligned

Perfectly aligned: yes, modulo the row-level `LD`/`SD` structured-failure caveats already listed under `# Natives`.

Issues found: None in expansion shape. `SB`/`SH`/`SW` splicing and alignment assertions match the Rust recipes.

## Advice Loads :

Status: WARNING: issues found

Perfectly aligned: no

Issues found:

- Source `AdviceLB`/`AdviceLH`/`AdviceLW`/`AdviceLD` with `rd = x0`: Rust treats advice loads as side-effecting and rewrites `rd = x0` to a temporary before expansion, so the advice tape is still consumed. Lean's `advicel*Program` currently uses `pureWritebackTraceProgram`, which turns `rd = x0` into `ADDI x0, x0, 0` and drops the advice-load effect.

## Atomics :

Status: NEXT: issues found

Perfectly aligned: no

- Normal AMO doubleword and word read-modify-write expansion shape aligns with Rust for ordinary destinations.
- AMO expansion `LD` rows now use `.amo`, so the Sail AMO alignment-fault class is represented without changing Rust's successful load-row shape.
- Source AMO expansions with `rd = x0`: Rust treats AMOs as side-effecting and rewrites the destination to a temporary before expansion. Lean AMO programs take `rd` literally. The memory update still occurs, but exact Rust final-row parity differs.

## System / CSR :

Status: DONE: expansion shape aligned

Perfectly aligned: yes for the supported CSR whitelist and machine-mode trap model.

Issues found: None in expansion shape. `ECALL`, `EBREAK`, `MRET`, `CSRRW`, and `CSRRS` align with Rust's supported expansion paths.

## LR/SC :

Status: NEXT: out of current proof scope

Perfectly aligned: no, but intentionally not actionable for this audit.

Issues found:

- Rust `LR.W`/`LR.D` now prepend a RAM-region assertion before recording reservations.
- Lean has LR programs but no `SCW`/`SCD` expansion programs under `JoltISA/Expansions`.
- Per audit direction, LR/SC will not be proven for now due to Lean issues, so this should not block the current JoltISA CPU-alignment work.
