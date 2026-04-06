
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

### 3. EmbeddedSailJoltState/ (mvcgen proofs, 6 instructions)

**State model**: `SailJoltState` embeds `SailState` directly as a field:
`structure SailJoltState where sail : SailState; vregs : ...`.
`project js = js.sail`. Much cleaner than field duplication.

**What it proves**: Same theorem as (2), but with `WellFormed js` precondition
(all register reads succeed — true for any real RISC-V state). Load instructions
additionally require `JoltConfig js.sail` (M-mode, flat memory).

**Proof style**: `@[spec]` Hoare triples + `mvcgen` tactic. The monadic plumbing
is automated. Each instruction file provides only:
- The Jolt decomposition definition (`jolt_addw`, `jolt_srai`, etc.)
- A factoring lemma (how `execute_RTYPE`/`execute_ITYPE` decomposes)
- A math bridge lemma (e.g., `extractLsb_add`, `srai_bitmask_eq_arith_shift`)

**6 instructions**: Addw, Subw, Addiw, Srai, Sraiw, Lw
**5 fully proved (zero sorries), 1 main theorem proved with sorry'd helper lemmas (Lw)**

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
    Defs.lean             -- SailJoltState, liftSail, project, memory primitives, JoltConfig
    RegisterOps.lean      -- register lemmas, stateAfterWrite
    RtypeW.lean           -- mvcgen specs + generic W-type framework
    InstructionEquivalence/
      Addw.lean           -- ADDW: 64-bit ADD then sign-extend word
      Subw.lean           -- SUBW: 64-bit SUB then sign-extend word
      Addiw.lean          -- ADDIW: 64-bit ADDI then sign-extend word
      Srai.lean           -- SRAI: arithmetic right shift via bitmask
      Sraiw.lean          -- SRAIW: 3-step decomposition with virtual registers
      Lw.lean             -- LW: dword-load-then-shift decomposition
```

The two SailJolt systems are fully independent — zero cross-imports.

## Detailed theorem catalog: EmbeddedSailJoltState/

### Defs.lean — Core definitions and state management

- **`SailState`**: Abbreviation for Sail's `SequentialState RegisterType trivialChoiceSource`.
  The RISC-V machine state: registers (hash map), memory (hash map), choice state, etc.

- **`SailJoltState`**: Extends SailState with virtual registers.
  `structure SailJoltState where sail : SailState; vregs : BitVec 7 → BitVec 64`.
  The embedded architecture — SailState is a single field, not duplicated.

- **`JoltMonad`**: `EStateM (Error exception) SailJoltState α`.
  Stateful computation over JoltState that can throw Sail errors.

- **`project`**: `SailJoltState → SailState`. Extracts the embedded Sail state (`js.sail`).
  Strips virtual registers so we can compare with pure Sail computations.

- **`inject`**: `SailJoltState → SailState → SailJoltState`. Updates the Sail state,
  preserving virtual registers. Inverse direction of project.

- **`projectResult`**: Applies `project` to the state inside an `EStateM.Result`.
  Used to compare: `projectResult (jolt_op.run js) = sail_op.run js.sail`.

- **`liftSail`**: `SailM α → JoltMonad α`. Runs a Sail computation inside JoltMonad.
  Strips vregs (via project), runs Sail code, restores vregs (via inject).

- **`project_inject`**: Projecting after injecting gives back the Sail state. `project (inject js ss) = ss`.

- **`inject_inject`**: Double injection: only the last Sail state matters. `inject (inject js ss1) ss2 = inject js ss2`.

- **`inject_project`**: Injecting the projection is identity. `inject js (project js) = js`.

- **`liftSail_project`**: Running liftSail and projecting = running Sail directly.
  `projectResult ((liftSail m).run js) = m.run js.sail`. The fundamental correctness property.

- **`liftSail_bind`**: liftSail preserves monadic bind.
  `liftSail (m >>= f) = do let a ← liftSail m; liftSail (f a)`.

- **`liftSail_pure`**: liftSail preserves pure. `liftSail (pure a) = pure a`.

- **`readVReg`**: Read a virtual register. `readVReg vr = do let js ← get; pure (js.vregs vr)`.

- **`writeVReg`**: Write a virtual register. Updates `js.vregs` at index `vr`.

- **`sailReadByte`**: Read one byte from Sail's physical memory at a given address.
  Looks up `s.mem.get? addr`. This is what Sail's `readByte` does at the bottom
  of the memory hierarchy. Fails with `OutOfMemoryRange` if address not in map.

- **`sailReadWord`**: Read 4 bytes (little-endian) from Sail's memory as a 32-bit word.
  Chains 4 `sailReadByte` calls.

- **`sailReadDword`**: Read 8 bytes (little-endian) from Sail's memory as a 64-bit dword.
  Chains 2 `sailReadWord` calls (low word + high word).

- **`JoltConfig`**: Predicate on SailState capturing Jolt's execution environment.
  - `machine_mode`: `cur_privilege = Machine` (bare-metal, no OS).
  - `mstatus_ok`: `MPRV = 0` in mstatus (no privilege virtualization).
  - `mem_populated`: all memory addresses are in `state.mem`.
  Together these make Sail's vmem_read pipeline reduce to raw byte reads.

- **`translateAddr_machine_bare`** (SORRY): Under JoltConfig, Sail's virtual-to-physical
  address translation is the identity. Machine mode → translationMode = Bare → paddr = vaddr.
  Requires unfolding through effectivePrivilege, translationMode, and register reads.

- **`execute_LOAD_LW_factored`** (SORRY): Under JoltConfig, Sail's `execute_LOAD` for LW
  (width=4, signed) equals: read rs1, compute address, `sailReadWord(addr)`, sign-extend,
  write to rd. Collapses the entire vmem_read pipeline (6 layers of checks) to raw byte reads.

- **`jolt_virtual_sign_extend_word`**: Read register rd, extract lower 32 bits,
  sign-extend to 64 bits, write back to rd. Shared across all W-type instructions.

### RegisterOps.lean — Register operation lemmas

- **`readReg_pure`**: Sail's readReg does not change state. If `readReg reg s = .ok v s'` then `s' = s`.

- **`rX_bits_pure`**: Register reads via `rX_bits` do not change state.
  For any register index, if the read succeeds, the output state equals the input state.

- **`wX_shape`**: Register writes via `wX_bits` always succeed.
  For any register and value, `∃ s', wX_bits r v s = .ok () s'`.

- **`eStateM_deterministic`**: EStateM computations are deterministic.
  If `m s = .ok a1 s1` and `m s = .ok a2 s2`, then `a1 = a2` and `s1 = s2`.

- **`wX_shape_modify`**: Register writes only change the `regs` field.
  All other fields (mem, tags, etc.) are preserved.

- **`wX_eq_modify_regs`**: After a write, the state differs from the original only in `regs`.

- **`wX_update_regs`**: Pure function mirroring what `wX_bits` does to the register map.
  A 32-way match on register index, inserting the value at the right key.

- **`wX_regs_spec`**: `wX_bits` produces a state whose `regs = wX_update_regs r v s.regs`.
  Links the Sail monadic write to the pure function.

- **`extDHashMap_insert_insert`**: Inserting the same key twice: only the last value matters.

- **`wX_update_regs_idem`**: `wX_update_regs` is idempotent.
  `wX_update_regs r v2 (wX_update_regs r v1 regs) = wX_update_regs r v2 regs`.

- **`wX_wX_collapse`**: Two writes to the same register = just the second write.
  If `wX_bits r v1 s = .ok () s1` and `wX_bits r v2 s1 = .ok () s2`,
  then `wX_bits r v2 s = .ok () s2`.

- **`readReg_insert_self`**: Reading from a state where the same key was inserted returns
  the inserted value.

- **`rX_after_wX`**: Reading register r from a state where wX_update_regs r v was applied
  returns v. Proved by exhaustive 31-way case split (excluding register 0).

- **`wX_rX_roundtrip`**: Write then read gives back the value.
  If `wX_bits r v s = .ok () s'` and `r ≠ 0`, then `rX_bits r s' = .ok v s'`.

- **`extractLsb_add`**: Truncating to 32 bits distributes over addition.
  `extractLsb(a + b, 31, 0) = extractLsb(a, 31, 0) + extractLsb(b, 31, 0)`.
  The mathematical core of ADDW.

- **`stateAfterWrite`**: Pure model of a register write's effect.
  `stateAfterWrite s rd val = { s with regs := wX_update_regs rd val s.regs }`.

- **`stateAfterWrite_stateAfterWrite`**: Double write collapses.
  `stateAfterWrite (stateAfterWrite s rd v1) rd v2 = stateAfterWrite s rd v2`.

- **`rX_after_stateAfterWrite`**: Reading rd from stateAfterWrite returns the written value.

- **`wX_bits_eq_stateAfterWrite`**: Concrete write result equals the pure model.
  If `wX_bits rd v s = .ok () s'`, then `s' = stateAfterWrite s rd v`.

### RtypeW.lean — Generic W-type instruction framework

- **`WellFormed`**: All register reads succeed. `∀ r, ∃ v, rX_bits r js.sail = .ok v js.sail`.
  True for any real RISC-V state (registers are always initialized).

- **`liftSail_rX_spec`** `@[spec]`: Reading register r via liftSail succeeds (given WellFormed),
  returns the register value, and does not change the state.

- **`liftSail_wX_spec`** `@[spec]`: Writing value v to register r via liftSail always succeeds
  and updates the sail state to stateAfterWrite. Virtual registers are preserved.

- **`liftSail_RTYPE_spec`** `@[spec]`: Generic spec for liftSail(execute_RTYPE).
  Parameterized by a factoring hypothesis that decomposes execute_RTYPE into
  read rs1, read rs2, write f(v1,v2) to rd. Used for ADDW, SUBW, and any R-type op.

- **`vsew_spec`** `@[spec]`: After a write to rd, jolt_virtual_sign_extend_word reads rd back,
  sign-extends the lower 32 bits, and writes the result. Total correctness given
  `hrd_ok` (rd is readable), which mvcgen discharges from the preceding write.

- **`jolt_rtype_w`**: Generic Jolt W-type instruction: `liftSail(execute_RTYPE op)` then
  `jolt_virtual_sign_extend_word rd` then `pure RETIRE_SUCCESS`.

- **`jolt_rtype_w_concrete`**: mvcgen composes liftSail_RTYPE_spec + vsew_spec to characterize
  the full computation. Produces existential witnesses for read values and final state.

- **`jolt_rtype_w_eq_sail`**: Generic main theorem. Parameterized by op, opw, f, factoring proof,
  and math lemma. Shows `projectResult (jolt_rtype_w.run js) = execute_RTYPEW.run js.sail`.

### InstructionEquivalence/Addw.lean — ADDW (zero sorries)

- **`execute_RTYPE_ADD_factored`**: execute_RTYPE for ADD reads rs1, rs2, writes v1 + v2 to rd.
  Proved by `simp [execute_RTYPE, bind_pure_comp, pure_bind]`.

- **`jolt_addw`**: Jolt's ADDW decomposition: 64-bit ADD then sign-extend lower 32 bits.
  `do let _ ← liftSail (execute_RTYPE rs2 rs1 rd rop.ADD); jolt_virtual_sign_extend_word rd; pure RETIRE_SUCCESS`.

- **`jolt_addw_eq_sail`**: Running Jolt's ADDW and projecting equals running Sail's ADDW.
  One-line instantiation of jolt_rtype_w_eq_sail with extractLsb_add as the math lemma.

### InstructionEquivalence/Subw.lean — SUBW (zero sorries)

- **`execute_RTYPE_SUB_factored`**: execute_RTYPE for SUB reads rs1, rs2, writes v1 - v2 to rd.

- **`extractLsb_sub`**: Truncation distributes over subtraction.
  `extractLsb(a - b) = extractLsb(a) - extractLsb(b)`. Proved by omega.

- **`jolt_subw`**: Jolt's SUBW: 64-bit SUB then sign-extend lower 32 bits.

- **`jolt_subw_eq_sail`**: Jolt SUBW = Sail SUBW. Instantiation of the generic framework.

### InstructionEquivalence/Addiw.lean — ADDIW (zero sorries)

- **`execute_ITYPE_ADDI_factored`**: execute_ITYPE for ADDI reads rs1, adds sign-extended
  immediate, writes to rd.

- **`liftSail_ADDI_spec`** `@[spec]`: After liftSail(execute_ITYPE ADDI), the result is
  RETIRE_SUCCESS and rd holds v1 + sign_extend(imm). Uses WellFormed for register read.

- **`jolt_addiw`**: Jolt's ADDIW: 64-bit ADDI then sign-extend lower 32 bits.

- **`jolt_addiw_concrete`**: mvcgen composes ADDI spec + vsew spec.

- **`jolt_addiw_eq_sail`**: Jolt ADDIW = Sail ADDIW. The math is trivial —
  both sides compute sign_extend(extractLsb(v1 + sign_extend(imm))).

### InstructionEquivalence/Srai.lean — SRAI (zero sorries)

- **`srai_bitmask_eq_arith_shift`**: Jolt's sshiftRight via ctz(bitmask) equals Sail's
  shift_bits_right_arith. The bridge connecting the bitmask-based decomposition to
  the standard arithmetic right shift. Uses ctz_srai_bitmask from BytecodeExpansions.

- **`execute_SHIFTIOP_SRAI_eq_factored`**: Sail's SRAI reads rs1, arithmetically right-shifts
  by the shift amount, writes to rd.

- **`jolt_srai`**: Jolt's SRAI: read rs1, arithmetic right shift by ctz(bitmask), write to rd.
  No VSEW step — direct read-compute-write using primitive specs.

- **`jolt_srai_concrete`**: mvcgen composes liftSail_rX + liftSail_wX primitive specs.

- **`jolt_srai_eq_sail`**: Jolt SRAI = Sail SRAI. Uses srai_bitmask_eq_arith_shift as bridge.

### InstructionEquivalence/Sraiw.lean — SRAIW (zero sorries)

- **`writeVReg_spec`** `@[spec]`: Writing to a virtual register always succeeds and only
  changes vregs, not the sail state.

- **`readVReg_spec`** `@[spec]`: Reading from a virtual register always succeeds, returns
  the stored value, and does not change state.

- **`three_step_eq_sraiwJolt`**: The 3-step Jolt value (sign-extend, shift, truncate,
  sign-extend) equals sraiwJolt (the pure-function decomposition from BytecodeExpansions).

- **`sail_sraiw_eq_riscv`**: Sail's SRAIW value equals Riscv.sraiw (the reference semantics).

- **`sraiw_three_step_value`**: Chains the above: LHS = sraiwJolt = Riscv.sraiw = RHS.
  The mathematical bridge connecting Jolt's 3-step bitmask computation to Sail's
  direct arithmetic right shift.

- **`execute_SHIFTIWOP_SRAIW_eq_factored`**: Sail's SRAIW reads rs1, extracts lower 32 bits,
  arithmetically right-shifts, sign-extends to 64, writes to rd.

- **`jolt_sraiw`**: Jolt's SRAIW: 3 steps with virtual registers.
  Step 1: Read rs1, sign-extend lower 32 bits, write to virtual register 1.
  Step 2: Read virtual register 1, logical right shift by ctz(bitmask), write to rd.
  Step 3: Read rd, sign-extend lower 32 bits, write to rd (VSEW).

- **`jolt_sraiw_concrete`**: mvcgen composes all 5 primitive specs (liftSail_rX, writeVReg,
  readVReg, liftSail_wX, vsew).

- **`jolt_sraiw_eq_sail`**: Jolt SRAIW = Sail SRAIW.

### InstructionEquivalence/Lw.lean — LW (main theorem proved, 3 sorry'd helpers)

- **`sailReadDword_ok`** (SORRY): sailReadDword succeeds when all memory addresses are
  populated (mem_populated), and does not change the Sail state.

- **`sailReadWord_ok`** (SORRY): sailReadWord succeeds when all memory addresses are
  populated, and does not change the Sail state.

- **`sailReadWord_eq_dword_extract`** (SORRY): The dword-extract identity. Loading a 64-bit
  dword from the dword-aligned address and shifting right, truncated to 32 bits, equals
  loading the 32-bit word directly. Pure byte arithmetic — the Sail-level version of
  read_word_eq_dword_extract from BytecodeExpansions/Lw.lean.

- **`jolt_lw`**: Jolt's LW decomposition with virtual registers:
  Step 1 (ADDI): Read rs1, compute effective address base + sign_extend(imm).
  Step 2 (ANDI): Dword-align the address (addr &&& -8).
  Step 3 (LD): Load 64-bit dword from memory via sailReadDword.
  Step 4 (SLLI): Compute byte shift amount (addr <<< 3).
  Step 5 (SRL): Shift dword right to extract the 32-bit word.
  Step 6 (VSEW): Sign-extend lower 32 bits, write to rd.

- **`jolt_lw_eq_sail`**: Jolt LW = Sail LW. **Main theorem has NO sorry.**
  Uses execute_LOAD_LW_factored to rewrite Sail side, unfolds Jolt side,
  reduces vreg plumbing, uses sailReadWord_eq_dword_extract to connect
  dword-shift to word read, then both sides do the same wX_bits write.

## What remains

### Sorry'd lemmas to prove (5 total)

**Memory read purity (2 lemmas, easy)**:
- `sailReadDword_ok`: Prove sailReadDword succeeds under mem_populated.
  Just unfold sailReadDword → sailReadWord → sailReadByte → mem.get?,
  use mem_populated to show each get? returns some.
- `sailReadWord_ok`: Same, 4 bytes instead of 8.

**Dword-extract math (1 lemma, medium)**:
- `sailReadWord_eq_dword_extract`: Port read_word_eq_dword_extract from
  BytecodeExpansions/Lw.lean to Sail's memory model. Pure byte arithmetic.

**vmem_read pipeline bridge (2 lemmas, hard)**:
- `translateAddr_machine_bare`: Machine mode → Bare (identity) translation.
  Requires unfolding through effectivePrivilege, translationMode, and
  Sail register reads. Blocked by Sail's monad transformer stack.
- `execute_LOAD_LW_factored`: Full vmem_read pipeline collapse.
  Layers 1-3 proved mechanically. Layers 4-6 need translateAddr_machine_bare
  plus PMP/PMA/MMIO checks.

### Porting the remaining 59 instructions

The 65 pure-function proofs in `BytecodeExpansions/` need to be lifted to
monadic Sail equivalences. Currently 6 have been lifted (5 complete + 1 with sorry'd helpers).

The lifting pattern depends on the instruction type:
- **R-type W** (Sllw, Srlw, Sraw): generic framework in `RtypeW.lean`.
  Each new instruction needs only a factoring lemma and a math lemma.
- **I-type W** (Slliw, Srliw): similar to Addiw.
- **Shift instructions** (Slli, Srli, Sra, Sll, Srl): read-compute-write with
  bitmask bridge. Uses primitive specs like Srai.
- **Load** (Lb, Lbu, Lh, Lhu, Lwu, Ld): same pattern as Lw with different widths.
  Once execute_LOAD_LW_factored is proved, generalizing to other widths is straightforward.
- **Store** (Sb, Sh, Sw): memory writes — need sailWriteByte and execute_STORE bridge.
- **Mul/Div/Rem**: similar to R-type but different Sail functions.
- **Atomic** (Amo*, Lr*, Sc*): memory + atomics — more complex Sail semantics.
- **CSR** (Csrrs, Csrrw): CSR read/write operations.
- **System** (Ecall, Mret): trap/return semantics.
