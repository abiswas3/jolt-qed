# Trustworthiness Hardening Plan

This document scaffolds work that makes the `JoltBytecode` formal-verification
effort *more trustworthy*, as distinct from work that *extends coverage*.
Coverage and scope live in `planning/roadmap.md` and
`planning/LEAN_BYTECODE_MODEL_LIMITATIONS.md`; this plan does not restate them.

It is written for handoff to future agents and humans. Each workstream is
self-contained: goal, rationale, concrete tasks, acceptance criteria, rough
effort, dependencies, and code pointers.

## Framing: which bugs this targets

The Lean kernel already guarantees that every proof in this repository is valid.
So no effort here goes toward "checking the proofs." A *valid* proof can still
fail to deliver a meaningful guarantee in exactly four ways, and every item
below targets one of them:

1. **Drift.** The Lean specification (`execInstr` per-row semantics, and the
   `xProgram` expansions) is hand-transcribed from Rust and only *asserted*
   faithful. If the transcription is wrong, we prove the wrong thing correctly.
   This is the dominant risk.
2. **Vacuity.** If an assumption bundle (`JoltConfig`, `EcallSystemAssumptions`,
   the memory predicates) is internally contradictory, every theorem about it is
   vacuously true. Nothing currently rules this out.
3. **Weak statement.** A theorem can be true but under-constrain the result: a
   loose postcondition, a projection that discards exactly the bits that differ,
   or a comparison against the wrong Sail function.
4. **Bad base.** The trusted reference (`LeanRV64D/`) is Sail-generated but has
   at least one deliberate edit, and parts of the proof trust `native_decide`
   (compiler + decision-procedure evaluation), which is a larger trusted base
   than the kernel.

## Trusted Computing Base (TCB) ledger

Everything the final guarantee rests on, today. Keeping this list short,
explicit, and CI-enforced is itself a workstream (W7).

| # | Trusted element | Kind | Notes |
| --- | --- | --- | --- |
| T1 | Lean kernel + standard axioms (`propext`, `Classical.choice`, `Quot.sound`) | unavoidable | acceptable; just enumerate |
| T2 | Native-evaluation axioms (`*._native.native_decide.ax_*` / `*._native.bv_decide.ax_*`; the `Lean.ofReduceBool` trust class) | reducible | 104 `native_decide` sites + 163 `bv_decide` sites (SAT-path uses native eval too — verified June 2026). Removable via kernel `decide` (W7); no fundamental blocker, only compile time |
| T3 | `LeanRV64D/` Sail-generated RISC-V semantics | reference spec | trusted by design, but must be provably the genuine upstream output (W5) |
| T4 | `plat_enable_misaligned_access := false` edit to T3 | base edit | load-bearing for the misaligned branch of SH/SW/AMO; a faithfulness modeling choice to justify and isolate, not remove (W5, W6) |
| T5 | Faithfulness of `execInstr` to Rust per-row `cpu_exec` semantics | unproven | drift risk (W1) |
| T6 | Faithfulness of `xProgram` definitions to Rust `inline_sequence` emission | unproven | drift risk; already has at least one row-level mismatch to triage in AMO.D alignment handling (W1) |
| T7 | Toolchain mismatch: `v4.29.0-rc4` vs lean-sail's target nightly | environment | documented in `README.md`; keep pinned and reproducible (W5) |

## Recorded decisions (June 2026)

These are settled for handoff; update this section when they change.

1. **Hand-written `xProgram` vs generated output (W1c).** No upfront policy to
   replace hand-written `JoltISA/Expansions/*.lean` definitions outright or to
   only check equality against them. Clean up per opcode or family as W1c rolls
   out: either path is fine case by case.

2. **Extractor delivery (W1c).** **Pinned artifact in `jolt-qed` for now.** The
   Rust side (extractor or export tool) produces a versioned expansion artifact;
   `jolt-qed` checks in or imports that pinned output and CI diffs it against
   the hand-written `xProgram`s (or adopts generated definitions where we choose
   to). Rust repo CI does not gate on `jolt-qed` equivalence yet.

3. **June 2026 audit correction.** W1 is no longer a later cleanup item. The
   Rust and Lean trees already disagree at row granularity for doubleword AMOs:
   Lean AMO.D programs start with `VirtualAssertDwordAlignment`, while Rust's
   `expand_amo_d` emits `LD` / op / `SD` / `ADDI` and relies on the MMU's
   doubleword alignment assertion. This may be semantically equivalent on the
   failing path, but it is not row-for-row conformance.

4. **Memory inhabitance — investigation concluded (June 2026 deep audit).**
   `JoltConfig.mem_populated` (`∀ addr : Nat, s.mem.get? addr ≠ none` over
   Sail's finite `Std.ExtHashMap Nat (BitVec 8)`) is unsatisfiable; no witness
   exists. W2's only path is the finite footprint contract for the bytes each
   theorem actually touches (≤ 8 consecutive bytes per consumer; see unknown 1
   resolution for the migration surface).

## Workstreams

Status legend: **not-started** / **in-progress** / **done** / **blocked**.
Effort is in agent-runtime terms. The binding constraint everywhere is the Lean
rebuild/recheck cycle, not authoring; size estimates assume that bottleneck.

---

### W1 — Rust to Lean conformance (DRIFT)

**Status: not-started, with known drift finding. Priority: highest value.
Effort: L.**

Goal: detect and prevent divergence between the Lean specification and the Rust
implementation it claims to model. This closes the gap behind T5 and T6, which
together carry most of the residual risk.

Rationale: every proof below T5/T6 is conditional on a transcription no machine
checks. Because `JoltISA.Program` is a concrete inductive (a list of `Instr`),
the expansion half (T6) can be checked structurally without a Rust verifier.

#### Existing Rust-side state (June 2026 audit)

The Rust repo (`/Users/quang.dao/Documents/Snarks/jolt`) already has, after PRs
around #1490/#1518/#1522/#1533:

- A single source of truth for expansion recipes in
  `crates/jolt-program/src/expand/` using an `ExpansionBuilder` / `ExpansionOp`
  grammar.
- Tracing uses the central expansion path for expanded instructions, but the
  old shorthand "thin `inline_sequence` callers" is too simple: some opcodes use
  default single-row tracing, many expanded opcodes wrap `inline_sequence`, and
  native `exec()` methods remain separate from trace expansion. W1b must account
  for both `exec()` vs trace drift and Rust-vs-Lean expansion drift.
- Internal golden regression tests (SHA256 over serialized
  `JoltInstructionRow`s): `expand/fixtures/main_expand_parity_hashes.json`
  (360 source-only cases) and
  `jolt-inlines/fixtures/fixtures/registered_inline_expand_parity_hashes.jsonl`
  (92 registered-inline cases). Both run in CI (`test-crates`, `test-inlines`).
  `jolt-eval` also replays the main 360-case corpus.
- `zklean-extractor`: a working Rust to Lean extractor, but it targets the
  ZkLean proof frontend (R1CS constraints, lookup tables, sumchecks), not the
  bytecode-expansion recipes, and its CI step that would `lake build` the
  extracted Lean is commented out.

What this means: drift is well-controlled *inside Rust* against a past Rust
baseline, but **nothing connects Rust to `jolt-qed`**, golden tests are hashes
rather than structural data, and the existing extractor is a different Lean
universe. So T6 (and T5) are still unguarded with respect to the Sail-equivalence
Lean repo. The AMO.D alignment-row mismatch is the concrete warning shot: the
current plan should treat W1 as near-term trust repair, not late process
hardening.

Rust is fully under our control and freely modifiable, which makes the
single-source approach (W1c) the recommended target rather than an aspiration.

#### W1c — Single source of truth for expansions (RECOMMENDED PRIMARY)

- Add a dedicated bytecode-expansion emitter. It may share infrastructure with
  `zklean-extractor`, but it is effectively a new artifact: the current extractor
  emits ZkLean proof-frontend data, not `JoltISA.Program` rows.
- Emit each opcode's `jolt-qed` `JoltISA.Program` (or a structural manifest)
  from the `jolt-program::expand` recipes.
- **Delivery (recorded decision):** pin the emitted artifact in `jolt-qed`; CI
  here diffs against hand-written `xProgram`s or adopts generated definitions
  per family as we clean up. Rust CI does not gate on this yet.
- **Replace vs check-equal (recorded decision):** no global choice; evolve per
  opcode or family (see Recorded decisions above).

Acceptance criteria: for at least one family, a pinned artifact from
`jolt-program::expand` is checked in `jolt-qed` and CI enforces conformance to
the hand-written or adopted `xProgram` (including `pureWritebackTraceProgram`
`rd = x0` where applicable). The first family should include AMO.D or another
family that exercises early-return and alignment behavior, not only pure ALU
writeback. Extended to all covered opcodes thereafter. This collapses T6 from
trusted transcription to generated-and-checked.

#### W1a — Bytecode structural conformance harness (interim safety net)

- Until W1c covers everything, emit Rust's expansion rows per opcode across an
  operand sweep as a structural manifest (not just a hash), and diff row-for-row
  against the Lean `xProgram`.
- Reuse / widen the existing golden corpus so the same operand cases are checked
  on both sides. The existing hash fixtures are intentionally narrow
  regression fixtures, not a boundary sweep.
- Metadata decision (resolved by the June 2026 deep audit, unknown 4): all
  three fields (`virtual_sequence_remaining`, `is_first_in_sequence`,
  `is_compressed`) are consumed by the constraint system / PC mapping, so the
  manifest diff must check them — sequence position against Lean `Program`
  structure, `is_compressed` carried as out-of-Lean-model but diffed.

Acceptance criteria: a CI job asserting `RustEmitted(opcode, operands) ==
LeanProgram(opcode, operands)` as data, for a documented operand sample
including `rd = x0` and boundary shifts, for opcodes not yet covered by W1c.

#### W1b — Value-primitive differential fuzzing

- The pure value functions (`jolt_virtual_pow2_value`, `change_divisor_value`,
  `jolt_mulhu_value`, `jolt_virtual_srl_value`, ...) encode Jolt's
  lookup-table/constraint semantics (the T5 side).
- Cross-check each against its Rust implementation on randomized inputs.
- Note: advice-dependent expansions inject advice at tracer runtime, which the
  static golden corpus does not cover. This includes DIV/REM
  `fill_virtual_advice`, SC success advice, registered-inline `build_advice`,
  and advice-load source instructions. The differential harness should exercise
  each advice path explicitly.

Acceptance criteria: a fuzz target per primitive with a documented input
distribution and iteration count, green in CI.

Dependencies: W1a/W1b are the interim net; W1c is the durable fix and the
recommended primary investment given full Rust malleability.

---

### W2 — Anti-vacuity: inhabitance witnesses (VACUITY)

**Status: not-started, but the central question is now answered. Effort: M.
Recommended first — escalated to urgent by the June 2026 deep audit:
`mem_populated` is confirmed unsatisfiable (see unknown 1 resolution), so the
~219 `JoltConfig`-hypothesized theorems are vacuous as stated until the
finite-footprint migration lands.**

Goal: prove every assumption bundle is satisfiable, so no family's theorems are
vacuously true.

Rationale: a proof under contradictory hypotheses is indistinguishable from a
real one. There is currently no inhabitance check anywhere in `JoltBytecode/`.

Tasks:

- First produce a complete inventory of hypothesis bundles, not only the
  obvious ones. Include `JoltConfig`, `EcallSystemAssumptions`,
  `CsrrwSystemAssumptions`, `StoreFamily.StoreMemoryAssumptions`,
  `AtomicFamily.AmoMemoryAssumptions`,
  `LoadReservedFamily.LoadReservedMemoryAssumptions`, `FlatPhysMem`,
  `FlatStoreMem`, `FlatLoadStoreMem`, `FlatAtomicMem`,
  `FlatLoadReservedMem`, and the CSR access/legalizer assumptions.
- For each inventoried predicate/structure used as a theorem hypothesis,
  construct a concrete witness as a checked `example`, or document why the
  current predicate is intentionally uninhabited and replace it before relying
  on any theorem that uses it.
- Prefer a single realistic `initialJoltState` builder from which the bundles
  are *jointly* derivable, so co-satisfiability (not just per-predicate
  satisfiability) is demonstrated.
- `JoltConfig.mem_populated` is **resolved: unwitnessable** (finite
  `Std.ExtHashMap` vs `∀ addr : Nat`; unknown 1 resolution has the full
  consumer list). Replace it with a finite memory-footprint assumption and
  migrate the `readBytes_*_eq_loaded_*` bottleneck (`Memory/Utils.lean:381–435`)
  and the store-splice/AMO consumers; public statements keep their shape.

Acceptance criteria: a file (for example
`JoltBytecode/InstructionEquivalence/AssumptionsAreSatisfiable.lean`) containing
a witness `example` for every surviving hypothesis bundle, in the root build;
or a smaller, proved finite-footprint memory contract replacing the global
`mem_populated` assumption before the witness file is finalized.

Dependencies: none.

---

### W3 — Statement-strength validation: mutation testing (WEAK STATEMENT)

**Status: not-started. Effort: M. Highest insight.**

Goal: empirically confirm each equivalence theorem actually constrains what we
think it does.

Rationale: the most direct answer to "could the spec be wrong and the proof
still pass." If a deliberately corrupted `xProgram` still satisfies its
`*_eq_sail` theorem, the statement is too weak. The test must be semantic,
not merely "the old proof script stopped compiling": a brittle proof script is
not evidence that the theorem statement rules out the mutant.

Approach (decided June 2026, revised after audit): do the **lightweight version
first**, but make each spot-check semantic. One hand-picked mutant per selected
public theorem branch (swap two operands, drop a sign-extend row, change an
immediate, flip a scratch register) should be shown to contradict the theorem
statement or produce a concrete semantic counterexample. Only build the full
automated harness if a spot-check reveals a surviving mutant (a too-weak
theorem), since that is the signal that systematic coverage is worth the cost.

Tasks (lightweight):

- Define the mutation unit explicitly. Use public theorem branches where they
  exist (`*_eq_sail_aligned`, `*_eq_sail_misaligned`, `_concrete`,
  `_rel_sail`), not only README-level families.
- For each mutation unit, corrupt the relevant `xProgram` once and either
  produce a semantic counterexample or show that the corresponding theorem
  statement cannot be re-established under the mutant with a fresh proof
  attempt. Do not count breakage of the original proof script alone as a killed
  mutant.
- A mutation that leaves the build green is a finding: the theorem is too weak
  or the mutation is semantically inert (document which).
- Track shared helpers separately. Mutating a shared expansion block can kill
  many theorem fronts at once, so survivor/kill attribution must say which
  theorem statement was actually tested.
- Exclude deferred LR/SC theorem fronts until closed public equivalence theorems
  exist.

Tasks (full, only if triggered):

- A harness that injects a mutation catalogue and reports kill rate per family,
  run as an offline/nightly job, not on the critical path.

Acceptance criteria (lightweight): a short report showing one semantically
killed mutant per selected public theorem branch, with triage notes for any
survivor or inert mutation.

Dependencies: most informative once W2 rules out vacuity (a vacuous theorem
trivially "survives" all mutations).

---

### W4 — Frame conditions and projection justification (WEAK STATEMENT)

**Status: not-started. Effort: M.**

Goal: make explicit what each theorem promises about the *whole* state, and why
each projection is the faithful comparison.

Rationale: `projectResult` discards `vregs`, so architectural-equivalence claims
are silent about scratch state. That is a legitimate scoping decision, but it
must be stated, and the dual safety property should be proved. There are now
three comparison shapes (`projectResult`, `systemProjectResult`,
`EbreakResultRelation`); each is a place a spec can be subtly wrong.

Tasks:

- Document the scratch-register scoping invariant: expansions may leave
  arbitrary values in unused virtual registers; the claim is purely
  architectural. Where virtual registers are used as cross-row temporaries,
  prove only the local write-before-read facts needed by that expansion or
  helper block. A repository-wide SSA theorem is a separate project, not the
  default W4 deliverable.
- Prove a lemma relating `systemProject` to `project` off the CSR keys, and
  record why `systemProjectResult` is the faithful projection for ECALL/MRET/CSR
  (Jolt holds CSRs in persistent virtual registers).
- Consolidate the existing argument for `EbreakResultRelation` being
  intentionally a relation, not equality (constructor mismatch is by design).
- Confirm no theorem asserts only the written register and leaves the rest of
  the state existentially loose; the `stateAfterWrite`-based `_concrete` lemmas
  already capture full frame, so this is an audit, not a rewrite.

Acceptance criteria: a short `Projections.md` (or module docstring) justifying
each projection, plus the CSR-off-key lemma and any local scratch-register
lemmas needed by audited expansion blocks in the build.

Dependencies: none.

---

### W5 — Trusted base lockdown (BAD BASE)

**Status: not-started. Effort: M.**

Goal: make T3, T4, and T7 mechanically guarded so the trusted semantics cannot
silently diverge from genuine upstream Sail.

Rationale: a silent edit to `LeanRV64D/` is the scariest possible bug, because
no proof will ever flag it. The README asserts `LeanRV64D/` is "trusted/generated
except for the platform change"; that exception should be the *only* allowed
delta and should be enforced.

Tasks:

- Bootstrap provenance first: pin the exact sail-riscv commit, lean-sail
  version, and Lean toolchain that generated `LeanRV64D/`. Today the repo pins
  the Lean toolchain and `lean-sail` dependency, but does not record the
  sail-riscv generation commit or a regeneration command.
- June 2026 audit facts to build on: `LeanRV64D/` was imported in commit
  `c3bceb3` (2026-03-23) and has exactly one post-import edit, `b9bcdf5`
  (2026-04-18, the `PlatformConfig.lean:206` flip) — git-verified. The
  generation inputs are *not* recoverable from the repo: generated files have
  no provenance headers and the upstream generator
  (`LayerZero-Research/sail-riscv-lean`) clones unpinned sail-riscv and Sail in
  CI. First task: match the imported tree against sail-riscv-lean history to
  identify the generation snapshot, then pin upstream.
- Add a reproducible regeneration script for `LeanRV64D/`.
- After regeneration works locally, add CI that regenerates `LeanRV64D/` and
  diffs against the checked-in tree, allowing exactly one reviewed patch:
  `plat_enable_misaligned_access := false` (expressed as a standalone patch
  file). Until that CI exists, "exactly one patch" is an assumption, not an
  established fact.
- Document T7 (toolchain mismatch) as an explicit accepted risk with the reason
  it is believed benign.

Acceptance criteria: first, checked-in provenance metadata and a regeneration
script; second, a green CI job proving the checked-in `LeanRV64D/` equals
upstream-generated output plus a single named patch.

Dependencies: none. Enables W6.

---

### W6 — Validate the misaligned-flag edit (BAD BASE)

**Status: investigated; reframed. Effort: M.**

Original hypothesis (eliminate the edit via reachability) is **withdrawn**. The
edit is load-bearing, not a convenience.

Finding (June 2026): the Lean store and AMO proofs include explicit alignment
assertion rows where their modeled Jolt program needs an early alignment
failure (`VirtualAssertWordAlignment` in `Expansions/Store.lean`,
`VirtualAssertD/Word` in the AMO programs). Those asserts do **not** make the
misaligned Sail path unreachable. They make the *Jolt* side fault. The proofs
include explicit misaligned-branch theorems, e.g. `swProgram_eq_sail_misaligned`
(`StoreFamily/Sw_main.lean:411`), whose Sail side
(`execute_SW_misaligned`, `Sw_main.lean:377`) depends on
`access_causes_misaligned_exception (Virtaddr ea) 4 false = true`. With
`plat_enable_misaligned_access := true`, Sail would split the access instead of
faulting and that theorem would break. So T4 is required for the misaligned
branch of SH/SW/AMO to match.

This W6 fact is separate from the W1 row-level drift finding: Rust doubleword
AMO expansion currently relies on MMU alignment assertions rather than emitting
the explicit `VirtualAssertDwordAlignment` row that Lean models.

Reframed goal: the flag is a *faithfulness modeling choice* (Jolt faults on
misalignment, it does not split), so the work is to justify and isolate it, not
remove it.

Tasks:

- Confirm against the Rust/Jolt platform that misaligned multi-byte ordinary
  accesses are rejected rather than split, so the flag value is the faithful
  no-split model and not just the convenient one. Record evidence from the Rust
  MMU alignment assertions, virtual alignment assertion rows, and ACT4 Sail
  config. (June 2026 audit confirmed the MMU side: `load_doubleword` /
  `store_doubleword` hard-panic via `assert_eq!(ea % 8, 0)` at
  `tracer/src/emulator/mmu.rs:362,470` — rejects, never splits.)
- State the layer distinction explicitly: Sail with the flag disabled raises an
  architectural alignment exception; Lean `execInstr` models the virtual
  alignment rows as `Memory_Exception`; Rust host execution generally reaches
  `assert!` / panic on the same bad access rather than producing an architectural
  trap value. The proof's current claim is no-split semantic alignment, not
  equality to Rust panic behavior.
- Scope byte accesses out of this concern: byte loads/stores are always aligned
  by width and need no misaligned-fault argument.
- Ensure the edit is isolated as the single reviewed patch guarded by W5.

Acceptance criteria: a written, evidence-backed justification that
`plat_enable_misaligned_access := false` matches Jolt's real platform behavior,
referenced from `README.md`, plus the W5 diff guard allowing exactly this patch.
The justification must explicitly say "rejects rather than splits" and must not
claim Rust host execution produces the same trap object as Sail.

Dependencies: W5.

---

### W7 — TCB enumeration and axiom audit (BAD BASE)

**Status: not-started. Effort: M. Pairs with W2, but can run after W1 theorem
inventory is stable.**

Goal: make the trusted base enumerable and CI-checked, and shrink the
`native_decide` surface.

Tasks:

- Add `#print axioms` for every public `*_eq_sail` / `*_rel_sail` theorem and
  assert the axiom set is exactly the expected one. This simultaneously catches
  accidental `sorry`, new `axiom`s, and `native_decide` (`Lean.ofReduceBool`)
  leaking into theorems where it was not intended. This gate is also the meter
  for the `native_decide` removal below.
- Add a separate declaration-level scan for `sorry`, `axiom`, and
  `native_decide` in `JoltBytecode/`. This is distinct from theorem axiom
  printing: deferred LR/SC modules contain explicit reservation axioms even when
  no closed public theorem uses them.
- Curate the theorem list. Important helper theorems do not all match the
  `*_eq_sail` / `*_rel_sail` naming pattern, so the gate should start from the
  README coverage surface and include any helper theorem that is itself part of
  the public proof claim.
- Remove `native_decide` from `JoltBytecode/`. Investigated June 2026: no
  fundamental obstruction. The sites fall into four decidable buckets:
  - **A. BitVec value facts** (`sign_extend (0:BitVec 21) = 0#64`,
    `privLevel_to_bits .Machine = 0b11`, `jolt_virtual_muli_value 3 2048 =
    zeroOSMstatus`, `ecallMachineCause = 11#64`): replace with kernel `decide`
    — **not `bv_decide`** (see the empirical resolution of unknown 7: the
    `bv_decide` SAT path introduces a `*._native.bv_decide.ax_*` axiom, same
    trust class as `native_decide`). Verified on the pinned toolchain that
    `decide` closes the real ProgramBlocks goals with `[propext]` only, fast.
  - **B. VReg (`BitVec 7`) distinctness** (`trapHandlerVReg ≠ mstatusVReg`,
    many): `decide`, trivial.
  - **C. `Register` enum distinctness and map-key `≠`** (`Register.nextPC ≠
    Register.mtvec`, `(Register.mstatus == reg) = false`): `decide` via derived
    `DecidableEq`. The `Register` enum has ~180 constructors
    (`LeanRV64D/Defs.lean:1526`), so the only real risk is **compile time**, not
    possibility; mitigate with a one-time fast distinctness helper via a tag
    projection (`toCtorIdx` injectivity) instead of full `decide` per pair.
  - **D. small-enum `BEq`** (`CSRAccessType`): `decide`, trivial.
- Two caveats, both practical not fundamental: (1) kernel `decide` / `bv_decide`
  is slower than compiled `native_decide`, so watch build time, especially
  bucket C and 64-bit BitVec goals; (2) a few facts route through generated Sail
  helpers (`privLevel_to_bits`, `trapCause_bits_forwards`) that must be
  structurally reducible for `decide` (they appear to be; if any hides an opaque
  or well-founded def, give it a manual unfolding lemma).
- **Verified June 2026 (experiment on v4.29.0-rc4):** `bv_decide` is *not*
  kernel-only. When `bv_normalize` closes the goal it adds no extra axioms
  (`[propext, Quot.sound]`), but when the SAT/LRAT path runs the proof depends
  on a generated `<decl>._native.bv_decide.ax_*` axiom — same trust class as
  `native_decide`, which itself appears in this toolchain as
  `<decl>._native.native_decide.ax_*` rather than bare `Lean.ofReduceBool`.
  Therefore: the axiom gate must flag generated `*._native.*` axioms by
  pattern, and the 163 existing `bv_decide` sites in `JoltBytecode/` must be
  audited alongside the 104 `native_decide` sites.

Acceptance criteria: the axiom gate shows every closed public equivalence
theorem depends only on the expected standard axioms, with no
`Lean.ofReduceBool` and no generated `*._native.*` axioms (from either
`native_decide` or `bv_decide`'s SAT path); explicit deferred-hook axioms are
listed separately and do not silently enter closed theorem dependencies; zero
`native_decide` in `JoltBytecode/`; documented build-time impact.

Dependencies: none. Build the axiom gate first; it measures the removal.

---

### W8 — Coverage completeness tied to the type (WEAK STATEMENT / process)

**Status: not-started. Effort: S.**

Goal: prevent a Jolt source instruction from being silently uncovered.

Rationale: the coverage table in `README.md` and `roadmap.md` is prose. A newly
added instruction can drift out of the table without notice.

Tasks:

- Define the closed source-opcode universe first. `JoltBytecode` currently has
  final-row `Instr` syntax and hand-written expansion definitions, but not a
  Lean-side type for Rust's full `SourceInstructionKind`. The source universe
  should come from a generated Rust manifest or an explicitly maintained Lean
  inductive that is checked against Rust.
- Once the universe exists, bind every opcode to exactly one of `{proved,
  proved-under-assumptions, advice, deferred, out-of-scope}`, mechanically (an
  exhaustiveness check or a checked table).
- Reconcile the classification with imports. Deferred LR/SC files are imported
  for boundary documentation, while CSRRS is deferred and not in the root build;
  the coverage table should make that distinction explicit.

Acceptance criteria: a generated or checked source-opcode manifest, then a
build-time or CI check that fails if a source opcode has no classification.

Dependencies: none.

---

### W9 — Spec hygiene (process)

**Status: not-started. Effort: M for memory-envelope unification, S for
`WellFormed` cleanup.**

Goal: remove dead and duplicated specification that misleads auditors.

Tasks:

- `WellFormed` (`InstructionEquivalence/ProofSupport.lean:22`) is defined and
  unused. Remove it or wire it into the statements that need it. Because it
  expresses architectural-register readability, check first whether it is useful
  for W2 witnesses or W4 frame audits before deleting it.
- Centralize the ordinary Sail-memory access predicate (already flagged in
  `LEAN_BYTECODE_MODEL_LIMITATIONS.md` item 1) so load/store/AMO theorems share
  one named envelope instead of family-local restatements.
- Update `LEAN_BYTECODE_MODEL_LIMITATIONS.md` while doing this cleanup. It
  mentions `BareTranslation`, which is not a current Lean predicate.

Acceptance criteria: no dead hypothesis predicates; a single shared
ordinary-memory predicate used across memory families.

Dependencies: coordinate with the memory-envelope cleanup in
`LEAN_BYTECODE_MODEL_LIMITATIONS.md`.

## Sequencing

Dependency-ordered, optimized for early certainty per unit of agent runtime:

1. **W2 first, with W9's memory-envelope cleanup if needed.** The global
   `mem_populated` assumption is the largest vacuity unknown; either prove it
   inhabitably or replace it with a finite footprint contract before treating
   memory-family theorems as non-vacuous.
2. **W1 next.** The AMO.D alignment-row mismatch shows expansion conformance is
   already actionable. Start with W1a on a small structural manifest, then move
   to W1c for a generated artifact.
3. **W7 in parallel once theorem inventory is stable.** Build the axiom/declaration
   gate early, then use it to measure `native_decide` removal.
4. **W3 after W2/W1 have stabilized the object under test.** Mutation testing is
   most meaningful once the assumptions are non-vacuous and the expansion being
   mutated is known to be the intended Rust shape.
5. **W4 alongside W3.** Projection documentation and CSR off-key lemmas are
   localized; global scratch-register SSA is explicitly out of scope unless a
   local theorem needs it.
6. **W5, then W6.** Bootstrap regeneration provenance first; then justify and
   isolate the single misaligned-access patch.
7. **W8 after the source-opcode universe is chosen.** It is small only after the
   Rust or Lean opcode manifest exists.

## Focused unknowns — resolutions (June 2026 deep audit)

The follow-up audit (June 11, 2026; both repos plus toolchain experiments) has
resolved or sharply narrowed all ten unknowns. Findings below supersede the
original questions; each item records the evidence and the action it implies.

1. **`JoltConfig.mem_populated` — RESOLVED: unsatisfiable.** Sail memory is
   `Std.ExtHashMap Nat (BitVec 8)` (lean-sail `Sail/Sail.lean:470`), a finite
   map; no concrete state can satisfy `∀ addr : Nat, s.mem.get? addr ≠ none`
   (`JoltBytecode/JoltISA/Environment.lean:77`). Every theorem hypothesizing
   `JoltConfig` (~219 by grep) is therefore vacuous as stated today. The fix is
   mechanical, not structural: all 16 direct consumers (the
   `readBytes_*_eq_loaded_*` bottleneck at `Memory/Utils.lean:381–435` and its
   `mem_read_*` clients, the store-splice lemmas in `StoreFamily/S{b,h,w}_main.lean`,
   and the AMO bridging lemmas) touch at most 8 consecutive bytes around one
   base address, so a finite-footprint hypothesis
   (`∀ k, base ≤ k < base + w → s.mem.get? k ≠ none`) suffices, and the public
   statements already carry local `FlatPhysMem`-style envelopes. W2 is hereby
   escalated from investigation to urgent trust repair.
2. **AMO.D conformance target — RESOLVED: real drift; fix Rust, not Lean.**
   Verified in source: `expand_amo_d`
   (`crates/jolt-program/src/expand/memory/shared.rs:182`) emits LD / op / SD /
   ADDI with no assert row (`expand_amoswapd`: LD/SD/ADDI,
   `expand/memory/amoswapd.rs:8`); misalignment instead hits
   `assert_eq!(ea % 8, 0)` host panics in `tracer/src/emulator/mmu.rs:362,470`
   — a tracer panic, not a provable trap. Lean
   (`JoltISA/Expansions/Atomics.lean:192,271`) prepends
   `VirtualAssertDwordAlignment`. AMO.W carries the explicit
   `VirtualAssertWordAlignment` row on *both* sides (`shared.rs:413`,
   `Atomics.lean:145`), so AMO.D is the inconsistency inside Rust, not Lean
   inventiveness. Recommendation: Rust emits the explicit dword-assert row —
   consistent with AMO.W, consistent with W6's "faults, not splits" model, and
   it gives the misaligned path provable trap semantics. Dropping the Lean row
   instead would orphan the `*_eq_sail_misaligned` theorems. Secondary check
   for the first W1a manifest: the audit saw slightly different AMO.W
   pre64/post64 row counts on the two sides; confirm row-for-row.
3. **Rust `exec()` vs trace drift — RESOLVED.** The prover never consumes
   source-instruction `exec()`. Proof semantics are defined by the expansion
   path (`inline_sequence`, `tracer/src/instruction/mod.rs:706`) plus the
   lookup/constraint definitions (`crates/jolt-lookup-tables/src/instructions/`);
   `exec()` is the emulator fast path only, and no existing test compares the
   two paths, so they can diverge silently. T5's conformance target is the
   per-row semantics of Jolt rows plus their lookup tables — not source
   `exec()`. One candidate divergence to triage upstream: SC.D `exec()` vs
   `trace()` reservation-clearing behavior (`tracer/src/instruction/scd.rs`,
   ~line 40 vs 69). A cheap Rust-side exec-vs-expansion differential harness is
   a natural W1b companion.
4. **Metadata in conformance — RESOLVED: all three fields are semantic.**
   `virtual_sequence_remaining` feeds the bytecode PC mapping consumed by the
   constraint system (`crates/jolt-program/src/preprocess/bytecode.rs:57–65,106–112`);
   `is_first_in_sequence` and `is_compressed` gate constraints
   (`crates/jolt-riscv/src/lib.rs`). Row type: `JoltInstructionRow`
   (`crates/jolt-riscv/src/row.rs:74–81`). W1 conformance must therefore check
   them rather than ignore them: verify structural position in the Lean
   `Program` matches `virtual_sequence_remaining` ordering, derive
   `is_first_in_sequence` from position, and carry `is_compressed` in the
   manifest as out-of-Lean-model but diffed.
5. **Advice-path inventory — RESOLVED.** (a) DIV/REM ×8 via
   `fill_virtual_advice` (`tracer/src/instruction/mod.rs:167–181`): quotient +
   remainder advice constrained by AssertValidDiv0 /
   AssertValidUnsignedRemainder / recomposition rows
   (`expand/division/shared.rs`). (b) SC.W/D success boolean patched into
   `VirtualAdvice` (`tracer/src/instruction/scd.rs:44–71`). (c)
   Registered-inline `build_advice`: only the big-int field ops use it
   (secp256k1/p256/grumpkin `mulq_advice`,
   `jolt-inlines/sdk/src/host.rs:106–159`); SHA-2/Keccak/Blake are
   deterministic with no advice. (d) AdviceLB/LH/LW/LD read the advice tape and
   expand to `VirtualAdviceLoad` (`expand/memory/shared.rs:146–174`). (e)
   `VirtualAdviceLen` is unconstrained/informational. Structural fact that
   scopes W1b: the `VirtualAdvice` row itself is only range-checked — all
   soundness lives in the downstream assert rows, which are exactly the value
   primitives Lean encodes. W1b fuzz targets: each assert-row value function
   plus each generator above.
6. **Source-opcode universe — RESOLVED.** Authoritative:
   `for_each_instruction_kind!` (`crates/jolt-riscv/src/lib.rs:20–162`), 135
   source kinds (enum `SourceInstruction`, 138 variants incl.
   Noop/Unimpl/InlineDispatch): 67 map 1:1 to `JoltInstructionKind`, 68 expand,
   1 inline dispatch. `SourceInstructionKind::ALL` and canonical-name
   serialization already exist, so the W8 manifest is generable today with a
   small exporter and no new enum infrastructure. Compressed instructions are
   normalized before the enum (`uncompress.rs`), tracked by `is_compressed`.
   Known fixture gap to enumerate during W1a: the main expand fixtures cover 66
   unique opcodes vs 68 expanded kinds.
7. **`bv_decide` TCB — RESOLVED empirically; the W7 bucket-A guidance was
   wrong as originally written.** Experiment on the pinned v4.29.0-rc4: kernel
   `decide` proves the real `native_decide` goals (e.g.
   `StoreFamily/ProgramBlocks.lean:196,201`) with axioms `[propext]`, and
   180-constructor enum distinctness with *no* axioms, in negligible time.
   `bv_decide` adds no extra axiom only when `bv_normalize` closes the goal;
   when the SAT/LRAT path runs, the theorem depends on a generated
   `<decl>._native.bv_decide.ax_*` axiom — the same trust class as
   `native_decide` (which in this toolchain likewise appears as
   `<decl>._native.native_decide.ax_*`, not as bare `Lean.ofReduceBool`).
   Consequences: (i) replace `native_decide` with `decide`, not `bv_decide`;
   (ii) the axiom gate must flag `*._native.*` generated axioms, not only
   `Lean.ofReduceBool`; (iii) the **163 existing `bv_decide` sites** in
   `JoltBytecode/` need auditing — any that hit the SAT path already carry
   native axioms today. Current counts: 104 `native_decide`, 163 `bv_decide`.
   Stale `NoExtraAxioms.olean` / `RV64IMAC.olean` build artifacts with no
   surviving sources suggest a previous axiom-gate experiment was deleted;
   resurrect it under version control.
8. **`LeanRV64D/` provenance — RESOLVED as a negative result with a
   reconstruction path.** Git-verified: imported in commit `c3bceb3`
   (2026-03-23, 154 files); exactly one post-import edit, `b9bcdf5`
   (2026-04-18), flipping `PlatformConfig.lean:206` `true → false` with a
   WARNING comment; nothing since. So "exactly one edit *since import*" is now
   established. What cannot be established: the generation inputs — generated
   files carry no provenance headers, and the upstream generator
   (`LayerZero-Research/sail-riscv-lean`) clones unpinned latest sail-riscv and
   Sail in its CI. W5 bootstrap: match the imported tree against
   sail-riscv-lean commit history to identify the generation snapshot, then pin
   sail-riscv + Sail revisions upstream and record them in-repo.
9. **System/CSR joint satisfiability — PARTIALLY RESOLVED; one real
   composition gap.** Each bundle (`EcallSystemAssumptions`,
   `System/Common.lean:1657`; `CsrrwSystemAssumptions`, `Csrrw.lean:335`;
   `MretSystemAssumptions`, `Mret.lean:542`) appears individually satisfiable —
   W2 should construct the witnesses. But ECALL leaves the mstatus vreg at
   `zeroOSMstatus = 0x1800` (MPIE=0, MIE=0; `Common.lean:36`), while MRET
   assumes `MPIE = 1` and `MIE = MPIE` (`Mret.lean:563–567`) precisely so that
   Sail's xret mstatus update is a no-op. The modeled ECALL → handler → MRET
   round trip is therefore *not* covered by composing the two theorems unless
   the handler rewrites mstatus (e.g. CSRRW) in between. Action: check what
   ZeroOS actually executes between trap entry and `mret`; either document the
   required intermediate mstatus write as part of the environment contract, or
   rework the MRET assumptions / Jolt mstatus modeling. Relatedly, ECALL's
   `trap_vector_matches_jalr` and `trap_target_fetch_aligned` are loader-time
   environment invariants and belong in a documented ZeroOS contract (W4/W2).
10. **Scratch-register invariants — RESOLVED: no global work needed.** No
    public theorem exposes vregs: `projectResult` (`JoltISA/Core.lean:51`)
    discards all vregs; `systemProjectResult` (`System/Common.lean:78`)
    overlays only the persistent CSR vregs; `EbreakResultRelation`
    (`Ebreak.lean:165`) is intentionally a relation. Cross-row temporaries
    (ECALL scratch, CSRRW `rd = rs1` save/restore, DIV `t0–t4` phases,
    load/store address temps) are already discharged inside existing
    phase/block proofs. W4 reduces to its documentation deliverable plus the
    systemProject off-CSR-key lemma.

## Definition of "more trustworthy" (exit criteria)

The effort has materially improved trust when:

- no equivalence theorem can be vacuous (W2);
- the TCB is a short, CI-asserted, documented list (W7), with `native_decide`
  minimized;
- a deliberate corruption of any `xProgram` provably breaks its theorem (W3);
- each projection has a written faithfulness justification and the scratch-state
  scope is explicit (W4);
- the trusted Sail base is provably genuine upstream plus one named patch (W5),
  with that patch justified as faithful to Jolt's real platform behavior (W6);
- Lean and Rust expansions are continuously cross-checked, ideally generated
  from one source (W1).

## Cross-references

- `planning/roadmap.md` — coverage and scope status.
- `planning/LEAN_BYTECODE_MODEL_LIMITATIONS.md` — current scope risks and the
  ordinary-memory-envelope cleanup (W9 depends on it).
- `planning/JOLT_EXPANSION_DSL_DESIGN.md` — input to W1c.
- `planning/JOLT_SPECIAL_MEMORY_REGION_PLAN.md`,
  `planning/JOLT_TRACE_METADATA_PLAN.md` — out-of-scope boundaries this plan
  does not touch.
- `README.md` — theorem shape, coverage table, the misaligned-access edit (T4).
