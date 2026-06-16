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
fail to deliver a meaningful guarantee in six ways, and every item below targets
one of them:

1. **Drift.** The Lean specification (`execInstr` per-row semantics, and the
   `xProgram` expansions) is hand-transcribed from Rust and only *asserted*
   faithful. If the transcription is wrong, we prove the wrong thing correctly.
   This is the dominant risk.
2. **Vacuity.** If an assumption bundle (`JoltConfig`, `EcallSystemAssumptions`,
   the memory predicates) is internally contradictory, every theorem about it is
   vacuously true. The June 2026 deep audit found the old
   `JoltConfig.mem_populated` field was unsatisfiable; the load/store/AMO
   theorem boundary now uses finite primitive memory windows instead.
3. **Weak statement.** A theorem can be true but under-constrain the result: a
   loose postcondition, a projection that discards exactly the bits that differ,
   or a comparison against the wrong Sail function.
4. **Bad base.** The trusted reference (`LeanRV64D/`) is Sail-generated but has
   at least one deliberate edit. Earlier proof closures also trusted generated
   `_native` solver axioms, but the June 2026 W7 cleanup removed those from the
   public Jolt theorem dependency scan (`752` targets,
   `native_dep_theorems=0`, `native_axioms_unique=0`). The remaining risk is
   regression control: keep the scan checked in and CI-enforced. The
   `LeanRV64D/` provenance/edit issue is documented and deferred; it is not an
   active hardening blocker.
5. **Assumed conclusion.** A hypothesis bundle can contain the very
   correspondence the theorem is meant to establish. The June 2026 deep audit
   found this in the system family: 8 of ~30 fields across
   `CsrrwSystemAssumptions`/`EcallSystemAssumptions`/`MretSystemAssumptions`
   assume Sail and Jolt already agree (CSR read/write match the vreg, the four
   MRET mstatus fields make Sail's xret postlude a no-op). The proofs are valid
   but the system-family guarantee is weaker than the theorem names imply (W10).
6. **Non-composition.** Every public theorem is per-instruction and assumes a
   fresh start-state bundle; nothing proves an expansion *preserves* the
   invariants the next instruction needs (`JoltConfig`, the persistent CSR
   vregs, untouched memory). Because `projectResult` discards all vregs, an
   expansion that clobbered `mstatusVReg` would satisfy its own theorem while
   silently breaking every later system theorem. No two per-instruction results
   can be chained today (W11).

## Trusted Computing Base (TCB) ledger

Everything the final guarantee rests on, today. Keeping this list short and
explicit is part of the recorded TCB discipline; W7's active cleanup is closed,
with only optional regression-gate work remaining.

| # | Trusted element | Kind | Notes |
| --- | --- | --- | --- |
| T1 | Lean kernel + standard axioms (`propext`, `Classical.choice`, `Quot.sound`) | unavoidable | acceptable; just enumerate |
| T2 | Native-evaluation axioms (`*._native.native_decide.ax_*` / `*._native.bv_decide.ax_*`; the `Lean.ofReduceBool` trust class) | regression risk | Repaired for public Jolt theorem closures in June 2026: broad scan reported `752` targets, `native_dep_theorems=0`, `native_axioms_unique=0`. Current source count is `0` `native_decide` and `60` `bv_decide` in `JoltBytecode/`; an optional CI gate can prevent regression, but there is no active public-theorem dependency issue |
| T3 | `LeanRV64D/` Sail-generated RISC-V semantics | reference spec | trusted by design; provenance is documented externally and W5 is deferred |
| T4 | `plat_enable_misaligned_access := false` edit to T3 | base edit | load-bearing for the misaligned branch of SH/SW/AMO; git shows it is the only semantic post-import edit, and W6 records why it is intentional |
| T5 | Faithfulness of `execInstr` to Rust per-row `cpu_exec` semantics | unproven | drift risk (W1). Sharpest for single-row native instructions (ADD, MUL, MULHU, ANDN, branches, JAL, FENCE) whose `execInstr` case has **no equivalence theorem at all** — a transcription typo there is currently unfalsifiable until W1 adds Rust/Lean conformance coverage |
| T6 | Faithfulness of `xProgram` definitions to Rust `inline_sequence` emission | unproven | drift risk; the AMO.D row mismatch was repaired in Lean, but no general Rust-to-Lean expansion check exists yet (W1) |
| T7 | Toolchain mismatch: `v4.29.0-rc4` vs lean-sail's target nightly | environment | documented in `README.md`; not active hardening work |
| T8 | lean-sail runtime (`Sail` package: `SequentialState`, BitVec/`shift_bits_right` helpers, memory primitives, the `EStateM` monad) | reference runtime | trusted by everything, pinned at tag `v3`; distinct from generated `LeanRV64D/` (T3) and included in W7's axiom/TCB scope |
| T9 | jolt-qed's own `sailReadByte`/`sailReadWord`/`sailReadDword` (`Environment.lean:28–45`) | bridge definition | trusted Lean definitions, proven equal to Sail's `vmem_read` only under the primitive finite-window memory evidence used by the current load/store/AMO theorem bundles |
| T10 | Decode/encode: Rust decoder vs Sail `encdec`, and PC-step/fetch/interrupt loop (`LeanRV64D/Step.lean`) | out of model | every theorem is at the post-decode `execute_*` level; decode agreement and the step loop are checked by *nothing*, in this plan or W1. See the claim-boundary note in `LEAN_BYTECODE_MODEL_LIMITATIONS.md` and the decode-differential addition to W1 |

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
   audit found a row-granularity AMO.D mismatch: Lean had a hallucinated
   doubleword virtual assert row, while Rust's `expand_amo_d` emits
   `LD` / op / `SD` / `ADDI` and `expand_amoswapd` emits `LD` / `SD` / `ADDI`.
   The Lean ISA and AMO.D expansions now remove that row and model the dword
   `LD`/`SD` row itself as the alignment boundary.

4. **Memory inhabitance — repaired for load/store/AMO theorem boundaries.**
   The old `JoltConfig.mem_populated` field (`∀ addr : Nat, s.mem.get? addr ≠
   none` over Sail's finite `Std.ExtHashMap Nat (BitVec 8)`) was unsatisfiable.
   It has been removed from `JoltConfig`. Load/store/AMO public theorem bundles
   now assume only finite primitive windows for the bytes each instruction can
   touch, and derive exact `Flat*` memory evidence internally.

5. **ALU / ALUAdvice public assumption boundary — repaired.** Ordinary ALU and
   advice-backed DIV/REM public equivalence theorems now take only source-register
   read bundles: one read for unary/immediate ALU, two reads for binary ALU and
   ALUAdvice. Destination writes, advice correctness, and phase facts remain
   internal proof obligations, not public assumptions.

## Workstreams

Status legend: **not-started** / **in-progress** / **done** / **blocked**.
Effort is in agent-runtime terms. The binding constraint everywhere is the Lean
rebuild/recheck cycle, not authoring; size estimates assume that bottleneck.

### Current triage

Only three items are active trust issues:

| Workstream | Decision | Why |
| --- | --- | --- |
| W1 — Rust to Lean conformance | **Active** | We already found real drift: AMO.D's Lean program had a row Rust did not emit. |
| W2 — anti-vacuity / witnesses | **Partly done / active** | The impossible `JoltConfig.mem_populated` memory boundary has been replaced for load/store/AMO by finite primitive windows, and ALU/ALUAdvice theorem boundaries expose only source-register reads. Remaining W2 work is witness/co-satisfiability coverage for surviving bundles, especially system/CSR bundles. |
| W10 — system/CSR assumptions | **Active** | Several system theorem hypotheses assume the Sail/Jolt CSR correspondence the theorem name appears to prove. |
| W11 — composition/frame lemmas | **Later / conditional** | Real only if we want multi-instruction or trace-level chaining. Not a blocker for current per-instruction claims. |

The following are **not active workflows** and should not consume proof time in
the current cycle:

| Workstream | Decision | Why we are not pursuing it now |
| --- | --- | --- |
| W3 — mutation testing | **Rejected as standalone work** | This is a testing technique, not a discovered flaw. It becomes useful only after W1/W2/W10 define the real target. |
| W4 — projection/frame documentation | **Folded into W10/W11** | The only real projection problem is the CSR/system theorem shape. Generic scratch-register documentation is not a separate trust repair. |
| W5 — trusted-base provenance | **Deferred / low priority** | Git proves the only semantic post-import `LeanRV64D/` edit, and the broader generated-Sail provenance is documented externally. |
| W6 — misaligned flag | **Done / not an issue** | Jolt rejects misaligned multi-byte accesses rather than splitting them. The flag is intentional. |
| W7 — native solver TCB | **Closed; guard only** | The public theorem scan is already clean: `native_dep_theorems=0`, `native_axioms_unique=0`. Keep a regression gate later if desired. |
| W8 — coverage manifest | **Guard only, not soundness repair** | Useful to prevent future coverage drift, but it does not show any current theorem is false or weak. Do it only as part of W1 manifest work. |
| W9 — spec hygiene | **Folded into W2** | The real part is memory-envelope cleanup required by `mem_populated`; the rest is housekeeping. |

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
Lean repo. The repaired AMO.D alignment-row mismatch is the concrete warning
shot: the current plan should treat W1 as near-term trust repair, not late
process hardening.

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

#### W1d — Decode differential (NEW, June 2026 deep audit)

- Every conformance check above and every Lean theorem operates on *already
  decoded* operands. Neither this plan nor W1a–c checks that the Rust decoder
  and Sail's `encdec` agree on the bits → (opcode, rd, rs1, rs2, imm) mapping.
  S-type and B-type immediate scrambling is the classic place this silently
  diverges, and it sits entirely below T10.
- Add a differential fuzz target: random 32-bit (and 16-bit compressed) words →
  Rust decode vs Sail `encdec_backwards`/decoder → compare the normalized
  operand tuple. Compressed forms should be checked both directly and through
  Rust's `uncompress_rv64_instruction` normalization.

Acceptance criteria: a decode-differential fuzz target, green in CI, with a
documented word distribution covering each RV64IMAC encoding format and the
compressed set.

Dependencies: W1a/W1b are the interim net; W1c is the durable fix and the
recommended primary investment given full Rust malleability. W1d is independent
and closes part of T10.

---

### W2 — Anti-vacuity: inhabitance witnesses (VACUITY)

**Status: partly done. Effort: M.**

The urgent memory-boundary repair is complete for load/store/AMO:
`JoltConfig.mem_populated` has been removed, and public theorem bundles now use
finite primitive windows. The ALU and ALUAdvice public theorem boundaries have
also been reduced to minimal source-register read bundles. Remaining W2 work is
to add checked inhabitance / co-satisfiability witnesses for the surviving
bundles, especially system/CSR bundles.

Goal: prove every assumption bundle is satisfiable, so no family's theorems are
vacuously true.

Rationale: a proof under contradictory hypotheses is indistinguishable from a
real one. There is currently no inhabitance check anywhere in `JoltBytecode/`.

Tasks:

- First produce a complete inventory of surviving public hypothesis bundles,
  not only the obvious ones. Include `JoltConfig`,
  `LoadFamily.LoadProgramEqSailAssumptions`,
  `StoreFamily.StoreProgramEqSailAssumptions`,
  `AtomicFamily.AmoDwordProgramEqSailAssumptions`,
  `AtomicFamily.AmoWordProgramEqSailAssumptions`,
  `ALUFamily.UnarySourceReadAssumptions`,
  `ALUFamily.BinarySourceReadAssumptions`,
  `EcallSystemAssumptions`, `CsrrwSystemAssumptions`,
  `MretSystemAssumptions`, and the CSR access/legalizer assumptions.
- For each inventoried predicate/structure used as a theorem hypothesis,
  construct a concrete witness as a checked `example`, or document why the
  current predicate is intentionally uninhabited and replace it before relying
  on any theorem that uses it.
- Prefer a single realistic `initialJoltState` builder from which the bundles
  are *jointly* derivable, so co-satisfiability (not just per-predicate
  satisfiability) is demonstrated.
- The old `JoltConfig.mem_populated` issue is **resolved for load/store/AMO**:
  public memory assumptions are finite primitive windows, and exact read/write
  evidence is derived in `LoadFamily.Derived`, `StoreFamily.Derived`, and
  `AtomicFamily.Derived`.
- The ALU/ALUAdvice public theorem boundary is **resolved as a vacuity concern**:
  public assumptions are exactly source-register reads. The remaining hard
  assumption-boundary problem is the system/CSR family.

Acceptance criteria: a file (for example
`JoltBytecode/InstructionEquivalence/AssumptionsAreSatisfiable.lean`) containing
a witness `example` for every surviving hypothesis bundle, in the root build;
or a smaller, proved finite-footprint memory contract replacing the global
`mem_populated` assumption before the witness file is finalized.

Dependencies: none.

---

### W3 — Statement-strength validation: mutation testing (WEAK STATEMENT)

**Status: rejected as standalone active work. Effort: none in the active plan.**

NOTE: (ari) -- This is the CSRRs virtual mapping i think

Decision: do not pursue W3 as a workflow.

Why: mutation testing is a technique, not an identified trust bug. Running a
mutation harness before fixing W1/W2/W10 would mostly measure known problems:
Rust/Lean drift, vacuous memory hypotheses, and proof-shaped CSR assumptions.
It would add process without clarifying the actual proof boundary.

Where the useful part goes: after W1/W2/W10 land, a small mutation spot-check can
be used as validation evidence. It should not be planned as independent
14-day proof work.

Acceptance criteria: none.

Dependencies: none.

---

### W4 — Frame conditions and projection justification (WEAK STATEMENT)

**Status: not pursuing standalone; folded into W10/W11. Effort: none as a
separate workflow.**

Goal: no separate W4 workstream.

Rationale: the original W4 mixed a real issue with documentation. The real issue
is not "scratch registers are unconstrained" in general. Ordinary theorem
statements intentionally project away scratch vregs because the claim is
architectural. The real projection weakness is specific: system/CSR theorems use
persistent CSR vregs and assumption bundles that can assume the correspondence
they should establish. That is W10. If we later want multi-instruction
composition, preserving persistent vregs across ordinary instructions is W11.

Not pursuing:

- A global "vregs are preserved" theorem for every scratch register.
- Standalone projection documentation as a trust-repair deliverable.
- Generic frame-condition cleanup disconnected from a concrete theorem claim.

Where the useful parts go:

- W10: discharge or explicitly trust the CSR/system correspondence assumptions.
- W11: if trace composition becomes a goal, prove preservation/frame lemmas.

Acceptance criteria: none as W4.

Dependencies: none.

---

### W5 — Trusted base provenance (DEFERRED)

**Status: deferred / low priority. Effort: none in the active plan.**

Goal: no active work. This is not a current hardening blocker.

Rationale: the local fact needed for this audit is already git-verified:
`LeanRV64D/` was imported in `c3bceb3`, and the only post-import semantic edit is
`b9bcdf5`, changing `plat_enable_misaligned_access : true -> false` with a
warning comment. That edit is intentional and covered by W6. The broader
generated-Sail provenance story is documented externally in the project blog, so
we are not spending proof-engineering time reconstructing a regeneration CI path
inside this repo.

Optional future work, outside the active workflow list: add a regeneration
script and CI diff proving checked-in `LeanRV64D/` equals upstream-generated
output plus the single named platform patch.

Acceptance criteria: none for the active hardening plan.

Dependencies: none. Does not block W6.

---

### W6 — Validate the misaligned-flag edit (BAD BASE)

**Status: done / settled. Effort: none in the active plan.**

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
AMO expansion currently relies on the emitted dword memory row rather than a
dedicated virtual assert row, and Lean now models the same row shape.

Conclusion: the flag is a *faithfulness modeling choice* (Jolt faults on
misalignment, it does not split), not an issue to remove.

Recorded evidence:

- Rust/Jolt platform evidence: misaligned multi-byte ordinary
  accesses are rejected rather than split, so the flag value is the faithful
  no-split model and not just the convenient one. Evidence comes from the Rust
  MMU alignment assertions, virtual alignment assertion rows, and ACT4 Sail
  config. (June 2026 audit confirmed the MMU side: `load_doubleword` /
  `store_doubleword` hard-panic via `assert_eq!(ea % 8, 0)` at
  `tracer/src/emulator/mmu.rs:362,470` — rejects, never splits.)
- Layer distinction: Sail with the flag disabled raises an
  architectural alignment exception; Lean `execInstr` models the virtual
  alignment rows as `Memory_Exception`; Rust host execution generally reaches
  `assert!` / panic on the same bad access rather than producing an architectural
  trap value. The proof's current claim is no-split semantic alignment, not
  equality to Rust panic behavior.
- Byte accesses are out of scope for this concern: byte loads/stores are always aligned
  by width and need no misaligned-fault argument.
- Git shows the edit is isolated as the single semantic
  post-import patch to `LeanRV64D/`.

Acceptance criteria: recorded here and in README/model-limitations docs as
needed: `plat_enable_misaligned_access := false` matches Jolt's real platform
behavior because Jolt rejects rather than splits misaligned multi-byte accesses;
git shows this is the only semantic post-import patch to `LeanRV64D/`; and the
documentation does not claim Rust host execution produces the same trap object
as Sail.

Dependencies: none.

---

### W7 — TCB enumeration and axiom audit (BAD BASE)

**Status: closed as an issue; optional regression gate only. Effort: none in
the active plan.**

Goal: no active proof cleanup. The actual native-solver dependency issue has
already been removed.

Completed in June 2026:

- Removed all textual `native_decide` from `JoltBytecode/`.
- Replaced the public-theorem `bv_decide` SAT-path leaks with ordinary Lean
  proofs in the store/AMO splice facts, write-address decomposition facts, and
  ECALL `mstatus[41]` Zicfilp no-op fact.
- Verified by broad public-theorem scan after commit `64b9212`:
  `W7 targets=752`, `W7 native_dep_theorems=0`,
  `W7 native_axioms_unique=0`.
- Current raw source count is `0` `native_decide` and `60` `bv_decide` in
  `JoltBytecode/`. Those remaining `bv_decide` sites are not currently leaking
  generated native axioms into the scanned public theorem closures; they are a
  regression watchlist and declaration-level audit item.

Why not pursuing now: there is no remaining public-theorem native-axiom leak to
fix. Additional work would be process hardening, not a new proof issue. It is
reasonable to add a CI gate later, but it should not compete with W1/W2/W10.

Important recorded fact: `bv_decide` is *not*
  kernel-only. When `bv_normalize` closes the goal it adds no extra axioms
  (`[propext, Quot.sound]`), but when the SAT/LRAT path runs the proof depends
  on a generated `<decl>._native.bv_decide.ax_*` axiom — same trust class as
  `native_decide`, which itself appears in this toolchain as
  `<decl>._native.native_decide.ax_*` rather than bare `Lean.ofReduceBool`.

Optional future guard: check in an axiom-closure scan that fails if generated
`*._native.*` axioms re-enter public theorem closures.

Acceptance criteria: none for the active hardening plan.

Dependencies: none.

---

### W8 — Coverage completeness tied to the type (WEAK STATEMENT / process)

**Status: not pursuing as active soundness work; guard only. Effort: none in
the active plan.**

Goal: no active W8 workstream in the current cycle.

Rationale: W8 is a coverage/process guard, not evidence that any current theorem
is false, vacuous, or too weak. It should not be presented as a core soundness
issue. The real Rust/Lean coverage/conformance problem is W1: Lean definitions
must match what Rust emits. A source-opcode manifest can support W1, but it is
not an independent proof repair.

Not pursuing:

- A standalone Lean source-opcode universe just to mirror Rust.
- A separate coverage-completeness theorem before Rust/Lean conformance exists.
- Treating prose coverage drift as a current proof bug.

Where the useful part goes: W1's generated Rust manifest should include source
opcode identity and row metadata. Once that exists, coverage classification can
be a small CI check over the W1 artifact.

Acceptance criteria: none as W8.

Dependencies: W1 if revived as a guard.

---

### W9 — Spec hygiene (process)

**Status: not pursuing standalone; useful part folded into W2. Effort: none as
a separate workflow.**

Goal: no active W9 workstream.

Rationale: W9 is mostly housekeeping. Housekeeping is not the same as a trust
bug. The only part that matters for soundness is memory-envelope unification,
because `JoltConfig.mem_populated` is impossible and must be replaced by finite
footprint assumptions. That belongs directly under W2.

Not pursuing:

- Removing every dead helper or unused predicate as a standalone effort.
- Documentation cleanup disconnected from W1/W2/W10.
- A general spec-hygiene pass during the current proof cycle.

Where the useful part goes: W2 should introduce the finite memory-footprint
contract and update any stale memory-envelope docs as part of that change.

Acceptance criteria: none as W9.

Dependencies: W2 if revived as cleanup.

---

### W10 — Discharge proof-shaped system assumptions (ASSUMED CONCLUSION)

**Status: active / not repaired, new in June 2026 deep audit. Effort: L.
Highest system-family value.**

Goal: convert the system-family assumption bundles from "assume Sail and Jolt
agree" to "prove they agree from genuine environment invariants," so the
ECALL/MRET/CSRRW theorems claim what their names imply.

Rationale: the deep audit found 8 of ~30 fields across
`CsrrwSystemAssumptions` (`Csrrw.lean:335`), `EcallSystemAssumptions`
(`System/Common.lean:1683`), and `MretSystemAssumptions` (`Mret.lean:580`) are
*correspondence assumptions*: they hypothesize the very Sail↔Jolt equality the
theorem exists to establish. A comment at `Csrrw.lean:326` already records that
these are provisional and "should be discharged from concrete ZeroOS
invariants"; nothing tracks that debt today. This is distinct from vacuity (the
bundles are satisfiable) — the theorems are valid but under-claim.

The eight red-flag fields:

- `CsrrwSystemAssumptions.csr_read_matches`, `csr_write_matches` — assume Sail's
  `read_CSR`/`write_CSR` return exactly the raw Jolt vreg value, which assumes
  away Sail's CSR **legalization** (`legalize_mstatus` etc.), the one place a
  raw vreg and an architecturally-legalized CSR can differ.
- `EcallSystemAssumptions.mstatus_matches_zeroOS_trap`, `trap_vector_matches_jalr`
  — assume Sail's trap mstatus update is already idempotent and Sail's
  `tvec_addr` already equals the Jolt JALR target.
- `MretSystemAssumptions.mstatus_{mie_matches_mpie, mpie_one, mpp_machine,
  mpelp_zero}` — four fields that collectively make Sail's entire xret mstatus
  postlude a no-op (helper lemmas `mretMstatus_*_write_eq_self` exist only to
  prove the writes do nothing under these hypotheses). The current MRET theorem
  therefore proves the jump target and **nothing about mstatus handling**.

Note the ECALL↔MRET cycle (unknown 9): ECALL assumes mstatus is already in
trap-safe form, MRET assumes field values ECALL does not produce. Discharging
one constrains the other; resolve them together against the real ZeroOS
trap-entry/return path.

Tasks:

- For each red-flag field, decide: provable from genuine initial-state
  environment invariants (privilege, ZeroOS CSR whitelist, loader-set trap
  vector), or hiding a real Sail-vs-Jolt mismatch (legalization). The W2 witness
  construction is the forcing function: building a concrete witness for each
  bundle *requires proving* these fields for a concrete state, which immediately
  separates the dischargeable from the genuinely-assumed.
- Prove the CSR legalization lemmas for the ZeroOS-whitelisted CSRs (`mstatus`,
  `mtvec`, `mepc`, `mscratch`, `mcause`, `mtval`): Sail's read/write applied to a
  Jolt-written raw value returns the value Jolt expects (or document the exact
  legalized delta and fold it into the projection).
- Replace the idempotence assumptions with a proved environment contract for the
  initial mstatus / trap-vector vregs, shared between ECALL and MRET.

Acceptance criteria: each of the eight fields is either proved from a documented
environment invariant and removed from the bundle, or explicitly reclassified in
`LEAN_BYTECODE_MODEL_LIMITATIONS.md` as a named trusted ZeroOS contract with the
reason it cannot be discharged against the current Sail model. No correspondence
field silently remains in a public theorem's hypotheses.

Dependencies: pairs with W2. Witness construction surfaces these assumptions
without needing mutation testing as a separate workflow.

---

### W11 — Frame conditions and composition (NON-COMPOSITION)

**Status: later / conditional. Effort: L if trace-level composition becomes a
goal.**

Goal: make the per-instruction theorems chainable by proving each expansion
preserves what the next instruction assumes, and demonstrate one multi-row
composition.

Rationale: this is real, but only for a stronger claim than the current
per-instruction theorem surface. The deep audit found **no preservation or frame lemmas anywhere**.
Nothing proves a non-system expansion leaves the persistent CSR vregs
(v32–v39) untouched. Because `projectResult` discards all vregs
(`JoltISA/Core.lean:51`), an ALU/load/store expansion that clobbered
`mstatusVReg` would satisfy its own `*_eq_sail` theorem perfectly and silently
invalidate every later system-instruction assumption — an invisible bug class.
Sail memory is not part of this extra frame problem: it lives in the projected
Sail state, so `projectResult jres = sres` already exposes memory differences.
VReg disjointness is currently proven only for the one scratch register CSRRW
uses (`systemScratch_ne_systemCSR_vreg`, `Csrrw.lean:75`); v41–v47 have no such
facts. The per-instruction theorems are honest, but nothing licenses chaining
even two of them, so no trace-level claim is reachable from the current surface.

This subsumes and generalizes the W4 scratch-register concern: W4 documents the
intra-instruction scratch scope; W11 proves the inter-instruction frame.

Why not active now: current theorem names and proof statements are
per-instruction. W11 becomes necessary if we want to claim that two or more
proved instructions compose into a trace-level theorem. Until then, it should
not compete with W1/W2/W10.

Tasks:

- Per non-system family, strengthen the public theorem contract so executing
  the `xProgram` both matches the projected Sail result and leaves protected
  Jolt registers unchanged.
- Establish vreg disjointness for the full scratch pool (v40–v47) vs the
  persistent CSR vregs (v32–v39), not just the single CSRRW scratch register.
- Prove one concrete two-instruction composition theorem (e.g. an ALU op
  followed by a store, or any op followed by ECALL) as the acceptance test that
  the frame lemmas actually chain. A general n-instruction/trace theorem is a
  larger follow-on, explicitly out of scope for the first pass.

Acceptance criteria: strengthened public theorem contracts in the root build
for each non-system family; full scratch-vs-CSR vreg disjointness; one proved
two-instruction composition.

Dependencies: none for the protected-vreg frame. Future composition with memory
instructions may still rely on the W2 finite-memory assumptions already present
in those theorem statements.

## Sequencing

Dependency-ordered, optimized for the issues we now agree are real:

1. **W2 first.** Replace impossible `mem_populated` with finite memory
   footprints. This removes the clearest vacuity problem.
2. **W1 next or in parallel.** Rust/Lean drift is proven real by the AMO.D row
   mismatch. Start with expansion conformance; decode differential can run
   independently if cheap.
3. **W10 with/after W2.** Constructing system-bundle witnesses forces the
   proof-shaped CSR fields into the open. This is the real theorem-strength
   problem.
4. **W11 later, only if trace composition becomes a goal.** It is real for
   multi-instruction claims, but not required for the current per-instruction
   theorem surface.

Not in the active sequence: W3, W4, W5, W6, W7, W8, W9. Their useful pieces are
either done, deferred, or folded into W1/W2/W10/W11 as described above.

## Focused unknowns — resolutions (June 2026 deep audit)

The follow-up audit (June 11, 2026; both repos plus toolchain experiments) has
resolved or sharply narrowed all ten unknowns. Findings below supersede the
original questions; each item records the evidence and the action it implies.

1. **`JoltConfig.mem_populated` — RESOLVED and repaired for load/store/AMO.**
   Sail memory is `Std.ExtHashMap Nat (BitVec 8)` (lean-sail
   `Sail/Sail.lean:470`), a finite map; no concrete state can satisfy the old
   global predicate `∀ addr : Nat, s.mem.get? addr ≠ none`. The repair is now
   implemented for load/store/AMO public theorem boundaries: `JoltConfig`
   contains only Machine-mode / MPRV facts, `JoltBytecode.Assumptions` contains
   finite primitive memory windows, and family public bundles derive exact
   `Flat*` evidence internally. Ordinary ALU and ALUAdvice public theorem
   boundaries now expose only source-register read bundles. W2 remains open only
   for checked witness / co-satisfiability coverage of the surviving bundles,
   especially system/CSR bundles.
2. **AMO.D conformance target — RESOLVED: real drift; Lean now matches Rust.**
   Verified in source: `expand_amo_d`
   (`crates/jolt-program/src/expand/memory/shared.rs:182`) emits LD / op / SD /
   ADDI with no assert row (`expand_amoswapd`: LD/SD/ADDI,
   `expand/memory/amoswapd.rs:8`). Lean previously prepended a hallucinated
   doubleword virtual assert row. The fix is to remove that row from the Lean
   ISA/expansions and make the Lean `LD`/`SD` semantics expose the same
   alignment boundary the Rust tracer reaches through `load_doubleword` /
   `store_doubleword`. The AMO.D misaligned theorems now stop at the first
   emitted `LD` and still match Sail's store/AMO alignment exception.
   Secondary check for the first W1a manifest: the audit saw slightly different AMO.W
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
   serialization already exist, so a coverage manifest is easy to generate if
   W1 needs it. This is a W1 support artifact, not an active standalone W8
   soundness workflow. Compressed instructions are normalized before the enum
   (`uncompress.rs`), tracked by `is_compressed`.
   Known fixture gap to enumerate during W1a: the main expand fixtures cover 66
   unique opcodes vs 68 expanded kinds.
7. **`bv_decide` TCB — RESOLVED and repaired for public theorem closures.**
   Experiment on the pinned v4.29.0-rc4: kernel `decide` proves the real
   `native_decide` goals (e.g. `StoreFamily/ProgramBlocks.lean:196,201`) with
   axioms `[propext]`, and 180-constructor enum distinctness with *no* axioms,
   in negligible time. `bv_decide` adds no extra axiom only when `bv_normalize`
   closes the goal; when the SAT/LRAT path runs, the theorem depends on a
   generated `<decl>._native.bv_decide.ax_*` axiom, the same trust class as
   `native_decide` (which in this toolchain likewise appears as
   `<decl>._native.native_decide.ax_*`, not as bare `Lean.ofReduceBool`).
   Consequences: (i) replace `native_decide` with `decide`, not `bv_decide`;
   (ii) the axiom gate must flag `*._native.*` generated axioms, not only
   `Lean.ofReduceBool`; (iii) raw `bv_decide` source sites remain a
   declaration-level watchlist.

   Follow-up cleanup removed the actual public-theorem dependency issue:
   current source counts are `0` `native_decide` and `60` `bv_decide` in
   `JoltBytecode/`, while the broad public theorem scan reports
   `W7 targets=752`, `W7 native_dep_theorems=0`,
   `W7 native_axioms_unique=0`. This closes W7 as an active issue; an axiom gate
   is optional regression infrastructure.
8. **`LeanRV64D/` provenance — RESOLVED enough for this plan; W5 deferred.**
   Git-verified: imported in commit `c3bceb3` (2026-03-23, 154 files); exactly
   one post-import semantic edit, `b9bcdf5` (2026-04-18), flipping
   `PlatformConfig.lean:206` `true -> false` with a WARNING comment; nothing
   else. The broader generated-Sail provenance story is documented externally in
   the project blog, so reconstructing a local regeneration CI path is deferred
   and not part of the active hardening work.
9. **System/CSR joint satisfiability — STILL NEEDS ATTENTION.** The memory,
   ALU, and ALUAdvice theorem boundaries have been tightened, but the system
   bundles remain the open assumption-boundary work. Each bundle
   (`EcallSystemAssumptions`, `System/Common.lean:1683`;
   `CsrrwSystemAssumptions`, `Csrrw.lean:335`; `MretSystemAssumptions`,
   `Mret.lean:580`) appears individually satisfiable — W2 should construct the
   witnesses. But ECALL leaves the mstatus vreg at
   `zeroOSMstatus = 0x1800` (MPIE=0, MIE=0; `Common.lean:36`), while MRET
   assumes `MPIE = 1` and `MIE = MPIE` (`Mret.lean:563–567`) precisely so that
   Sail's xret mstatus update is a no-op. The modeled ECALL → handler → MRET
   round trip is therefore *not* covered by composing the two theorems unless
   the handler rewrites mstatus (e.g. CSRRW) in between. Action: check what
   ZeroOS actually executes between trap entry and `mret`; either document the
   required intermediate mstatus write as part of the environment contract, or
   rework the MRET assumptions / Jolt mstatus modeling. Relatedly, ECALL's
   `trap_vector_matches_jalr` and `trap_target_fetch_aligned` are loader-time
   environment invariants and belong in the W10/W2 system-contract repair.
10. **Scratch-register invariants — RESOLVED: no global work needed.** No
    public theorem exposes vregs: `projectResult` (`JoltISA/Core.lean:51`)
    discards all vregs; `systemProjectResult` (`System/Common.lean:78`)
    overlays only the persistent CSR vregs; `EbreakResultRelation`
    (`Ebreak.lean:165`) is intentionally a relation. Cross-row temporaries
    (ECALL scratch, CSRRW `rd = rs1` save/restore, DIV `t0–t4` phases,
    load/store address temps) are already discharged inside existing
    phase/block proofs. No standalone W4 work remains; the real projection issue
    is W10, and trace-level preservation is W11 if needed later.

## Deep audit of the Lean formalization itself (June 11, 2026)

A second pass looked *inside* the Lean development, assuming the Rust bridges and
the ten unknowns above are resolved. It asked where a fully-checked proof tree
could still under-deliver. Recorded so a future audit does not re-investigate
the parts that checked out.

**Checked out clean (do not re-audit without cause):**

- **Advice is quantified soundly.** All 8 DIV/REM variants have both a soundness
  theorem universally quantified over advice (`divProgram_sound` etc.: any
  `q, rem` that let the guarded program succeed are pinned to the Sail values via
  `advice_unique_of_guards`, `Div_math.lean:1145`) and an honest-advice
  completeness theorem (`*_eq_sail`). The assert rows genuinely gate execution
  with `Error.Assertion`. The malicious-prover direction is covered for DIV/REM;
  the only advice family with no closed theorem is LR/SC, already deferred.
- **Branch totality is explicit.** Stores, loads, and AMOs have dispatcher
  theorems that `by_cases` on exact-negation alignment predicates
  (`swProgram_eq_sail`, `Sw_main.lean:430`; loads and AMO word/dword similarly),
  so no input region falls between the aligned/misaligned branches. CSRRW's
  three-way split (rd=x0 / rd=rs1 / general) is exhaustive but only implicitly
  via its `if/else`; a one-line cover lemma would make it auditable (no actual
  gap).
- **Mechanical conventions are sound.** x0 writes are proven discarded at the
  Sail level (`wX_bits_regidx_zero`, `RegisterOps.lean:103`); `cycleCount` and
  `choiceState` are inert (`trivialChoiceSource`, `α = Unit` — no hidden
  nondeterminism); address wraparound is excluded by explicit `h_no_ovf`
  hypotheses, not silently divergent.

**Concerns retained after triage:**

1. **Proof-shaped system assumptions → W10.** See the dedicated workstream; the
   single largest hole in what is *proven* today.
2. **No frame/composition layer → W11 later.** Real only for trace-level or
   multi-instruction claims; not active per-instruction proof repair.
3. **Decode and the step loop are outside every check → W1d + T10.** Verified
   directly: `JoltBytecode/` never references `LeanRV64D/Step.lean`
   (`dispatchInterrupt`, fetch, `encdec`, `tick_pc`). The post-decode
   `execute_*` scope is defensible but must be *stated*; decode agreement is
   differentially testable (W1d) and the rest is a documented boundary.
4. **TCB additions → T8/T9/T10.** The lean-sail runtime, jolt-qed's own memory
   functions, and the decode/step boundary are now ledger entries.

Explicitly not retained as active concerns: W3 mutation testing, W4 generic
projection documentation, W5 provenance reconstruction, W6 misaligned flag, W7
native-solver cleanup, W8 coverage manifest, and W9 general hygiene. See the
triage table and individual sections for why.

**Fault-row ordering (watch item, no workstream yet).** Error results compare
post-fault state with no rollback (`projectResult`, `Core.lean:55`), which is
only obviously correct because every current expansion places its assert rows
*first*. If W1c ever generates a program with an assert *after* an architectural
write, the error-branch comparison semantics become subtle. Add a one-line
conformance check ("assert rows precede state-modifying rows") when W1c lands, or
prove it structurally.

## Definition of "more trustworthy" (exit criteria)

The effort has materially improved trust when:

- no equivalence theorem can be vacuous (W2);
- Lean and Rust expansions are continuously cross-checked, ideally generated
  from one source (W1), and decode agreement is differentially tested (W1d);
- no public theorem hypothesizes the Sail↔Jolt correspondence it claims to
  prove; system-family assumptions are discharged or named as explicit trusted
  contracts (W10);
- if we later claim trace-level composition, expansions provably preserve the
  invariants the next instruction needs and at least one multi-instruction
  composition is proved (W11).

## Cross-references

- `planning/roadmap.md` — coverage and scope status.
- `planning/LEAN_BYTECODE_MODEL_LIMITATIONS.md` — current scope risks and the
  ordinary-memory-envelope cleanup folded into W2.
- `planning/JOLT_EXPANSION_DSL_DESIGN.md` — input to W1c.
- `planning/JOLT_SPECIAL_MEMORY_REGION_PLAN.md`,
  `planning/JOLT_TRACE_METADATA_PLAN.md` — out-of-scope boundaries this plan
  does not touch.
- `README.md` — theorem shape, coverage table, the misaligned-access edit (T4).
