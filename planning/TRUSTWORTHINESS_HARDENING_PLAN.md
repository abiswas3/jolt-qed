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
| T2 | `Lean.ofReduceBool` via `native_decide` | reducible | compiler + `Decidable` eval; ~100 sites, heaviest in `System/`. Target for reduction (W7) |
| T3 | `LeanRV64D/` Sail-generated RISC-V semantics | reference spec | trusted by design, but must be provably the genuine upstream output (W5) |
| T4 | `plat_enable_misaligned_access := false` edit to T3 | base edit | a real semantic narrowing; isolate or eliminate (W5, W6) |
| T5 | Faithfulness of `execInstr` to Rust per-row `cpu_exec` semantics | unproven | drift risk (W1) |
| T6 | Faithfulness of `xProgram` definitions to Rust `inline_sequence` emission | unproven | drift risk; cheapest to check because `Program` is first-order data (W1) |
| T7 | Toolchain mismatch: `v4.29.0-rc4` vs lean-sail's target nightly | environment | documented in `README.md`; keep pinned and reproducible (W5) |

## Workstreams

Status legend: **not-started** / **in-progress** / **done** / **blocked**.
Effort is in agent-runtime terms. The binding constraint everywhere is the Lean
rebuild/recheck cycle, not authoring; size estimates assume that bottleneck.

---

### W1 — Rust to Lean conformance (DRIFT)

**Status: not-started. Priority: highest value. Effort: L.**

Goal: detect and prevent divergence between the Lean specification and the Rust
implementation it claims to model. This closes the gap behind T5 and T6, which
together carry most of the residual risk.

Rationale: every proof below T5/T6 is conditional on a transcription no machine
checks. Because `JoltISA.Program` is a concrete inductive (a list of `Instr`),
the expansion half (T6) can be checked structurally without extraction or a Rust
verifier. This is unusually high leverage.

#### W1a — Bytecode structural conformance harness

- Emit Rust's `inline_sequence` output (the final `Vec` of trace-row
  instructions) for every covered opcode across a structured/random sweep of
  operands.
- Serialize to a stable format (JSON manifest).
- Compare row-for-row against the corresponding Lean `xProgram`
  (`JoltISA/Expansions/*.lean`), including the `pureWritebackTraceProgram`
  `rd = x0` branch.
- Run in CI; fail on any structural mismatch.

Acceptance criteria: a CI job that, for each opcode in the coverage table,
asserts `RustEmitted(opcode, operands) == LeanProgram(opcode, operands)` as
data, for a documented operand sample including `rd = x0` and boundary shifts.

#### W1b — Value-primitive differential fuzzing

- The pure value functions (`jolt_virtual_pow2_value`, `change_divisor_value`,
  `jolt_mulhu_value`, `jolt_virtual_srl_value`, ...) encode Jolt's
  lookup-table/constraint semantics.
- Cross-check each against its Rust implementation on randomized inputs through
  the same harness.

Acceptance criteria: a fuzz target per primitive with a documented input
distribution and iteration count, green in CI.

#### W1c — Single source of truth for expansions (durable fix)

- Generate both the Rust `inline_sequence` and the Lean `Program` definitions
  from one declarative table/DSL, so drift becomes structurally impossible
  rather than tested-against.
- See `planning/JOLT_EXPANSION_DSL_DESIGN.md`; promote it from design note to
  artifact.

Acceptance criteria: at least one instruction family whose Lean `xProgram` and
Rust `inline_sequence` are both generated from a shared spec, with W1a passing
trivially for that family.

Dependencies: W1a/W1b are independent and should land first as the interim
safety net. W1c is the long-term replacement.

---

### W2 — Anti-vacuity: inhabitance witnesses (VACUITY)

**Status: not-started. Effort: S. Recommended first.**

Goal: prove every assumption bundle is satisfiable, so no family's theorems are
vacuously true.

Rationale: a proof under contradictory hypotheses is indistinguishable from a
real one. There is currently no inhabitance check anywhere in `JoltBytecode/`.

Tasks:

- For each predicate/structure used as a theorem hypothesis (`JoltConfig` in
  `JoltISA/Environment.lean`, `EcallSystemAssumptions` in
  `System/Common.lean`, `StoreFamily.StoreMemoryAssumptions`,
  `AtomicFamily.AmoMemoryAssumptions`, `FlatPhysMem`, `FlatLoadStoreMem`,
  `FlatAtomicMem`, the CSR access/legalizer assumptions), construct a concrete
  witness as a checked `example`.
- Prefer a single realistic `initialJoltState` builder from which the bundles
  are *jointly* derivable, so co-satisfiability (not just per-predicate
  satisfiability) is demonstrated.

Acceptance criteria: a file (for example
`JoltBytecode/InstructionEquivalence/AssumptionsAreSatisfiable.lean`) containing
a witness `example` for every hypothesis bundle, in the root build.

Dependencies: none.

---

### W3 — Statement-strength validation: mutation testing (WEAK STATEMENT)

**Status: not-started. Effort: M. Highest insight.**

Goal: empirically confirm each equivalence theorem actually constrains what we
think it does.

Rationale: the most direct answer to "could the spec be wrong and the proof
still pass." If a deliberately corrupted `xProgram` still satisfies its
`*_eq_sail` theorem, the statement is too weak.

Tasks:

- Build a harness that injects a catalogue of mutations into each `xProgram`
  (swap two operands, drop a sign-extend row, change an immediate, flip a
  scratch register) and confirms the build *breaks*.
- A mutation that leaves the build green is a finding: the theorem is too weak
  or the mutation is semantically inert (document which).
- Run as an offline/nightly job, not on the critical path.

Acceptance criteria: a documented mutation catalogue with a report of
kill rate per instruction family, and a triage note for any surviving mutant.

Dependencies: none, but most informative once W2 rules out vacuity (a vacuous
theorem trivially "survives" all mutations).

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
  prove write-before-read within the program.
- Prove a lemma relating `systemProject` to `project` off the CSR keys, and
  record why `systemProjectResult` is the faithful projection for ECALL/MRET/CSR
  (Jolt holds CSRs in persistent virtual registers).
- Record the explicit argument for `EbreakResultRelation` being intentionally a
  relation, not equality (constructor mismatch is by design).
- Confirm no theorem asserts only the written register and leaves the rest of
  the state existentially loose; the `stateAfterWrite`-based `_concrete` lemmas
  already capture full frame, so this is an audit, not a rewrite.

Acceptance criteria: a short `Projections.md` (or module docstring) justifying
each projection, plus the scratch-register and CSR-off-key lemmas in the build.

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

- Pin the exact sail-riscv commit and lean-sail version that generated
  `LeanRV64D/`, with a reproducible regeneration script.
- Add CI that regenerates `LeanRV64D/` and diffs against the checked-in tree,
  allowing exactly one reviewed patch: `plat_enable_misaligned_access := false`
  (expressed as a standalone patch file).
- Document T7 (toolchain mismatch) as an explicit accepted risk with the reason
  it is believed benign.

Acceptance criteria: a green CI job proving the checked-in `LeanRV64D/` equals
upstream-generated output plus a single named patch.

Dependencies: none. Enables W6.

---

### W6 — Eliminate the misaligned-flag edit via reachability (BAD BASE)

**Status: not-started. Effort: M. Optional but removes a trusted delta.**

Goal: remove T4 entirely by proving it is irrelevant on the modeled subset.

Rationale: Jolt's inline memory sequences emit leading alignment-assert rows
(`VirtualAssertWordAlignment`, etc.). If those asserts dominate, the misaligned
Sail path is never reached, and the value of `plat_enable_misaligned_access`
does not affect the proved equivalence. Proving this lets us drop the base edit.

Tasks:

- Show that for each memory expansion, a misaligned effective address makes the
  alignment-assert row return a `Memory_Exception` before any `vmem_*` call.
- Show the comparison holds for both flag settings on the reachable subset, or
  that the misaligned branch is unreachable given the asserts.

Acceptance criteria: either the equivalence theorems no longer depend on the
flag value, or a documented argument for why the edit is still required.

Dependencies: W5 (so the base is locked before reasoning about its edits).

---

### W7 — TCB enumeration and axiom audit (BAD BASE)

**Status: not-started. Effort: S. Recommended first, pairs with W2.**

Goal: make the trusted base enumerable and CI-checked, and shrink the
`native_decide` surface.

Tasks:

- Add `#print axioms` for every public `*_eq_sail` / `*_rel_sail` theorem and
  assert the axiom set is exactly the expected one. This simultaneously catches
  accidental `sorry`, new `axiom`s, and `native_decide` (`Lean.ofReduceBool`)
  leaking into theorems where it was not intended.
- Inventory all `native_decide` sites (heaviest in `System/Common.lean`,
  `System/Mret.lean`, `System/Csrrw.lean`, `StoreFamily/ProgramBlocks.lean`).
  Convert register-key distinctness and similar facts to `decide` or structural
  lemmas where feasible; isolate the irreducible remainder so the trust surface
  is small and listed.

Acceptance criteria: a CI gate asserting the per-theorem axiom set, and a
documented, minimized inventory of remaining `native_decide` uses with
justification.

Dependencies: none.

---

### W8 — Coverage completeness tied to the type (WEAK STATEMENT / process)

**Status: not-started. Effort: S.**

Goal: prevent a Jolt source instruction from being silently uncovered.

Rationale: the coverage table in `README.md` and `roadmap.md` is prose. A newly
added instruction can drift out of the table without notice.

Tasks:

- Bind the coverage status to the actual source-opcode set: every opcode maps to
  exactly one of `{proved, proved-under-assumptions, advice, deferred,
  out-of-scope}`, mechanically (an exhaustiveness check or a checked table).

Acceptance criteria: a build-time or CI check that fails if a source opcode has
no classification.

Dependencies: none.

---

### W9 — Spec hygiene (process)

**Status: not-started. Effort: S.**

Goal: remove dead and duplicated specification that misleads auditors.

Tasks:

- `WellFormed` (`InstructionEquivalence/ProofSupport.lean:22`) is defined and
  unused. Remove it or wire it into the statements that need it.
- Centralize the ordinary Sail-memory access predicate (already flagged in
  `LEAN_BYTECODE_MODEL_LIMITATIONS.md` item 1) so load/store/AMO theorems share
  one named envelope instead of family-local restatements.

Acceptance criteria: no dead hypothesis predicates; a single shared
ordinary-memory predicate used across memory families.

Dependencies: coordinate with the memory-envelope cleanup in
`LEAN_BYTECODE_MODEL_LIMITATIONS.md`.

## Sequencing

Dependency-ordered, optimized for early certainty per unit of agent runtime:

1. **W2 + W7** first. Small, mechanical, immediately CI-enforceable, and
   together they close the two cheapest ways the current proofs could be
   silently worthless (vacuity and an unaudited TCB).
2. **W3** next. Mutation testing gives the highest insight into statement
   strength, and is most meaningful once W2 has excluded vacuity.
3. **W4** and **W9** in parallel with the above; they are localized audits plus
   small lemmas.
4. **W5**, then **W6**. Lock the base before reasoning about its single edit.
5. **W1** is the highest-value but largest investment. W1a/W1b (the differential
   harnesses) are the interim safety net; W1c (shared DSL) is the durable fix.
6. **W8** any time; it is process hygiene.

## Definition of "more trustworthy" (exit criteria)

The effort has materially improved trust when:

- no equivalence theorem can be vacuous (W2);
- the TCB is a short, CI-asserted, documented list (W7), with `native_decide`
  minimized;
- a deliberate corruption of any `xProgram` provably breaks its theorem (W3);
- each projection has a written faithfulness justification and the scratch-state
  scope is explicit (W4);
- the trusted Sail base is provably genuine upstream plus one named patch (W5),
  ideally with that patch shown irrelevant (W6);
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
