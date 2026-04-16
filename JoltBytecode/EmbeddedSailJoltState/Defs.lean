import LeanRV64D

/-!
# Embedded Architecture: SailJoltState embeds SailState

Instead of duplicating SailState's fields, SailJoltState embeds it directly.
This makes project/inject trivial (field access/update) and may eliminate
the monadic plumbing noise in proofs.
-/

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

-- ============================================================================
-- Types
-- ============================================================================

abbrev SailState := SequentialState RegisterType trivialChoiceSource

-- SailJoltState embeds SailState directly instead of duplicating fields.
structure SailJoltState where
  sail : SailState
  vregs : BitVec 7 → BitVec 64 := fun _ => 0

@[ext]
theorem SailJoltState.ext
    {js₁ js₂ : SailJoltState}
    (hsail : js₁.sail = js₂.sail)
    (hvregs : js₁.vregs = js₂.vregs) :
    js₁ = js₂ := by
  cases js₁
  cases js₂
  cases hsail
  cases hvregs
  rfl

-- Note that SailM whiach is the Monad the transpilation exposes 
-- is just SailM (a: Type) := EStateM (Error exception) SailState α
abbrev JoltMonad (α : Type) := EStateM (Error exception) SailJoltState α

-- ============================================================================
-- Projection: trivial field access/update
-- ============================================================================

-- project: just read the embedded SailState.
@[simp] def project (js : SailJoltState) : SailState := js.sail

-- inject: replace the embedded SailState, keeping vregs unchanged.
@[simp] def inject (js : SailJoltState) (ss : SailState) : SailJoltState :=
  { js with sail := ss }

-- projectResult: strip vregs from an EStateM result.
-- Once you a run the EStateM type i.e. call the step function it models
-- the output is Result .ok α σ' or Result .error e σ' 
-- σ' is the updated Jolt State
-- we project this down to SailState while keeping the error and return value the same.
def projectResult (r : EStateM.Result (Error exception) SailJoltState α) :
    EStateM.Result (Error exception) SailState α :=
  match r with
  | .ok a js' => .ok a (project js')
  | .error e js' => .error e (project js')

-- ============================================================================
-- liftSail
-- ============================================================================
-- Run Sail computation given by m as a JoltComputation
def liftSail (m : SailM α) : JoltMonad α := fun js =>
  match m js.sail with
  | .ok a ss' => .ok a { js with sail := ss' }
  | .error e ss' => .error e { js with sail := ss' }

-- ============================================================================
-- Structural lemmas
-- ============================================================================
-- Running sail computaiton ss as Joltcomputation and immediately projecting the state 
-- is the same thing as as running the sail computation on SailM monad.
@[simp] theorem project_inject (js : SailJoltState) (ss : SailState) :
    project (inject js ss) = ss := rfl

-- inject overwrites the sail field, so a second inject discards the first (set-then-set = set).
@[simp] theorem inject_inject (js : SailJoltState) (ss1 ss2 : SailState) :
    inject (inject js ss1) ss2 = inject js ss2 := rfl

@[simp] theorem inject_project (js : SailJoltState) :
    inject js (project js) = js := by 
    unfold inject project 
    rfl
    

theorem liftSail_project (m : SailM α) (js : SailJoltState) :
    projectResult ((liftSail m).run js) = m.run js.sail := by
  simp only [liftSail, projectResult, project, EStateM.run]
  cases m js.sail <;> rfl

-- liftSail preserves bind.
theorem liftSail_bind (m : SailM α) (f : α → SailM β) :
    liftSail (m >>= f) = (do let a ← liftSail m; liftSail (f a) : JoltMonad β) := by
  funext js
  simp only [liftSail, bind, EStateM.bind]
  cases m js.sail with
  | ok a ss' => rfl
  | error e ss' => rfl

-- liftSail preserves pure.
theorem liftSail_pure (a : α) :
    liftSail (pure a) = (pure a : JoltMonad α) := by
  funext js
  simp only [liftSail, pure, EStateM.pure]

-- ============================================================================
-- Virtual register operations
-- ============================================================================
def readVReg (vr : BitVec 7) : JoltMonad (BitVec 64) := do
  let js ← get; pure (js.vregs vr)

def writeVReg (vr : BitVec 7) (val : BitVec 64) : JoltMonad Unit :=
  modify fun js => { js with vregs := fun r => if r = vr then val else js.vregs r }

@[simp] theorem readVReg_run (vr : BitVec 7) (js : SailJoltState) :
    readVReg vr js = .ok (js.vregs vr) js := by
  unfold readVReg get
  rfl

-- ============================================================================
-- Memory read primitives (raw Sail memory access)
-- ============================================================================

-- Read a single byte from Sail's physical memory.
-- At the bottom of Sail's memory hierarchy, readByte looks up addr in
-- state.mem (an ExtHashMap Nat (BitVec 8)). This is the same operation.
def sailReadByte (addr : Nat) : SailM (BitVec 8) := fun s =>
  match s.mem.get? addr with
  | some v => .ok v s
  | none => .error (Error.OutOfMemoryRange addr) s

-- Read 4 bytes (little-endian) from Sail's memory, producing a 32-bit word.
def sailReadWord (addr : BitVec 64) : SailM (BitVec 32) := do
  let b0 ← sailReadByte addr.toNat
  let b1 ← sailReadByte (addr.toNat + 1)
  let b2 ← sailReadByte (addr.toNat + 2)
  let b3 ← sailReadByte (addr.toNat + 3)
  pure (b3 ++ b2 ++ b1 ++ b0)

-- Read 8 bytes (little-endian) from Sail's memory, producing a 64-bit dword.
def sailReadDword (addr : BitVec 64) : SailM (BitVec 64) := do
  let lo ← sailReadWord addr
  let hi ← sailReadWord (addr + 4)
  pure ((hi ++ lo : BitVec 64))

-- ============================================================================
-- JoltConfig: Sail state assumptions for Jolt's execution environment
-- ============================================================================

-- Jolt runs in bare-metal M-mode with flat physical memory. Under these
-- assumptions, Sail's virtual memory pipeline (vmem_read) reduces to raw
-- byte reads from state.mem.
--
-- The conditions are:
-- 1. Machine mode with MPRV=0: translateAddr returns identity (Bare mode)
-- 2. PMP entries are unlocked: Machine mode bypasses PMP
-- 3. Valid PMA region: the physical address has readable attributes
-- 4. Not MMIO: the address is regular RAM, not memory-mapped I/O
-- 5. Memory is populated: all accessed addresses are in state.mem
--
-- These are captured as a predicate on SailState rather than baking in
-- specific register values, so the proofs stay abstract.
structure JoltConfig (s : SailState) : Prop where
  -- Machine mode: cur_privilege register is Machine.
  -- This makes translateAddr use Bare (identity) translation.
  machine_mode : s.regs.get? Register.cur_privilege =
    some (Privilege.Machine : RegisterType Register.cur_privilege)
  -- mstatus register is readable and has MPRV=0.
  -- MPRV=0 means effectivePrivilege returns the actual privilege (Machine),
  -- not the MPP field. This ensures Bare translation mode.
  mstatus_ok : ∃ mval : RegisterType Register.mstatus,
    s.regs.get? Register.mstatus = some mval ∧
    _get_Mstatus_MPRV mval = 0#1
  -- All memory addresses are populated in state.mem.
  -- This makes sailReadByte succeed for any address.
  mem_populated : ∀ addr : Nat, s.mem.get? addr ≠ none

-- ============================================================================
-- Focused bridge lemmas for the vmem_read pipeline
-- ============================================================================

/- STALE:
These two older load-factoring bridge lemmas are not referenced anywhere in the
current instruction-equivalence development. The active load proofs use the
newer local lemmas in `InstructionEquivalence/LoadDefUtils.lean` and the
instruction-specific files instead.

Keeping the old sorried declarations here only pollutes the build status, so
they are commented out until there is a reason to revive them.

theorem translateAddr_machine_bare ...
theorem execute_LOAD_LW_factored ...
-/

-- ============================================================================
-- Shared Jolt instructions
-- ============================================================================

def jolt_virtual_sign_extend_word (rd : regidx) : JoltMonad Unit := do
  let v ← liftSail (rX_bits rd)
  liftSail (wX_bits rd (sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0)))

-- ============================================================================
-- sail_cases tactic
-- ============================================================================

syntax "sail_cases" term : tactic
macro_rules
  | `(tactic| sail_cases $t:term) => `(tactic|
      (generalize $t = _sc; cases _sc <;> simp))

end
