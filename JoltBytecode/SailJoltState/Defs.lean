import LeanRV64D

/-!
# Jolt ↔ Sail State Definitions and Projection

This file defines the core types and operations for bridging Jolt's
extended state (with virtual registers) and Sail's RISC-V state.

- SailJoltState: Sail's SequentialState plus virtual registers (vregs)
- project: strip vregs from a JoltState to get a SailState
- inject: put Sail fields back into a JoltState, keeping vregs
- liftSail: run a Sail computation inside JoltMonad
- projectResult: strip vregs from a JoltMonad result

The structural lemmas (project_inject, inject_inject, liftSail_project)
establish that project/inject are a retraction pair and that liftSail
preserves the Sail computation's result after projection.
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

-- SailState is Sail's sequential state for RISC-V, parameterized by
-- the concrete register types and a trivial choice source.
abbrev SailState := SequentialState RegisterType trivialChoiceSource

-- SailJoltState extends SailState with virtual registers (vregs).
-- The first 32 RISC-V registers live in `regs` (shared with Sail).
-- Virtual registers are Jolt-specific and invisible to Sail.
structure SailJoltState where
  regs        : Std.ExtDHashMap Register RegisterType
  choiceState : Unit
  mem         : Std.ExtHashMap Nat (BitVec 8)
  tags        : Unit
  cycleCount  : Nat
  sailOutput  : Array String
  vregs       : BitVec 7 → BitVec 64 := fun _ => 0

-- JoltMonad is EStateM over SailJoltState — a stateful computation
-- that can read/write the extended Jolt state and throw errors.
abbrev JoltMonad (α : Type) := EStateM (Error exception) SailJoltState α

-- ============================================================================
-- Projection: converting between JoltState and SailState
-- ============================================================================

-- project strips vregs from a JoltState, yielding a pure SailState.
def project (js : SailJoltState) : SailState where
  regs := js.regs
  choiceState := js.choiceState
  mem := js.mem
  tags := js.tags
  cycleCount := js.cycleCount
  sailOutput := js.sailOutput

-- inject writes Sail fields back into a JoltState, preserving vregs.
-- This is the inverse direction: after running Sail code, put the
-- updated Sail state back into the JoltState while keeping vregs intact.
def inject (js : SailJoltState) (ss : SailState) : SailJoltState :=
  { js with regs := ss.regs, choiceState := ss.choiceState,
            mem := ss.mem, tags := ss.tags,
            cycleCount := ss.cycleCount, sailOutput := ss.sailOutput }

-- projectResult strips vregs from the state inside an EStateM.Result.
-- Used to compare a Jolt computation's result with a Sail computation's result.
def projectResult (r : EStateM.Result (Error exception) SailJoltState α) :
    EStateM.Result (Error exception) SailState α :=
  match r with
  | .ok a js' => .ok a (project js')
  | .error e js' => .error e (project js')

-- ============================================================================
-- liftSail: running Sail computations inside JoltMonad
-- ============================================================================

-- liftSail takes a Sail computation and runs it inside JoltMonad.
-- It strips vregs (via project), runs the Sail code, then restores
-- vregs (via inject). Since Sail code never touches vregs, the
-- vregs pass through unchanged.
def liftSail (m : SailM α) : JoltMonad α := fun js =>
  match m (project js) with
  | .ok a ss' => .ok a (inject js ss')
  | .error e ss' => .error e (inject js ss')

-- Running a lifted Sail computation and projecting the result is the
-- same as running the Sail computation directly on the projected state.
-- This is the fundamental correctness property of liftSail.
theorem liftSail_project (m : SailM α) (js : SailJoltState) :
    projectResult ((liftSail m).run js) = m.run (project js) := by
  simp only [liftSail, projectResult, project, inject, EStateM.run]
  cases m ⟨js.regs, js.choiceState, js.mem, js.tags, js.cycleCount, js.sailOutput⟩ <;> simp_all

-- ============================================================================
-- Structural lemmas about project/inject
-- ============================================================================

-- Projecting after injecting gives back the original Sail state.
-- inject puts Sail fields into a JoltState; project reads them back out.
-- The vregs that inject preserved are stripped by project.
@[simp] theorem project_inject (js : SailJoltState) (ss : SailState) :
    project (inject js ss) = ss := by cases ss; rfl

-- Injecting twice: only the last Sail state matters.
-- The first inject's Sail fields are overwritten by the second.
-- vregs come from js in both cases.
@[simp] theorem inject_inject (js : SailJoltState) (ss1 ss2 : SailState) :
    inject (inject js ss1) ss2 = inject js ss2 := by rfl

end
