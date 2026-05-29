import LeanRV64D

/-!
# Jolt ISA core state

This module defines the Jolt CPU in lean. 
The semantics will then run instructions on this CPU.
-/

set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

abbrev SailState := SequentialState RegisterType trivialChoiceSource

structure SailJoltState where
  sail : SailState
  vregs : BitVec 7 → BitVec 64 := fun _ => 0

/-- Two `SailJoltState`s are equal when both their embedded Sail state and
virtual-register file are equal.  This is the extensionality principle used
when proofs need to compare whole Jolt states. -/
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

abbrev JoltMonad (α : Type) := EStateM (Error exception) SailJoltState α

-- TODO: I thought structures had natural projects (so do we need this ?)
@[simp] def project (js : SailJoltState) : SailState := js.sail

-- Replace current Sail state with new Sail State
@[simp] def inject (js : SailJoltState) (ss : SailState) : SailJoltState :=
  { js with sail := ss }

-- Given the output of a step of a Jolt CPU, return the same output as Sail CPU 
-- by projecting the JoltState down to Sail State
def projectResult (r : EStateM.Result (Error exception) SailJoltState α) :
    EStateM.Result (Error exception) SailState α :=
  match r with
  | .ok a js' => .ok a (project js')
  | .error e js' => .error e (project js')

-- Have some purely Sail computation i.e computation that a RISC CPU can hanle
-- but we wish to run it as a Jolt CPU computation by running the sail field of 
-- the joltstate which is just a RISC CPU
def liftSail (m : SailM α) : JoltMonad α := fun js =>
  match m js.sail with
  | .ok a ss' => .ok a { js with sail := ss' }
  | .error e ss' => .error e { js with sail := ss' }

/-- Projecting after injecting a Sail state returns the Sail state just
injected. -/
@[simp] theorem project_inject (js : SailJoltState) (ss : SailState) :
    project (inject js ss) = ss := rfl

/-- Injecting two Sail states in sequence keeps only the second one. -/
@[simp] theorem inject_inject (js : SailJoltState) (ss1 ss2 : SailState) :
    inject (inject js ss1) ss2 = inject js ss2 := rfl

/-- Injecting the Sail state already contained in a Jolt state leaves the Jolt
state unchanged. -/
@[simp] theorem inject_project (js : SailJoltState) :
    inject js (project js) = js := by
  unfold inject project
  rfl

/-- Running a lifted Sail computation and projecting its result agrees with
running the original Sail computation directly. -/
theorem liftSail_project (m : SailM α) (js : SailJoltState) :
    projectResult ((liftSail m).run js) = m.run js.sail := by
  simp only [liftSail, projectResult, project, EStateM.run]
  cases m js.sail <;> rfl

/-- Lifting a Sail bind into the Jolt monad is the same as binding the lifted
computation and then lifting the continuation. -/
theorem liftSail_bind (m : SailM α) (f : α → SailM β) :
    liftSail (m >>= f) = (do let a ← liftSail m; liftSail (f a) : JoltMonad β) := by
  funext js
  simp only [liftSail, bind, EStateM.bind]
  cases m js.sail <;> rfl

/-- Lifting a pure Sail value into the Jolt monad is just the pure Jolt value. -/
theorem liftSail_pure (a : α) :
    liftSail (pure a) = (pure a : JoltMonad α) := by
  funext js
  simp only [liftSail, pure, EStateM.pure]

end
