import JoltBytecode.JoltISA.Core

/-!
# Shim laws for the Jolt ISA core state

Equation and algebraic laws for the `SailJoltState` / `JoltMonad` embedding
defined in `JoltBytecode/JoltISA/Core.lean`.  The definitions stay in the ISA
layer; these `@[ext]` / `@[simp]` / monad-law theorems are proof support.
-/

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

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
