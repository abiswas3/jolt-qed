namespace Blog

structure State where
  x : Nat
  y : Nat
  deriving Repr

inductive Err where
  | assertFailed : String → Err
  deriving Repr

abbrev M (α : Type) : Type := EStateM Err State α

def doubleX : M Nat := do
  let s ← get
  let new := 2 * s.x
  set { s with x := new }
  pure new

def divYbyX : M Nat := do
  let s ← get
  if s.x = 0 then throw (Err.assertFailed "division by zero")
  else pure (s.y / s.x)

def prog1 : M Nat := do
  let _ ← doubleX
  let _ ← doubleX
  let _ ← doubleX
  divYbyX

#eval prog1.run { x := 5, y := 320 }
#eval prog1.run { x := 0, y := 320 }

theorem doubleX_run (s : State) :
    doubleX.run s = .ok (2 * s.x) { s with x := 2 * s.x } := rfl

theorem divYbyX_run_ok (s : State) (h : s.x ≠ 0) :
    divYbyX.run s = .ok (s.y / s.x) s := by
  unfold divYbyX
  simp only [EStateM.run_bind, EStateM.run_get]
  rw [if_neg h]
  rfl 

theorem divYbyX_run_err (s : State) (h : s.x = 0) :
    divYbyX.run s = .error (Err.assertFailed "division by zero") s := by
  unfold divYbyX
  simp only [EStateM.run_bind, EStateM.run_get]
  rw [if_pos h]
  rfl 

theorem divYbyX_run  (s: State):
    divYbyX.run s = 
    if s.x = 0 then .error (Err.assertFailed "division by zero") s 
    else .ok (s.y/ s.x) s := by 
  by_cases h : s.x = 0
  · rw [if_pos h] 
    exact divYbyX_run_err _ h 
  · rw [if_neg h] 
    exact divYbyX_run_ok s h  

theorem bind_run_of_ok {α β : Type} {m : M α} {f : α → M β}
    {s s₁ : State} {a : α}
    (h : m.run s = .ok a s₁) :
    (m >>= f).run s = (f a).run s₁ := by
  show (m >>= f) s = (f a) s₁
  simp only [bind, EStateM.bind]
  rw [show m s = .ok a s₁ from h]

theorem prog1_errors_on_zero (s : State) (h : s.x = 0) :
    ∃ s', prog1.run s = .error (Err.assertFailed "division by zero") s' := by
  let sz : State := { s with x := 0 }
  have h1 : doubleX.run s = .ok 0 sz := by
    rw [doubleX_run, h]
  have h2 : doubleX.run sz = .ok 0 sz := doubleX_run _
  have h3 : doubleX.run sz = .ok 0 sz := doubleX_run _
  have h4 : divYbyX.run sz = .error (Err.assertFailed "division by zero") sz :=
    divYbyX_run_err _ rfl
  refine ⟨sz, ?_⟩
  unfold prog1
  rw [bind_run_of_ok h1, bind_run_of_ok h2, bind_run_of_ok h3]
  exact h4


theorem prog1_on_5_320 (init_state final_state : State) 
  (h_start : init_state = { x := 5, y := 320 }) 
  (h_end : final_state = { x := 40, y := 320 }) 
  :
    prog1.run init_state = .ok 8 final_state := by
  let s1 : State := { x := 10, y := 320 }
  have h1 : doubleX.run init_state = .ok 10 s1 := by
    rw [h_start]
    exact doubleX_run _
  let s2 : State := { x := 20, y := 320 }
  have h2 : doubleX.run s1 = .ok 20 s2 := doubleX_run _ 
  have h3 : doubleX.run s2 = .ok 40 final_state := by 
    rw [h_end]
    exact doubleX_run _
  have hs3ne : final_state.x ≠ 0 := by
    rw [h_end]
    decide 
  have h4 : divYbyX.run final_state = .ok 8 final_state := by
    rw [h_end]
    exact divYbyX_run_ok _ (by rw [h_end] at hs3ne; exact hs3ne)
  -- Nothing has happened so far to the goal
  show prog1.run init_state = .ok 8 final_state
  unfold prog1
  -- Notice we do not actually simplify to that match business -
  -- we keep the imperative style. 
  rw [bind_run_of_ok h1, bind_run_of_ok h2, bind_run_of_ok h3]
  exact h4

end Blog
