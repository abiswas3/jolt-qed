import LeanRV64D

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# meh5: JoltMonad ↔ SailM equivalence via projection

Architecture:
- JoltState = SequentialState + virtual registers (vregs)
- JoltMonad = EStateM over JoltState (same error type as SailM)
- project : JoltState → SailState drops vregs
- liftSail : SailM α → JoltMonad α runs Sail on the projected state
- Theorem: jolt_addw projected = execute_RTYPEW
-/

-- ============================================================================
-- Types
-- ============================================================================

abbrev SailState := SequentialState RegisterType trivialChoiceSource

structure JoltState where
  regs        : Std.ExtDHashMap Register RegisterType
  choiceState : Unit
  mem         : Std.ExtHashMap Nat (BitVec 8)
  tags        : Unit
  cycleCount  : Nat
  sailOutput  : Array String
  vregs       : BitVec 7 → BitVec 64 := fun _ => 0

abbrev JoltMonad (α : Type) := EStateM (Error exception) JoltState α

-- ============================================================================
-- Projection
-- ============================================================================

def project (js : JoltState) : SailState where
  regs := js.regs; choiceState := js.choiceState; mem := js.mem
  tags := js.tags; cycleCount := js.cycleCount; sailOutput := js.sailOutput

def projectResult (r : EStateM.Result (Error exception) JoltState α) :
    EStateM.Result (Error exception) SailState α :=
  match r with
  | .ok a js' => .ok a (project js')
  | .error e js' => .error e (project js')

-- ============================================================================
-- liftSail
-- ============================================================================

def liftSail (m : SailM α) : JoltMonad α := fun js =>
  match m (project js) with
  | .ok a ss' => .ok a { regs := ss'.regs, choiceState := ss'.choiceState,
                          mem := ss'.mem, tags := ss'.tags,
                          cycleCount := ss'.cycleCount, sailOutput := ss'.sailOutput,
                          vregs := js.vregs }
  | .error e ss' => .error e { regs := ss'.regs, choiceState := ss'.choiceState,
                                mem := ss'.mem, tags := ss'.tags,
                                cycleCount := ss'.cycleCount, sailOutput := ss'.sailOutput,
                                vregs := js.vregs }

-- Projecting after liftSail = running Sail directly.
theorem liftSail_project (m : SailM α) (js : JoltState) :
    projectResult ((liftSail m).run js) = m.run (project js) := by
  simp only [liftSail, projectResult, project, EStateM.run]
  cases hm : m ⟨js.regs, js.choiceState, js.mem, js.tags, js.cycleCount, js.sailOutput⟩ <;> simp_all

-- ============================================================================
-- Virtual register operations
-- ============================================================================

def readVReg (vr : BitVec 7) : JoltMonad (BitVec 64) := do
  let js ← get; pure (js.vregs vr)

def writeVReg (vr : BitVec 7) (val : BitVec 64) : JoltMonad Unit :=
  modify fun js => { js with vregs := fun r => if r = vr then val else js.vregs r }

def jolt_add (rd rs1 rs2 : BitVec 7) : JoltMonad Unit := do
  let v1 ← readVReg rs1; let v2 ← readVReg rs2; writeVReg rd (v1 + v2)

-- ============================================================================
-- Sail register helpers
-- INSPIRED BY OPENVM (OpenvmFv/RV32D/Auxiliaries.lean)
-- ============================================================================

-- Pure state update: insert a register value into the hash map.
def write_reg_state (s : SailState) (r : Register) (v : RegisterType r) : SailState :=
  { regs := s.regs.insert r v, choiceState := s.choiceState,
    mem := s.mem, tags := s.tags,
    cycleCount := s.cycleCount, sailOutput := s.sailOutput }

-- writeReg reduces to write_reg_state.
theorem writeReg_state_success (r : Register) (v : RegisterType r) (s : SailState) :
    Sail.writeReg r v s = .ok () (write_reg_state s r v) := by
  simp [Sail.writeReg, PreSail.writeReg, write_reg_state,
        modify, modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, EStateM.modifyGet]

-- After inserting (r, v), looking up r gives v.
@[simp] theorem writeReg_read_same (s : SailState) (r : Register) (v : RegisterType r) :
    (write_reg_state s r v).regs.get? r = some v := by
  unfold write_reg_state; grind

-- Double write collapses.
@[simp] theorem writeReg_write_same (s : SailState) (r : Register)
    (v1 : RegisterType r) (v2 : RegisterType r) :
    write_reg_state (write_reg_state s r v1) r v2 = write_reg_state s r v2 := by
  simp [write_reg_state]
  apply Std.ExtDHashMap.ext_get?
  intro reg; by_cases h : reg = r <;> grind

-- Writing to r2 doesn't affect reading r1 (r1 ≠ r2).
theorem writeReg_read_diff (s : SailState) (r1 r2 : Register)
    (v1 : RegisterType r1) (v2 : RegisterType r2)
    (h_val : s.regs.get? r1 = some v1) (h_neq : r1 ≠ r2) :
    (write_reg_state s r2 v2).regs.get? r1 = some v1 := by
  unfold write_reg_state; grind

-- If register r is in the hash map, readReg succeeds.
@[simp] theorem readReg_succ (r : Register) (v : RegisterType r) (s : SailState)
    (h : s.regs.get? r = some v) :
    Sail.readReg r s = .ok v s := by
  simp [Sail.readReg, PreSail.readReg,
        bind, EStateM.bind, pure, EStateM.pure,
        get, getThe, MonadStateOf.get, EStateM.get, h]

-- ============================================================================
-- Factored execute_RTYPEW (INSPIRED BY OPENVM Execution.lean)
-- ============================================================================

-- Pure ADDW computation: add 32-bit truncations, then sign-extend.
def execute_RTYPEW_pure (v1 v2 : BitVec 64) (op : ropw) : BitVec 64 :=
  let r1_32 := Sail.BitVec.extractLsb v1 31 0
  let r2_32 := Sail.BitVec.extractLsb v2 31 0
  let result : BitVec 32 := match op with
    | .ADDW => r1_32 + r2_32
    | .SUBW => r1_32 - r2_32
    | .SLLW => shift_bits_left r1_32 (Sail.BitVec.extractLsb r2_32 4 0)
    | .SRLW => shift_bits_right r1_32 (Sail.BitVec.extractLsb r2_32 4 0)
    | .SRAW => shift_bits_right_arith r1_32 (Sail.BitVec.extractLsb r2_32 4 0)
  sign_extend (m := 64) result

-- Factored execute_RTYPEW: read rs1, read rs2, compute pure result, write rd.
def execute_RTYPEW' (rs2 rs1 rd : regidx) (op : ropw) : SailM ExecutionResult := do
  let v1 ← rX_bits rs1
  let v2 ← rX_bits rs2
  wX_bits rd (execute_RTYPEW_pure v1 v2 op)
  pure RETIRE_SUCCESS

-- The factored version equals the original.
theorem execute_RTYPEW_eq_RTYPEW' (rs2 rs1 rd : regidx) (op : ropw) :
    execute_RTYPEW rs2 rs1 rd op = execute_RTYPEW' rs2 rs1 rd op := by
  cases op <;> simp [execute_RTYPEW, execute_RTYPEW', execute_RTYPEW_pure]

-- ============================================================================
-- rX_bits shape (from meh.lean)
-- ============================================================================

-- rX_bits either succeeds preserving state, or fails with Unreachable.
theorem rX_bits_shape (r : regidx) (s : SailState) :
    (∃ v, rX_bits r s = .ok v s) ∨
    (rX_bits r s = .error .Unreachable s) := by
  obtain ⟨i⟩ := r
  unfold rX_bits rX regval_from_reg Sail.readReg PreSail.readReg
  simp only [Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, Int.toNat_natCast,
             bind, EStateM.bind, pure, EStateM.pure,
             getThe, MonadStateOf.get, get,
             throw, throwThe, MonadExceptOf.throw]
  have hi : i.toNat < 32 := i.isLt
  have hcases : i.toNat = 0 ∨ i.toNat = 1 ∨ i.toNat = 2 ∨ i.toNat = 3 ∨
    i.toNat = 4 ∨ i.toNat = 5 ∨ i.toNat = 6 ∨ i.toNat = 7 ∨
    i.toNat = 8 ∨ i.toNat = 9 ∨ i.toNat = 10 ∨ i.toNat = 11 ∨
    i.toNat = 12 ∨ i.toNat = 13 ∨ i.toNat = 14 ∨ i.toNat = 15 ∨
    i.toNat = 16 ∨ i.toNat = 17 ∨ i.toNat = 18 ∨ i.toNat = 19 ∨
    i.toNat = 20 ∨ i.toNat = 21 ∨ i.toNat = 22 ∨ i.toNat = 23 ∨
    i.toNat = 24 ∨ i.toNat = 25 ∨ i.toNat = 26 ∨ i.toNat = 27 ∨
    i.toNat = 28 ∨ i.toNat = 29 ∨ i.toNat = 30 ∨ i.toNat = 31 := by omega
  rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
                     h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    simp_all [zero_reg, EStateM.pure, EStateM.get, EStateM.bind] <;>
    (first | (cases s.regs.get? _ <;> simp_all [EStateM.pure, EStateM.throw]) | skip)

-- wX_bits always succeeds.
theorem wX_shape (r : regidx) (v : BitVec 64) (s : SailState) :
    ∃ s', wX_bits r v s = .ok () s' := by
  obtain ⟨i⟩ := r
  unfold wX_bits wX regval_into_reg
  simp only [Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, Int.toNat_natCast,
             bind, pure]
  have hi : i.toNat < 32 := i.isLt
  have hcases : i.toNat = 0 ∨ i.toNat = 1 ∨ i.toNat = 2 ∨ i.toNat = 3 ∨
    i.toNat = 4 ∨ i.toNat = 5 ∨ i.toNat = 6 ∨ i.toNat = 7 ∨
    i.toNat = 8 ∨ i.toNat = 9 ∨ i.toNat = 10 ∨ i.toNat = 11 ∨
    i.toNat = 12 ∨ i.toNat = 13 ∨ i.toNat = 14 ∨ i.toNat = 15 ∨
    i.toNat = 16 ∨ i.toNat = 17 ∨ i.toNat = 18 ∨ i.toNat = 19 ∨
    i.toNat = 20 ∨ i.toNat = 21 ∨ i.toNat = 22 ∨ i.toNat = 23 ∨
    i.toNat = 24 ∨ i.toNat = 25 ∨ i.toNat = 26 ∨ i.toNat = 27 ∨
    i.toNat = 28 ∨ i.toNat = 29 ∨ i.toNat = 30 ∨ i.toNat = 31 := by omega
  rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
                     h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    simp_all [Sail.writeReg, PreSail.writeReg, xreg_write_callback,
              reg_name_forwards, to_bits] <;>
    exact ⟨_, rfl⟩

-- ============================================================================
-- BitVec lemma
-- ============================================================================

-- Truncating to 32 bits distributes over addition.
theorem extractLsb_add (a b : BitVec 64) :
    Sail.BitVec.extractLsb (a + b) 31 0 =
    Sail.BitVec.extractLsb a 31 0 + Sail.BitVec.extractLsb b 31 0 := by
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, Nat.add_mod]

-- ============================================================================
-- wX/rX round-trip and collapse (sorry — need OpenVM-style proof)
-- ============================================================================
-- After writing v to rd, reading rd gives v back.
theorem wX_rX_roundtrip (r : regidx) (v : BitVec 64) (s s' : SailState)
    (hw : wX_bits r v s = .ok () s') :
    rX_bits r s' = .ok v s' := by
  sorry

-- Double write to same register collapses.
theorem wX_wX_collapse (r : regidx) (v1 v2 : BitVec 64) (s s1 s2 : SailState)
    (hw1 : wX_bits r v1 s = .ok () s1) (hw2 : wX_bits r v2 s1 = .ok () s2) :
    wX_bits r v2 s = .ok () s2 := by
  sorry

-- ============================================================================
-- Jolt ADDW definition
-- ============================================================================

-- Virtual sign-extend-word: read rd, sign-extend lower 32 bits, write back.
def jolt_virtual_sign_extend_word (rd : regidx) : JoltMonad Unit := do
  let v ← liftSail (rX_bits rd)
  liftSail (wX_bits rd (sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0)))

-- Jolt's ADDW: real ADD via Sail, then virtual sign-extend.
def jolt_addw (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let _ ← liftSail (execute_RTYPE rs2 rs1 rd rop.ADD)
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

-- ============================================================================
-- Simpler theorems 
-- ============================================================================
-- Noop projected = noop.
theorem noop_eq (js : JoltState) :
    projectResult ((pure () : JoltMonad Unit).run js) =
    (pure () : SailM Unit).run (project js) := by
  simp [projectResult, pure, EStateM.pure, EStateM.run]

-- Virtual register ADD is invisible after projection.
theorem jolt_add_invisible (rd rs1 rs2 : BitVec 7) (js : JoltState) :
    projectResult ((jolt_add rd rs1 rs2).run js) =
    (pure () : SailM Unit).run (project js) := by
  simp only [projectResult, jolt_add, readVReg, writeVReg, project,
        bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
        get, getThe, MonadStateOf.get, EStateM.get,
        modify, modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, EStateM.modifyGet]

-- Virtual ADD then real Sail ADD = just the Sail ADD.
theorem jolt_program_eq_sail (r4 r5 r6 : regidx) (js : JoltState) :
    projectResult ((do jolt_add 40 41 42; liftSail (execute_RTYPE r4 r5 r6 rop.ADD)).run js) =
    (execute_RTYPE r4 r5 r6 rop.ADD).run (project js) := by
  simp only [jolt_add, readVReg, writeVReg, liftSail, projectResult, project,
        bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
        get, getThe, MonadStateOf.get, EStateM.get,
        modify, modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, EStateM.modifyGet]
  cases execute_RTYPE r4 r5 r6 rop.ADD
          ⟨js.regs, js.choiceState, js.mem, js.tags, js.cycleCount, js.sailOutput⟩ <;> rfl

-- ============================================================================
-- Main theorem: Jolt ADDW projected = Sail ADDW
-- ============================================================================

theorem jolt_addw_eq_sail (rs2 rs1 rd : regidx) (js : JoltState) :
    projectResult ((jolt_addw rs2 rs1 rd).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.ADDW).run (project js) := by
  -- Rewrite Sail side to factored form
  rw [execute_RTYPEW_eq_RTYPEW']
  -- Unfold both sides to raw EStateM chains
  simp only [jolt_addw, jolt_virtual_sign_extend_word, execute_RTYPEW',
        execute_RTYPEW_pure, liftSail, projectResult, project,
        bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
  -- Unfold execute_RTYPE (the ADD inside jolt_addw)
  simp only [execute_RTYPE, bind, EStateM.bind, pure, EStateM.pure]
  -- Both sides read rs1 then rs2. Case split on success/failure.
  cases rX_bits rs1 ⟨js.regs, js.choiceState, js.mem, js.tags, js.cycleCount, js.sailOutput⟩ with
  | error e s => simp
  | ok v1 s1 =>
    simp
    cases rX_bits rs2 s1 with
    | error e s => simp
    | ok v2 s2 =>
      simp
      -- Jolt: wX_bits rd (v1+v2), rX_bits rd, wX_bits rd (sign_extend(extractLsb(v1+v2)))
      -- Sail: wX_bits rd (sign_extend(extractLsb v1 + extractLsb v2))
      -- Step 1: first write succeeds
      obtain ⟨s3, hwx⟩ := wX_shape rd (v1 + v2) s2
      simp [hwx]
      -- Step 2: read-back gives v1+v2
      have hrx := wX_rX_roundtrip rd (v1 + v2) s2 s3 hwx
      simp [hrx]
      -- Step 3: extractLsb distributes over addition
      rw [extractLsb_add v1 v2]
      -- Step 4: double write collapses
      obtain ⟨s4, hwx2⟩ := wX_shape rd
          (sign_extend (Sail.BitVec.extractLsb v1 31 0 + Sail.BitVec.extractLsb v2 31 0)) s3
      have hcollapse := wX_wX_collapse rd (v1 + v2)
          (sign_extend (Sail.BitVec.extractLsb v1 31 0 + Sail.BitVec.extractLsb v2 31 0))
          s2 s3 s4 hwx hwx2
      simp [hwx2, hcollapse]

end
