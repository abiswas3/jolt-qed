import JoltConstraints.basic
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess

/-!
# The necessary AND constraint

This file contains only:

1. the Jolt data needed for AND;
2. the fixed AND lookup table;
3. the AND constraint;
4. the projection from an honest `JoltISATrace` to `ANDData`;
5. the theorem that the constraint is necessary for honest execution.

No sufficiency claim is made here. Instruction/selector agreement will later be
enforced by the bytecode constraint.
-/

namespace JoltConstraints

open Sail PreSail LeanRV64D.Functions
open scoped BigOperators

universe u

/-! ## AND data -/

/-- One 64-bit operand represented as a finite lookup-table index. -/
abbrev ANDOperand : Type := Fin (2 ^ Xlen)

/-- An AND lookup key contains the two 64-bit source operands. -/
abbrev ANDLookupKey : Type := ANDOperand × ANDOperand

/-- A vector indexed by every possible pair of 64-bit operands. -/
abbrev ANDLookupVector (F : Type u) : Type u :=
  ANDLookupKey → F

/--
The prover-facing data used by the AND constraint.

These fields are claims. Their agreement with bytecode and the remaining Jolt
columns will be established by other constraints later.
-/
structure ANDData (T : Nat) (F : Type u) where
  /-- The instruction claimed at row `i`. -/
  trace : Column T JoltISA.Instr
  /-- `AND_FLAG[i] = 1` claims that row `i` is an AND instruction. -/
  AND_FLAG : Column T F
  /-- The encoded value claimed for the destination after row `i`. -/
  RD_val : Column T F
  /-- The `T × 2^128` lookup-address matrix for AND. -/
  ra : Column T (ANDLookupVector F)

/-! ## AND table and constraint -/

/-- The fixed field-valued AND lookup table. -/
abbrev ANDTable (F : Type u) : Type u :=
  ANDLookupVector F

/-- The concrete value stored in the AND table at `key`. -/
def ANDTableValue (key : ANDLookupKey) : BitVec Xlen :=
  BitVec.ofFin key.1 &&& BitVec.ofFin key.2

/-- Encode the concrete AND lookup table into the constraint field. -/
def encodedANDTable {F : Type u}
    (encode : BitVec Xlen → F) : ANDTable F :=
  fun key => encode (ANDTableValue key)

/--
The constraint from the specification:

`AND_FLAG[i] * (RD_val[i] - ∑ k, ra[i,k] * T_AND[k]) = 0`.
-/
def ANDConstraint {T : Nat} {F : Type u} [Field F]
    (data : ANDData T F) (T_AND : ANDTable F) : Prop :=
  ∀ i : Fin T,
    data.AND_FLAG i *
      (data.RD_val i -
        ∑ k : ANDLookupKey, data.ra i k * T_AND k) = 0

/-! ## Honest trace to AND data -/

/-- Whether a Jolt ISA instruction is AND. -/
def isAND : JoltISA.Instr → Bool
  | .AND _ _ _ => true
  | _ => false

/-- View a destination register as a readable register. -/
def destinationAsSource : JoltISA.Dst → JoltISA.Src
  | .vreg vr => .vreg vr
  | .xreg rd => .xreg rd

/-- Extract a register value from a traced machine state. -/
noncomputable def valueAtSource
    (state : SailJoltState) (src : JoltISA.Src) : BitVec Xlen :=
  match (JoltISA.readSrc src).run state with
  | .ok value _ => value
  | .error _ _ => 0

/-- Extract the destination value from the post-execution state. -/
noncomputable def valueAtDestination
    (state : SailJoltState) (dst : JoltISA.Dst) : BitVec Xlen :=
  valueAtSource state (destinationAsSource dst)

/-- The lookup key selected by two traced source values. -/
def andLookupKey (rs1Val rs2Val : BitVec Xlen) : ANDLookupKey :=
  (rs1Val.toFin, rs2Val.toFin)

/-- A one-hot lookup-address row selecting `key`. -/
def oneHot {F : Type u} [Zero F] [One F]
    (key : ANDLookupKey) : ANDLookupVector F :=
  fun k => if k = key then 1 else 0

@[simp] theorem ANDTableValue_andLookupKey
    (rs1Val rs2Val : BitVec Xlen) :
    ANDTableValue (andLookupKey rs1Val rs2Val) = rs1Val &&& rs2Val := by
  simp [ANDTableValue, andLookupKey]

@[simp] theorem sum_oneHot_mul
    {F : Type u} [Field F]
    (key : ANDLookupKey) (table : ANDTable F) :
    (∑ k : ANDLookupKey, oneHot key k * table k) = table key := by
  classical
  simp [oneHot]

/-! The following lemmas connect state observations to the existing ISA
register-access semantics. They do not define a second execution relation. -/

private theorem valueAtSource_eq_of_run
    {state state' : SailJoltState} {src : JoltISA.Src}
    {value : BitVec Xlen}
    (hread : (JoltISA.readSrc src).run state = .ok value state') :
    valueAtSource state src = value := by
  unfold valueAtSource
  rw [hread]

private theorem readSrc_run_state_eq
    {state state' : SailJoltState} {src : JoltISA.Src}
    {value : BitVec Xlen}
    (hread : (JoltISA.readSrc src).run state = .ok value state') :
    state' = state := by
  cases src with
  | vreg vr =>
      unfold JoltISA.readSrc readVReg at hread
      simp only [EStateM.run, get, getThe, MonadStateOf.get,
        pure] at hread
      cases hread
      rfl
  | xreg rs =>
      simp only [JoltISA.readSrc_xreg] at hread
      unfold liftSail at hread
      simp only [EStateM.run] at hread
      cases hrun : rX_bits rs state.sail with
      | error e sail' =>
          rw [hrun] at hread
          cases hread
      | ok readValue sail' =>
          have hsail : sail' = state.sail :=
            rX_bits_pure rs state.sail readValue sail' hrun
          rw [hrun] at hread
          cases hread
          cases hsail
          rfl

private theorem valueAtDestination_eq_of_write
    {before after : SailJoltState} {dst : JoltISA.Dst}
    {value : BitVec Xlen}
    (hrecorded : DestinationRecorded dst)
    (hwrite : (JoltISA.writeDst dst value).run before = .ok () after) :
    valueAtDestination after dst = value := by
  cases dst with
  | vreg vr =>
      rw [JoltISA.writeDst_vreg, writeVReg_run] at hwrite
      by_cases hwritable : vr.toNat < 32
      · simp only [hwritable, ↓reduceIte] at hwrite
        cases hwrite
      · simp only [hwritable, ↓reduceIte] at hwrite
        cases hwrite
        unfold valueAtDestination destinationAsSource valueAtSource
        unfold JoltISA.readSrc readVReg
        simp only [EStateM.run, bind, EStateM.bind, get, getThe,
          MonadStateOf.get, EStateM.get, pure, EStateM.pure]
        simp
  | xreg rd =>
      simp only [JoltISA.writeDst_xreg] at hwrite
      unfold liftSail at hwrite
      simp only [EStateM.run] at hwrite
      cases hw : wX_bits rd value before.sail with
      | error e sail' =>
          rw [hw] at hwrite
          cases hwrite
      | ok result sail' =>
          rw [hw] at hwrite
          cases hwrite
          have hsail : sail' = stateAfterWrite before.sail rd value :=
            wX_bits_eq_stateAfterWrite rd value before.sail sail' hw
          subst sail'
          unfold valueAtDestination destinationAsSource valueAtSource
          simp only [JoltISA.readSrc_xreg]
          unfold liftSail
          simp only [EStateM.run,
            rX_after_stateAfterWrite rd value before.sail hrecorded]

private theorem AND_step_output
    {before after : SailJoltState}
    (dst : JoltISA.Dst) (lhs rhs : JoltISA.Src)
    (hrecorded : DestinationRecorded dst)
    (hstep : (JoltISA.execInstr (.AND dst lhs rhs)).run before =
      .ok RETIRE_SUCCESS after) :
    valueAtDestination after dst =
      valueAtSource before lhs &&& valueAtSource before rhs := by
  simp only [JoltISA.execInstr, bind, EStateM.bind, EStateM.run] at hstep
  cases hlhs : JoltISA.readSrc lhs before with
  | error e stateAfterLhs =>
      rw [hlhs] at hstep
      cases hstep
  | ok lhsValue stateAfterLhs =>
      rw [hlhs] at hstep
      simp only at hstep
      have hlhsState : stateAfterLhs = before := readSrc_run_state_eq hlhs
      subst stateAfterLhs
      cases hrhs : JoltISA.readSrc rhs before with
      | error e stateAfterRhs =>
          rw [hrhs] at hstep
          cases hstep
      | ok rhsValue stateAfterRhs =>
          rw [hrhs] at hstep
          simp only at hstep
          have hrhsState : stateAfterRhs = before := readSrc_run_state_eq hrhs
          subst stateAfterRhs
          cases hwrite : JoltISA.writeDst dst (lhsValue &&& rhsValue) before with
          | error e stateAfterWrite =>
              rw [hwrite] at hstep
              cases hstep
          | ok result stateAfterWrite =>
              rw [hwrite] at hstep
              simp only [pure, EStateM.pure] at hstep
              cases hstep
              rw [valueAtDestination_eq_of_write hrecorded hwrite,
                valueAtSource_eq_of_run hlhs,
                valueAtSource_eq_of_run hrhs]

/--
Project the AND data from an already-executed Jolt ISA trace.

For an AND row, source values come from the pre-state and `RD_val` comes from
the post-state. Correctness of that state transition is already carried by
`trace.executes`, whose definition uses `JoltISA.execInstr`.
-/
noncomputable def JoltISATrace.toANDData
    {T : Nat} {F : Type u} [Zero F] [One F]
    (trace : JoltISATrace T)
    (encode : BitVec Xlen → F) : ANDData T F where
  trace := trace.instr
  AND_FLAG i := if isAND (trace.instr i) then 1 else 0
  RD_val i :=
    match trace.instr i with
    | .AND rd _ _ => encode (valueAtDestination (trace.postState i) rd)
    | _ => 0
  ra i :=
    match trace.instr i with
    | .AND _ rs1 rs2 =>
        oneHot <| andLookupKey
          (valueAtSource (trace.preState i) rs1)
          (valueAtSource (trace.preState i) rs2)
    | _ => fun _ => 0

/-! ## Main theorem: necessity -/

/--
The AND constraint is necessary for honest Jolt ISA execution.

An honest trace already carries a proof that every row was stepped by
`JoltISA.execInstr`. Therefore the AND data projected from that trace satisfies
the specified lookup constraint.
-/
theorem ANDConstraint_isNecessary
    {T : Nat} {F : Type u} [Field F]
    (trace : JoltISATrace T)
    (encode : BitVec Xlen → F) :
    ANDConstraint
      (trace.toANDData encode)
      (encodedANDTable encode) := by
  unfold ANDConstraint
  intro i
  generalize hInstr : trace.instr i = instr
  cases instr <;>
    simp [JoltISATrace.toANDData, hInstr, isAND]
  case AND dst lhs rhs =>
    have hrecorded : DestinationRecorded dst := by
      have hfinal := trace.finalRow i
      rw [hInstr] at hfinal
      exact hfinal
    have houtput :
        valueAtDestination (trace.postState i) dst =
          valueAtSource (trace.preState i) lhs &&&
            valueAtSource (trace.preState i) rhs := by
      apply AND_step_output dst lhs rhs hrecorded
      have hstep := trace.executes i
      rw [hInstr] at hstep
      simpa only [JoltISATrace.preState, JoltISATrace.postState] using hstep
    simp [encodedANDTable, houtput]

end JoltConstraints
