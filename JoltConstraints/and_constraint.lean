import JoltConstraints.polynomials
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess

/-!
# The necessary AND constraint

This file contains only:

1. the global Jolt polynomial data needed for AND;
2. the fixed AND lookup table;
3. the AND constraint;
4. the AND projection from an honest `JoltISATrace` to `JoltData`;
5. the theorem that the constraint is necessary for honest execution;
6. the row-level interface for composing it into a soundness proof.

The AND constraint alone is not sufficient for execution soundness. The
soundness theorem below therefore makes the required selector, lookup-address,
register, and encoding assumptions explicit.
-/

namespace JoltConstraints

open Sail PreSail LeanRV64D.Functions
open scoped BigOperators

universe u

/-! ## AND lookup domain -/

/-- One 64-bit operand represented as a finite lookup-table index. -/
abbrev ANDOperand : Type := InstructionLookupOperand

/-- An AND lookup key contains the two 64-bit source operands. -/
abbrev ANDLookupKey : Type := InstructionLookupKey

/-- A vector indexed by every possible pair of 64-bit operands. -/
abbrev ANDLookupVector (F : Type u) : Type u := InstructionLookupVector F

/-! ## AND table and constraint -/

/-- The fixed field-valued AND lookup table. -/
abbrev ANDTable (F : Type u) : Type u := ANDLookupVector F

/-- The concrete value stored in the AND table at `key`. -/
def ANDTableValue (key : ANDLookupKey) : BitVec Xlen :=
  BitVec.ofFin key.1 &&& BitVec.ofFin key.2

/-- Encode the concrete AND lookup table into the constraint field. -/
def encodedANDTable {F : Type u} 
    (encode : BitVec Xlen → F) : ANDTable F :=
  fun (key: InstructionLookupKey) => encode (ANDTableValue key)

/--
The constraint from the specification:

`AND_FLAG[i] * (RD_val[i] - ∑ k, ra[i,k] * T_AND[k]) = 0`.
-/
def ANDConstraint {T : Nat} {F : Type u} [Field F]
    (data : JoltData T F) 
    (T_AND : ANDTable F) : Prop :=
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
Project the polynomial data used by AND from an already-executed Jolt ISA
trace.

For an AND row, source values come from the pre-state and `RD_val` comes from
the post-state. Correctness of that state transition is already carried by
`isaTrace.executes`, whose definition uses `JoltISA.execInstr`.
-/
noncomputable def JoltISATrace.toANDData
    {T : Nat} {F : Type u} [Zero F] [One F]
    (isaTrace : JoltISATrace T)
    (encode : BitVec Xlen → F) : JoltData T F where
  trace := isaTrace.instrList
  polynomials :=
    { evals := fun polynomial =>
        match polynomial with
        | JoltPolynomial.committed .instructionRa => fun i =>
            match isaTrace.instrList i with
            | .AND _ rs1 rs2 =>
                oneHot (andLookupKey
                  (valueAtSource (isaTrace.preState i) rs1)
                  (valueAtSource (isaTrace.preState i) rs2))
            | _ => fun (_: InstructionLookupKey) => 0
        | JoltPolynomial.virtual .rdWriteValue => fun i =>
            match isaTrace.instrList i with
            | .AND rd _ _ =>
                encode (valueAtDestination (isaTrace.postState i) rd)
            | _ => 0
        | JoltPolynomial.virtual (.lookupTableFlag .AND) => fun i =>
            if isAND (isaTrace.instrList i) then 1 else 0 }

@[simp] theorem JoltISATrace.toANDData_AND_FLAG
    {T : Nat} {F : Type u} [Zero F] [One F]
    (isaTrace : JoltISATrace T) (encode : BitVec Xlen → F) (i : Fin T) :
    (isaTrace.toANDData encode).AND_FLAG i =
      if isAND (isaTrace.instrList i) then 1 else 0 := by
  rfl

@[simp] theorem JoltISATrace.toANDData_RD_val
    {T : Nat} {F : Type u} [Zero F] [One F]
    (isaTrace : JoltISATrace T) (encode : BitVec Xlen → F) (i : Fin T) :
    (isaTrace.toANDData encode).RD_val i =
      match isaTrace.instrList i with
      | .AND rd _ _ => encode (valueAtDestination (isaTrace.postState i) rd)
      | _ => 0 := by
  rfl

@[simp] theorem JoltISATrace.toANDData_ra
    {T : Nat} {F : Type u} [Zero F] [One F]
    (isaTrace : JoltISATrace T) (encode : BitVec Xlen → F) (i : Fin T) :
    (isaTrace.toANDData encode).ra i =
      match isaTrace.instrList i with
      | .AND _ rs1 rs2 =>
          oneHot (andLookupKey
            (valueAtSource (isaTrace.preState i) rs1)
            (valueAtSource (isaTrace.preState i) rs2))
      | _ => fun _ => 0 := by
  rfl

/-! ## Main theorem: necessity -/

/--
The AND constraint is necessary for honest Jolt ISA execution.

An honest trace already carries a proof that every row was stepped by
`JoltISA.execInstr`. Therefore the AND data projected from that trace satisfies
the specified lookup constraint.
-/
theorem ANDConstraint_isNecessary
    {T : Nat} {F : Type u} [Field F]
    (isaTrace : JoltISATrace T)
    (encode : BitVec Xlen → F) :
    ANDConstraint
      (isaTrace.toANDData encode)
      (encodedANDTable encode) := by
  unfold ANDConstraint
  intro i
  generalize hInstr : isaTrace.instrList i = instr
  cases instr <;>
    simp [hInstr, isAND]
  case AND dst lhs rhs =>
    have hrecorded : DestinationRecorded dst := by
      have hfinal := isaTrace.finalRow i
      rw [hInstr] at hfinal
      exact hfinal
    have houtput :
        valueAtDestination (isaTrace.postState i) dst =
          valueAtSource (isaTrace.preState i) lhs &&&
            valueAtSource (isaTrace.preState i) rhs := by
      apply AND_step_output dst lhs rhs hrecorded
      have hstep := isaTrace.executes i
      rw [hInstr] at hstep
      simpa only [JoltISATrace.preState, JoltISATrace.postState] using hstep
    simp [encodedANDTable, houtput]

/-! ## Soundness composition -/

/--
The AND lookup equation is sound for one selected row when the surrounding
constraint system supplies all of its consistency facts.

The hypotheses correspond to constraints outside `ANDConstraint`: the AND
selector is active, `ra` is one-hot at the source values, `RD_val` encodes the
claimed write value, the encoding is injective, and register reads/writeback
connect those values to the machine states. The conclusion deliberately uses
the existing `JoltISA.execInstr` semantics.

Without these additional hypotheses, `ANDConstraint` is not sufficient: for
example, setting `AND_FLAG` to zero makes its equation hold independently of
the row data.
-/
theorem ANDConstraint_isSoundAt
    {T : Nat} {F : Type u} [Field F]
    (data : JoltData T F)
    (encode : BitVec Xlen → F)
    (i : Fin T)
    (before after : SailJoltState)
    (dst : JoltISA.Dst) (lhs rhs : JoltISA.Src)
    (lhsValue rhsValue rdValue : BitVec Xlen)
    (hinstr : data.trace i = .AND dst lhs rhs)
    (hconstraint : ANDConstraint data (encodedANDTable encode))
    (hflag : data.AND_FLAG i = 1)
    (hra : data.ra i = oneHot (andLookupKey lhsValue rhsValue))
    (hrd : data.RD_val i = encode rdValue)
    (hencode : Function.Injective encode)
    (hlhs : JoltISA.readSrc lhs before = .ok lhsValue before)
    (hrhs : JoltISA.readSrc rhs before = .ok rhsValue before)
    (hwrite : JoltISA.writeDst dst rdValue before = .ok () after) :
    (JoltISA.execInstr (data.trace i)).run before =
      .ok RETIRE_SUCCESS after := by
  have hrow := hconstraint i
  rw [hflag, one_mul, hrd, hra, sum_oneHot_mul] at hrow
  simp only [encodedANDTable, ANDTableValue_andLookupKey] at hrow
  have hvalue : rdValue = lhsValue &&& rhsValue := by
    apply hencode
    exact sub_eq_zero.mp hrow
  subst rdValue
  rw [hinstr]
  simp only [JoltISA.execInstr, bind, EStateM.bind, EStateM.run]
  rw [hlhs]
  simp only
  rw [hrhs]
  simp only
  rw [hwrite]
  rfl

end JoltConstraints
