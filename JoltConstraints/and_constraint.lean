import JoltConstraints.polynomials
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess

/-!
# The AND-table witness and writeback constraint

This file contains only:

1. the global Jolt polynomial data needed for AND;
2. the fixed AND lookup table;
3. the R1CS lookup-output writeback constraint;
4. the AND-table projection from an honest `JoltISATrace` to `JoltData`;
5. the theorem that the constraint is necessary for honest execution;
6. the row-level interface for composing it into a soundness proof.

The writeback constraint alone is not sufficient for execution soundness. The
soundness theorem below therefore makes the required selector, lookup-output,
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

/-- Jolt's canonical `u64`-to-field witness encoding (`F::from_u64` in Rust). -/
def fieldEncode {F : Type u} [NatCast F] (value : BitVec Xlen) : F :=
  value.toNat

/-- Encode the concrete AND lookup table into the constraint field. -/
def encodedANDTable {F : Type u} [NatCast F] : ANDTable F :=
  fun (key : InstructionLookupKey) => fieldEncode (ANDTableValue key)

/--
R1CS constraint 12, `RdWriteEqLookupIfWriteLookupToRd`, from Jolt's generated
RV64 constraint system:

`WriteLookupOutputToRD[i] * (RdWriteValue[i] - LookupOutput[i]) = 0`.

The instruction lookup argument separately relates `LookupOutput` to the
selected table, lookup-table flag, and instruction read address.
-/
def ANDConstraint {T : Nat} {F : Type u} [Field F]
    (data : JoltData T F) : Prop :=
  ∀ i : Fin T,
    data.writeLookupOutputToRD i *
      (data.rdWriteValue i - data.lookupOutput i) = 0

/-! ## Honest trace to AND data -/

/-- Whether a Jolt ISA instruction is the register-register `AND` opcode. -/
def isAND : JoltISA.Instr → Bool
  | .AND _ _ _ => true
  | _ => false

/-- Whether a Jolt ISA instruction is the immediate `ANDI` opcode. -/
def isANDI : JoltISA.Instr → Bool
  | .ANDI _ _ _ => true
  | _ => false

/-- Whether a Jolt ISA instruction uses Jolt's shared `And` lookup table. -/
def usesANDTable : JoltISA.Instr → Bool
  | .ANDI _ _ _ => true
  | .AND _ _ _ => true
  | _ => false

/-- View a destination register as a readable register. -/
def destinationAsSource : JoltISA.Dst → JoltISA.Src
  | .vreg vr => .vreg vr
  | .xreg rd => .xreg rd

/-- Convert a source operand to Jolt's absolute 7-bit register address. -/
def sourceRegisterAddress : JoltISA.Src → RegisterAddress
  | .vreg vr => vr
  | .xreg (regidx.Regidx bits) => BitVec.ofNat 7 bits.toNat

/-- Convert a destination operand to Jolt's absolute 7-bit register address. -/
def destinationRegisterAddress : JoltISA.Dst → RegisterAddress
  | .vreg vr => vr
  | .xreg (regidx.Regidx bits) => BitVec.ofNat 7 bits.toNat

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

/-- A one-hot register-address row selecting `address`. -/
def registerOneHot {F : Type u} [Zero F] [One F]
    (address : RegisterAddress) : RegisterAddressVector F :=
  fun candidate => if candidate = address then 1 else 0

/-- The destination of an instruction using the shared AND lookup table. -/
def andTableDestination : JoltISA.Instr → Option JoltISA.Dst
  | .ANDI dst _ _ => some dst
  | .AND dst _ _ => some dst
  | _ => none

/-- The first register source of an instruction using the AND table. -/
def andTableRs1 : JoltISA.Instr → Option JoltISA.Src
  | .ANDI _ src _ => some src
  | .AND _ lhs _ => some lhs
  | _ => none

/-- The optional second register source of an instruction using the AND table. -/
def andTableRs2 : JoltISA.Instr → Option JoltISA.Src
  | .AND _ _ rhs => some rhs
  | _ => none

/-- The two concrete operands sent to the shared AND lookup table. -/
noncomputable def andTableOperands
    (state : SailJoltState) : JoltISA.Instr → Option (BitVec Xlen × BitVec Xlen)
  | .ANDI _ src imm =>
      some (valueAtSource state src, sign_extend (m := Xlen) imm)
  | .AND _ lhs rhs =>
      some (valueAtSource state lhs, valueAtSource state rhs)
  | _ => none

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

private theorem ANDI_step_output
    {before after : SailJoltState}
    (dst : JoltISA.Dst) (src : JoltISA.Src) (imm : BitVec 12)
    (hrecorded : DestinationRecorded dst)
    (hstep : (JoltISA.execInstr (.ANDI dst src imm)).run before =
      .ok RETIRE_SUCCESS after) :
    valueAtDestination after dst =
      valueAtSource before src &&& sign_extend (m := Xlen) imm := by
  simp only [JoltISA.execInstr, bind, EStateM.bind, EStateM.run] at hstep
  cases hsrc : JoltISA.readSrc src before with
  | error e stateAfterSrc =>
      rw [hsrc] at hstep
      cases hstep
  | ok srcValue stateAfterSrc =>
      rw [hsrc] at hstep
      simp only at hstep
      have hsrcState : stateAfterSrc = before := readSrc_run_state_eq hsrc
      subst stateAfterSrc
      cases hwrite : JoltISA.writeDst dst
          (srcValue &&& sign_extend (m := Xlen) imm) before with
      | error e stateAfterWrite =>
          rw [hwrite] at hstep
          cases hstep
      | ok result stateAfterWrite =>
          rw [hwrite] at hstep
          simp only [pure, EStateM.pure] at hstep
          cases hstep
          rw [valueAtDestination_eq_of_write hrecorded hwrite,
            valueAtSource_eq_of_run hsrc]

/--
Project the witness columns contributed by instructions using Jolt's shared
AND lookup table from an already-executed Jolt ISA trace.

This is a sparse AND-table projection: `AND` and `ANDI` rows carry their real
values and all other rows are zero. Source values come from the pre-state and
destination write values come from the post-state. Correctness of each state
transition is already carried by `isaTrace.executes`.
-/
noncomputable def JoltISATrace.toANDData
    {T : Nat} {F : Type u} [Field F]
    (isaTrace : JoltISATrace T) : JoltData T F where
  trace := isaTrace.instrList
  polynomials :=
    { evals := fun polynomial =>
        match polynomial with
        | JoltPolynomial.committed .rdInc => fun i =>
            match andTableDestination (isaTrace.instrList i) with
            | some dst =>
                fieldEncode (valueAtDestination (isaTrace.postState i) dst) -
                  fieldEncode (valueAtDestination (isaTrace.preState i) dst)
            | none => 0
        | JoltPolynomial.committed .instructionRa => fun i =>
            match andTableOperands (isaTrace.preState i) (isaTrace.instrList i) with
            | some (lhs, rhs) => oneHot (andLookupKey lhs rhs)
            | none => fun (_ : InstructionLookupKey) => 0
        | JoltPolynomial.virtual .leftLookupOperand => fun i =>
            match andTableOperands (isaTrace.preState i) (isaTrace.instrList i) with
            | some (lhs, _) => fieldEncode lhs
            | none => 0
        | JoltPolynomial.virtual .rightLookupOperand => fun i =>
            match andTableOperands (isaTrace.preState i) (isaTrace.instrList i) with
            | some (_, rhs) => fieldEncode rhs
            | none => 0
        | JoltPolynomial.virtual .leftInstructionInput => fun i =>
            match andTableOperands (isaTrace.preState i) (isaTrace.instrList i) with
            | some (lhs, _) => fieldEncode lhs
            | none => 0
        | JoltPolynomial.virtual .rightInstructionInput => fun i =>
            match andTableOperands (isaTrace.preState i) (isaTrace.instrList i) with
            | some (_, rhs) => fieldEncode rhs
            | none => 0
        | JoltPolynomial.virtual .rs1Value => fun i =>
            match andTableRs1 (isaTrace.instrList i) with
            | some rs1 => fieldEncode (valueAtSource (isaTrace.preState i) rs1)
            | none => 0
        | JoltPolynomial.virtual .rs2Value => fun i =>
            match andTableRs2 (isaTrace.instrList i) with
            | some rs2 => fieldEncode (valueAtSource (isaTrace.preState i) rs2)
            | none => 0
        | JoltPolynomial.virtual .rdWriteValue => fun i =>
            match andTableDestination (isaTrace.instrList i) with
            | some rd => fieldEncode (valueAtDestination (isaTrace.postState i) rd)
            | none => 0
        | JoltPolynomial.virtual .rs1Ra => fun i =>
            match andTableRs1 (isaTrace.instrList i) with
            | some rs1 => registerOneHot (sourceRegisterAddress rs1)
            | none => fun (_ : RegisterAddress) => 0
        | JoltPolynomial.virtual .rs2Ra => fun i =>
            match andTableRs2 (isaTrace.instrList i) with
            | some rs2 => registerOneHot (sourceRegisterAddress rs2)
            | none => fun (_ : RegisterAddress) => 0
        | JoltPolynomial.virtual .rdWa => fun i =>
            match andTableDestination (isaTrace.instrList i) with
            | some rd => registerOneHot (destinationRegisterAddress rd)
            | none => fun (_ : RegisterAddress) => 0
        | JoltPolynomial.virtual .lookupOutput => fun i =>
            match andTableOperands (isaTrace.preState i) (isaTrace.instrList i) with
            | some (lhs, rhs) => fieldEncode (lhs &&& rhs)
            | none => 0
        | JoltPolynomial.virtual .instructionRafFlag => fun _ => 0
        | JoltPolynomial.virtual (.opFlag .writeLookupOutputToRD) => fun i =>
            if usesANDTable (isaTrace.instrList i) then 1 else 0
        | JoltPolynomial.virtual
            (.instructionFlag .leftOperandIsRs1Value) => fun i =>
            if usesANDTable (isaTrace.instrList i) then 1 else 0
        | JoltPolynomial.virtual
            (.instructionFlag .rightOperandIsRs2Value) => fun i =>
            if isAND (isaTrace.instrList i) then 1 else 0
        | JoltPolynomial.virtual
            (.instructionFlag .rightOperandIsImm) => fun i =>
            if isANDI (isaTrace.instrList i) then 1 else 0
        | JoltPolynomial.virtual (.lookupTableFlag .AND) => fun i =>
            if usesANDTable (isaTrace.instrList i) then 1 else 0 }

@[simp] theorem JoltISATrace.toANDData_AND_FLAG
    {T : Nat} {F : Type u} [Field F]
    (isaTrace : JoltISATrace T) (i : Fin T) :
    (isaTrace.toANDData (F := F)).AND_FLAG i =
      if usesANDTable (isaTrace.instrList i) then 1 else 0 := by
  rfl

@[simp] theorem JoltISATrace.toANDData_RD_val
    {T : Nat} {F : Type u} [Field F]
    (isaTrace : JoltISATrace T) (i : Fin T) :
    (isaTrace.toANDData (F := F)).RD_val i =
      match andTableDestination (isaTrace.instrList i) with
      | some rd => fieldEncode (valueAtDestination (isaTrace.postState i) rd)
      | none => 0 := by
  rfl

@[simp] theorem JoltISATrace.toANDData_rdWriteValue
    {T : Nat} {F : Type u} [Field F]
    (isaTrace : JoltISATrace T) (i : Fin T) :
    (isaTrace.toANDData (F := F)).rdWriteValue i =
      match andTableDestination (isaTrace.instrList i) with
      | some rd => fieldEncode (valueAtDestination (isaTrace.postState i) rd)
      | none => 0 := by
  rfl

@[simp] theorem JoltISATrace.toANDData_ra
    {T : Nat} {F : Type u} [Field F]
    (isaTrace : JoltISATrace T) (i : Fin T) :
    (isaTrace.toANDData (F := F)).ra i =
      match andTableOperands (isaTrace.preState i) (isaTrace.instrList i) with
      | some (lhs, rhs) => oneHot (andLookupKey lhs rhs)
      | none => fun _ => 0 := by
  rfl

@[simp] theorem JoltISATrace.toANDData_writeLookupOutputToRD
    {T : Nat} {F : Type u} [Field F]
    (isaTrace : JoltISATrace T) (i : Fin T) :
    (isaTrace.toANDData (F := F)).writeLookupOutputToRD i =
      if usesANDTable (isaTrace.instrList i) then 1 else 0 := by
  rfl

@[simp] theorem JoltISATrace.toANDData_lookupOutput
    {T : Nat} {F : Type u} [Field F]
    (isaTrace : JoltISATrace T) (i : Fin T) :
    (isaTrace.toANDData (F := F)).lookupOutput i =
      match andTableOperands (isaTrace.preState i) (isaTrace.instrList i) with
      | some (lhs, rhs) => fieldEncode (lhs &&& rhs)
      | none => 0 := by
  rfl

/-! ## Main theorem: necessity -/

/--
The R1CS lookup-output writeback constraint is necessary for honest `AND` and
`ANDI` execution.

An honest trace already carries a proof that every row was stepped by
`JoltISA.execInstr`. Therefore its sparse AND-table projection has equal
`RdWriteValue` and `LookupOutput` values whenever
`WriteLookupOutputToRD` is active.
-/
theorem ANDConstraint_isNecessary
    {T : Nat} {F : Type u} [Field F]
    (isaTrace : JoltISATrace T) :
    ANDConstraint (isaTrace.toANDData (F := F)) := by
  unfold ANDConstraint
  intro i
  generalize hInstr : isaTrace.instrList i = instr
  cases instr <;>
    simp [hInstr, usesANDTable, andTableDestination, andTableOperands]
  case ANDI dst src imm =>
    have hrecorded : DestinationRecorded dst := by
      have hfinal := isaTrace.finalRow i
      rw [hInstr] at hfinal
      exact hfinal
    have houtput :
        valueAtDestination (isaTrace.postState i) dst =
          valueAtSource (isaTrace.preState i) src &&&
            sign_extend (m := Xlen) imm := by
      apply ANDI_step_output dst src imm hrecorded
      have hstep := isaTrace.executes i
      rw [hInstr] at hstep
      simpa only [JoltISATrace.preState, JoltISATrace.postState] using hstep
    simp [houtput]
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
    simp [houtput]

/-! ## Soundness composition -/

/--
The lookup-output writeback equation contributes to soundness for one selected
AND row when the surrounding constraint system supplies all consistency facts.

The hypotheses correspond to constraints outside `ANDConstraint`: the
write-lookup-output selector is active, `LookupOutput` is the AND of the source
values, `RdWriteValue` is the claimed write value, the canonical field encoding
is injective on 64-bit values, and register reads/writeback connect those values
to the machine states. The conclusion deliberately uses the existing
`JoltISA.execInstr` semantics.

Without these additional hypotheses, `ANDConstraint` is not sufficient: for
example, setting `WriteLookupOutputToRD` to zero makes its equation hold
independently of the row data.
-/
theorem ANDConstraint_isSoundAt
    {T : Nat} {F : Type u} [Field F]
    (data : JoltData T F)
    (i : Fin T)
    (before after : SailJoltState)
    (dst : JoltISA.Dst) (lhs rhs : JoltISA.Src)
    (lhsValue rhsValue rdValue : BitVec Xlen)
    (hinstr : data.trace i = .AND dst lhs rhs)
    (hconstraint : ANDConstraint data)
    (hflag : data.writeLookupOutputToRD i = 1)
    (hrd : data.rdWriteValue i = fieldEncode rdValue)
    (hlookup : data.lookupOutput i = fieldEncode (lhsValue &&& rhsValue))
    (hencode : Function.Injective (fieldEncode (F := F)))
    (hlhs : JoltISA.readSrc lhs before = .ok lhsValue before)
    (hrhs : JoltISA.readSrc rhs before = .ok rhsValue before)
    (hwrite : JoltISA.writeDst dst rdValue before = .ok () after) :
    (JoltISA.execInstr (data.trace i)).run before =
      .ok RETIRE_SUCCESS after := by
  have hrow := hconstraint i
  rw [hflag, one_mul, hrd, hlookup] at hrow
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
