import JoltConstraints.and_constraint

/-!
# AND tracing constraints

This file describes the constraints/claims created by reading a CPU trace and
building AND witness columns.

These are intentionally separate from the Jolt lookup constraint:

* `AND_JoltConstraint` is the polynomial identity.
* `AND_TracingConstraints` says the witness columns match the trace.
-/

namespace JoltConstraints

/-! ## Lookup Addresses -/

/-- A pair of `Xlen` source values forms the lookup-table key `rs1 || rs2`. -/
abbrev AND_LookupKey : Type :=
  BitVec (2 * Xlen)

/-- The lookup-table key for operands `a` and `b`. -/
def andLookupKey (a b : BitVec Xlen) : AND_LookupKey :=
  a +++ b

/-- The finite table row corresponding to key `a || b`. -/
def andLookupRow (a b : BitVec Xlen) : Fin AND_TableSize :=
  (andLookupKey a b).toFin

/-- Algebraic column that is `1` at `idx` and zero everywhere else. -/
def ColumnOneHotAtIdx {K : Nat} {F : Type} [Ring F]
    (col : Column K F) (idx : Fin K) : Prop :=
  col idx = 1 ∧
    forall k : Fin K, k ≠ idx -> col k = 0

/-! ## Trace-Built Witness Columns -/

/--
The full AND witness as built from tracing.

`jolt` contains the algebraic columns used by the Jolt constraint. The BitVec
columns record what the tracer claims it read from the CPU trace.
-/
structure AND_TraceWitness (T : Nat) (F : Type) where
  jolt : AND_Witness T F
  rs1Val : Column T (BitVec Xlen)
  rs2Val : Column T (BitVec Xlen)
  RDVal : Column T (BitVec Xlen)

/-- The predicate "this trace instruction is some `JoltISA.Instr.AND`". -/
def IsANDInstr (instr : JoltISA.Instr) : Prop :=
  exists (rd : JoltISA.Dst) (rs1 rs2 : JoltISA.Src),
    instr = JoltISA.Instr.AND rd rs1 rs2

/--
The source-value columns match the source reads performed by the JoltISA
semantics for decoded AND rows.
-/
def AND_SourceValuesFromTrace {T : Nat} {F : Type}
    (trace : CpuTrace T) (tw : AND_TraceWitness T F) : Prop :=
  forall (i : Fin T) (rd : JoltISA.Dst) (rs1 rs2 : JoltISA.Src),
    trace.instr i = JoltISA.Instr.AND rd rs1 rs2 ->
      exists afterRs1 afterRs2 : SailJoltState,
        (JoltISA.readSrc rs1).run (rowPreState trace i) =
          .ok (tw.rs1Val i) afterRs1 ∧
        (JoltISA.readSrc rs2).run afterRs1 =
          .ok (tw.rs2Val i) afterRs2

/--
Tracing constraints for AND.

These are the prover's trace-to-witness claims. They are not the polynomial
lookup constraint.
-/
structure AND_TracingConstraints {T : Nat} {F : Type} [Ring F]
    (encode : BitVec Xlen -> F)
    (trace : CpuTrace T) (tw : AND_TraceWitness T F) : Prop where
  flagSound :
    forall i : Fin T, tw.jolt.AND_FLAG i = 1 -> IsANDInstr (trace.instr i)
  flagComplete :
    forall i : Fin T, IsANDInstr (trace.instr i) -> tw.jolt.AND_FLAG i = 1
  sourceValues :
    AND_SourceValuesFromTrace trace tw
  lookupAddress :
    forall i : Fin T,
      tw.jolt.AND_FLAG i = 1 ->
        ColumnOneHotAtIdx (tw.jolt.RA_matrix i)
          (andLookupRow (tw.rs1Val i) (tw.rs2Val i))
  rdValEncoded :
    forall i : Fin T,
      tw.jolt.AND_FLAG i = 1 ->
        tw.jolt.RDVal i = encode (tw.RDVal i)

end JoltConstraints
