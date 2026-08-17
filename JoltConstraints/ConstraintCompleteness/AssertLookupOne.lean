import JoltConstraints.constraints
import JoltConstraints.trace

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem assertLookupOne
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .assertLookupOne
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro i
  -- TODO: require well-formed final Jolt instructions as well as successful
  -- execution. In particular, `VirtualAssertEQ` with a nonzero immediate
  -- retires successfully in `execInstr` without requiring equal operands.
  sorry

end JoltConstraints.JoltConstraint.Completeness
