import JoltConstraints.ConstraintCompleteness.Register

namespace JoltConstraints.JoltConstraint.Completeness

universe u

/-- One Rust register row contributes exactly `RdWa(address, i) * RdInc(i)`
to the field-valued state at `address`. -/
theorem honest_register_state_step
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) (address : RegisterAddress)
    (i : Fin params.traceLength) :
    HonestWitness.fieldFromU64 (F := F)
        (HonestWitness.registerAtAddress (trace.postState i) address) =
      HonestWitness.fieldFromU64 (F := F)
          (HonestWitness.registerAtAddress (trace.preState i) address) +
        (honest_witness (F := F) trace).rdWa address i *
          (honest_witness (F := F) trace).rdInc i := by
  let row := trace.rows i
  have valid : JoltTraceRow.Valid trace.metadata.toJoltPublicInputs row
      (trace.preState i) (trace.postState i) := by
    simpa [row, HonestTrace.preState, HonestTrace.postState] using
      trace.rowValid i
  have transition :
      HonestWitness.registerAtAddress (trace.postState i) address =
        match row.instructionRow.operands.rd with
        | some destination =>
            if destination = address then
              row.rdWriteValue
            else
              HonestWitness.registerAtAddress (trace.preState i) address
        | none =>
            HonestWitness.registerAtAddress (trace.preState i) address := by
    simpa [row, HonestTrace.preState, HonestTrace.postState] using
      trace.registerStateTransition i address
  change
    HonestWitness.fieldFromU64 (F := F)
        (HonestWitness.registerAtAddress (trace.postState i) address) =
      HonestWitness.fieldFromU64 (F := F)
          (HonestWitness.registerAtAddress (trace.preState i) address) +
        HonestWitness.registerAddressIndicator
            row.instructionRow.operands.rd address *
          HonestWitness.fieldFromI128 (F := F)
            (HonestWitness.rdIncrement row)
  cases destination_option_eq : row.instructionRow.operands.rd with
  | none =>
      rw [transition]
      simp [destination_option_eq, HonestWitness.registerAddressIndicator,
        HonestWitness.rdIncrement, HonestWitness.fieldFromI128]
  | some destination =>
      by_cases destination_eq : destination = address
      · subst destination
        have pre_eq :
            row.rdPreValue = HonestWitness.registerAtAddress
              (trace.preState i) address := by
          simpa [destination_option_eq,
            HonestWitness.registerAtOptionalAddress] using
            valid.rdPreValue_eq
        rw [transition]
        simp only [destination_option_eq, ↓reduceIte]
        simp [HonestWitness.registerAddressIndicator,
          HonestWitness.fieldBool, HonestWitness.rdIncrement]
        rw [← pre_eq]
        rw [destination_option_eq]
        exact fieldFromU64_add_signedDifference (F := F)
          row.rdPreValue row.rdWriteValue
      · rw [transition]
        simp [destination_option_eq, destination_eq,
          HonestWitness.registerAddressIndicator,
          HonestWitness.fieldBool]

/-- Register state reconstructed after exactly `cycle` proof rows. -/
theorem honest_register_state_at_cycle
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) (address : RegisterAddress)
    (cycle : Nat) (cycle_le : cycle ≤ params.traceLength) :
    HonestWitness.fieldFromU64 (F := F)
        (HonestWitness.registerAtAddress
          (trace.state ⟨cycle, Nat.lt_succ_iff.mpr cycle_le⟩) address) =
      ∑ j : Fin cycle,
        (honest_witness (F := F) trace).rdWa address
            ⟨j.val, lt_of_lt_of_le j.isLt cycle_le⟩ *
          (honest_witness (F := F) trace).rdInc
            ⟨j.val, lt_of_lt_of_le j.isLt cycle_le⟩ := by
  induction cycle with
  | zero =>
      rw [trace.initialRegistersZero address]
      simp [HonestWitness.fieldFromU64]
  | succ cycle inductionHypothesis =>
      have cycle_lt : cycle < params.traceLength :=
        Nat.lt_of_succ_le cycle_le
      let i : Fin params.traceLength := ⟨cycle, cycle_lt⟩
      have step := honest_register_state_step (F := F) trace address i
      have previous := inductionHypothesis (Nat.le_of_lt cycle_lt)
      have previous' :
          HonestWitness.fieldFromU64 (F := F)
              (HonestWitness.registerAtAddress
                (trace.state
                  ⟨cycle, Nat.lt_succ_iff.mpr (Nat.le_of_lt cycle_lt)⟩)
                address) =
            ∑ j : Fin cycle,
              (honest_witness (F := F) trace).rdWa address
                  ⟨j.castSucc.val,
                    lt_of_lt_of_le j.castSucc.isLt cycle_le⟩ *
                (honest_witness (F := F) trace).rdInc
                  ⟨j.castSucc.val,
                    lt_of_lt_of_le j.castSucc.isLt cycle_le⟩ := by
        simpa using previous
      rw [Fin.sum_univ_castSucc]
      rw [← previous']
      simpa [i, HonestTrace.preState, HonestTrace.postState,
        currentStateIndex, nextStateIndex] using step

end JoltConstraints.JoltConstraint.Completeness
