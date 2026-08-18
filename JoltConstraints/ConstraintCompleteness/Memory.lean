import JoltConstraints.ConstraintCompleteness.Ram

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem honest_trustedAdvice
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params)
    (included : params.includeTrustedAdvice = true)
    (index : Fin params.trustedAdviceLength) :
    (honest_witness (F := F) trace).trustedAdvice included index =
      HonestWitness.fieldFromU64 (F := F) (trace.metadata.trustedAdvice index) := by
  rfl

theorem honest_untrustedAdvice
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params)
    (included : params.includeUntrustedAdvice = true)
    (index : Fin params.untrustedAdviceLength) :
    (honest_witness (F := F) trace).untrustedAdvice included index =
      HonestWitness.fieldFromU64 (F := F)
        (trace.metadata.untrustedAdvice index) := by
  rfl

theorem honest_trustedAdviceWord_eq
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) (index : Nat) :
    (honest_witness (F := F) trace).trustedAdviceWord index =
      HonestWitness.fieldFromU64 (F := F)
        (trace.metadata.trustedAdviceWord index) := by
  by_cases included : params.includeTrustedAdvice = true
  · by_cases inBounds : index < params.trustedAdviceLength
    · simp [JoltWitness.trustedAdviceWord,
        JoltTraceMetadata.trustedAdviceWord, included, inBounds,
        honest_trustedAdvice]
    · simp [JoltWitness.trustedAdviceWord,
        JoltTraceMetadata.trustedAdviceWord, included, inBounds,
        HonestWitness.fieldFromU64]
  · have absent : params.includeTrustedAdvice = false :=
      Bool.eq_false_of_not_eq_true included
    by_cases inBounds : index < params.trustedAdviceLength
    · have value_zero :=
        trace.metadataValid.trustedAdviceZeroIfAbsent absent
          ⟨index, inBounds⟩
      simp [JoltWitness.trustedAdviceWord,
        JoltTraceMetadata.trustedAdviceWord, included, inBounds,
        value_zero, HonestWitness.fieldFromU64]
    · simp [JoltWitness.trustedAdviceWord,
        JoltTraceMetadata.trustedAdviceWord, included, inBounds,
        HonestWitness.fieldFromU64]

theorem honest_untrustedAdviceWord_eq
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) (index : Nat) :
    (honest_witness (F := F) trace).untrustedAdviceWord index =
      HonestWitness.fieldFromU64 (F := F)
        (trace.metadata.untrustedAdviceWord index) := by
  by_cases included : params.includeUntrustedAdvice = true
  · by_cases inBounds : index < params.untrustedAdviceLength
    · simp [JoltWitness.untrustedAdviceWord,
        JoltTraceMetadata.untrustedAdviceWord, included, inBounds,
        honest_untrustedAdvice]
    · simp [JoltWitness.untrustedAdviceWord,
        JoltTraceMetadata.untrustedAdviceWord, included, inBounds,
        HonestWitness.fieldFromU64]
  · have absent : params.includeUntrustedAdvice = false :=
      Bool.eq_false_of_not_eq_true included
    by_cases inBounds : index < params.untrustedAdviceLength
    · have value_zero :=
        trace.metadataValid.untrustedAdviceZeroIfAbsent absent
          ⟨index, inBounds⟩
      simp [JoltWitness.untrustedAdviceWord,
        JoltTraceMetadata.untrustedAdviceWord, included, inBounds,
        value_zero, HonestWitness.fieldFromU64]
    · simp [JoltWitness.untrustedAdviceWord,
        JoltTraceMetadata.untrustedAdviceWord, included, inBounds,
        HonestWitness.fieldFromU64]

theorem honest_initialRamValue_eq
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) (address : Fin params.ramK) :
    (honest_witness (F := F) trace).initialRamValue
        trace.metadata.toJoltPublicInputs address =
      HonestWitness.fieldFromU64 (F := F)
        (trace.metadata.initialRamValue address) := by
  unfold JoltWitness.initialRamValue JoltWitness.untrustedAdviceAt?
    JoltWitness.trustedAdviceAt? JoltTraceMetadata.initialRamValue
    JoltTraceMetadata.untrustedAdviceAt?
    JoltTraceMetadata.trustedAdviceAt?
  cases trusted : params.includeTrustedAdvice <;>
    cases untrusted : params.includeUntrustedAdvice <;>
    simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals
    cases untrustedRegion :
      trace.metadata.untrustedAdviceRegion.index? address <;>
    cases trustedRegion :
      trace.metadata.trustedAdviceRegion.index? address <;>
    simp [honest_untrustedAdviceWord_eq, honest_trustedAdviceWord_eq,
      HonestWitness.fieldFromU64]

/-- One Rust RAM row contributes exactly `RamRa(address, i) * RamInc(i)` to
the field-valued state at `address`. -/
theorem honest_ram_state_step
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) (address : Fin params.ramK)
    (i : Fin params.traceLength) :
    HonestWitness.fieldFromU64 (F := F)
        (HonestWitness.memoryWord (trace.postState i)
          (trace.metadata.lowestMemoryAddress.toNat + 8 * address.val)) =
      HonestWitness.fieldFromU64 (F := F)
          (HonestWitness.memoryWord (trace.preState i)
            (trace.metadata.lowestMemoryAddress.toNat + 8 * address.val)) +
        (honest_witness (F := F) trace).ramRa address i *
          (honest_witness (F := F) trace).ramInc i := by
  let row := trace.rows i
  have valid : JoltTraceRow.Valid trace.metadata.toJoltPublicInputs row
      (trace.preState i) (trace.postState i) := by
    simpa [row, HonestTrace.preState, HonestTrace.postState] using
      trace.rowValid i
  have transition :
      HonestWitness.memoryWord (trace.postState i)
          (trace.metadata.lowestMemoryAddress.toNat + 8 * address.val) =
        if HonestWitness.remappedRamAddressFromPublic
            trace.metadata.toJoltPublicInputs row = some address.val then
          row.ramWriteValue
        else
          HonestWitness.memoryWord (trace.preState i)
            (trace.metadata.lowestMemoryAddress.toNat + 8 * address.val) := by
    simpa [row, HonestTrace.preState, HonestTrace.postState] using
      trace.ramStateTransition i address
  change
    HonestWitness.fieldFromU64 (F := F)
        (HonestWitness.memoryWord (trace.postState i)
          (trace.metadata.lowestMemoryAddress.toNat + 8 * address.val)) =
      HonestWitness.fieldFromU64 (F := F)
          (HonestWitness.memoryWord (trace.preState i)
            (trace.metadata.lowestMemoryAddress.toNat + 8 * address.val)) +
        (match HonestWitness.remappedRamAddress trace row with
        | some ramAddress =>
            HonestWitness.oneHot (F := F) address.val ramAddress
        | none => 0) *
          HonestWitness.fieldFromI128 (F := F)
            (HonestWitness.ramIncrement row)
  cases remapped : HonestWitness.remappedRamAddress trace row with
  | none =>
      have remappedPublic :
          HonestWitness.remappedRamAddressFromPublic
              trace.metadata.toJoltPublicInputs row = none := by
        simpa [HonestWitness.remappedRamAddress] using remapped
      rw [transition]
      simp [remappedPublic]
  | some selected =>
      have remappedPublic :
          HonestWitness.remappedRamAddressFromPublic
              trace.metadata.toJoltPublicInputs row = some selected := by
        simpa [HonestWitness.remappedRamAddress] using remapped
      by_cases selected_eq : selected = address.val
      · have read_eq :
            row.ramReadValue =
              HonestWitness.memoryWord (trace.preState i)
                (trace.metadata.lowestMemoryAddress.toNat + 8 * address.val) := by
          have := valid.ramReadValue_eq selected remappedPublic
          simpa [selected_eq] using this
        rw [transition]
        simp [remappedPublic, selected_eq,
          HonestWitness.oneHot, HonestWitness.fieldBool]
        rw [← read_eq]
        exact fieldFromU64_ramWriteValue_eq_readValue_add_increment row
      · have address_ne : address.val ≠ selected := Ne.symm selected_eq
        rw [transition]
        simp [remappedPublic, selected_eq, address_ne,
          HonestWitness.oneHot, HonestWitness.fieldBool]

/-- RAM state reconstructed after exactly `cycle` rows. -/
theorem honest_ram_state_at_cycle
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) (address : Fin params.ramK)
    (cycle : Nat) (cycle_le : cycle ≤ params.traceLength) :
    HonestWitness.fieldFromU64 (F := F)
        (HonestWitness.memoryWord
          (trace.state ⟨cycle, Nat.lt_succ_iff.mpr cycle_le⟩)
          (trace.metadata.lowestMemoryAddress.toNat + 8 * address.val)) =
      (honest_witness (F := F) trace).initialRamValue
          trace.metadata.toJoltPublicInputs address +
        ∑ j : Fin cycle,
          (honest_witness (F := F) trace).ramRa address
              ⟨j.val, lt_of_lt_of_le j.isLt cycle_le⟩ *
            (honest_witness (F := F) trace).ramInc
              ⟨j.val, lt_of_lt_of_le j.isLt cycle_le⟩ := by
  induction cycle with
  | zero =>
      rw [honest_initialRamValue_eq]
      rw [trace.initialRamState address]
      simp
  | succ cycle inductionHypothesis =>
      have cycle_lt : cycle < params.traceLength :=
        Nat.lt_of_succ_le cycle_le
      let i : Fin params.traceLength := ⟨cycle, cycle_lt⟩
      have step := honest_ram_state_step (F := F) trace address i
      have previous := inductionHypothesis (Nat.le_of_lt cycle_lt)
      have previous' :
          HonestWitness.fieldFromU64 (F := F)
              (HonestWitness.memoryWord
                (trace.state
                  ⟨cycle, Nat.lt_succ_iff.mpr (Nat.le_of_lt cycle_lt)⟩)
                (trace.metadata.lowestMemoryAddress.toNat + 8 * address.val)) =
            (honest_witness (F := F) trace).initialRamValue
                trace.metadata.toJoltPublicInputs address +
              ∑ j : Fin cycle,
                (honest_witness (F := F) trace).ramRa address
                    ⟨j.castSucc.val,
                      lt_of_lt_of_le j.castSucc.isLt cycle_le⟩ *
                  (honest_witness (F := F) trace).ramInc
                    ⟨j.castSucc.val,
                      lt_of_lt_of_le j.castSucc.isLt cycle_le⟩ := by
        simpa using previous
      rw [Fin.sum_univ_castSucc]
      rw [← add_assoc]
      rw [← previous']
      simpa [i, HonestTrace.preState, HonestTrace.postState,
        currentStateIndex, nextStateIndex, add_assoc] using step

end JoltConstraints.JoltConstraint.Completeness
