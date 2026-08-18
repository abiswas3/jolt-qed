import JoltConstraints.ConstraintCompleteness.Ram

namespace JoltConstraints.JoltConstraint.Completeness

universe u

/-! Arithmetic facts shared by committed/virtual read-address proofs. -/

theorem Nat.eq_of_base_digits_eq
    (base digits left right : Nat) (base_pos : 0 < base)
    (left_bound : left < base ^ digits)
    (right_bound : right < base ^ digits)
    (digits_eq : ∀ i : Fin digits,
      left / base ^ i.val % base = right / base ^ i.val % base) :
    left = right := by
  induction digits generalizing left right with
  | zero =>
      simp at left_bound right_bound
      omega
  | succ digits inductionHypothesis =>
      have low_digit := digits_eq (0 : Fin (digits + 1))
      simp at low_digit
      have left_quotient_bound : left / base < base ^ digits := by
        apply (Nat.div_lt_iff_lt_mul base_pos).2
        simpa [pow_succ] using left_bound
      have right_quotient_bound : right / base < base ^ digits := by
        apply (Nat.div_lt_iff_lt_mul base_pos).2
        simpa [pow_succ] using right_bound
      have quotient_digits : ∀ i : Fin digits,
          left / base / base ^ i.val % base =
            right / base / base ^ i.val % base := by
        intro i
        have next_digit := digits_eq i.succ
        simpa [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm,
          Nat.mul_left_comm, Nat.mul_assoc] using next_digit
      have quotients_eq : left / base = right / base :=
        inductionHypothesis (left / base) (right / base)
          left_quotient_bound right_quotient_bound quotient_digits
      calc
        left = left % base + left / base * base :=
          (Nat.mod_add_div' left base).symm
        _ = right % base + right / base * base := by
          rw [low_digit, quotients_eq]
        _ = right := Nat.mod_add_div' right base

/-- MSB-first chunk selectors jointly determine every value that fits inside
their combined digit width. This is the generic algebra behind all Jolt `D`
read-address layouts. -/
theorem raChunkSelectors_jointly_injective
    {chunks bits left right : Nat} (bitsPositive : 0 < bits)
    (leftBound : left < 2 ^ (chunks * bits))
    (rightBound : right < 2 ^ (chunks * bits))
    (chunksEq : ∀ chunk : Fin chunks,
      (⟨chunk⟩ : JoltRaChunkSelector chunks bits).chunk left =
        (⟨chunk⟩ : JoltRaChunkSelector chunks bits).chunk right) :
    left = right := by
  let base := 2 ^ bits
  have basePositive : 0 < base := by simp [base]
  have basePowEq : base ^ chunks = 2 ^ (chunks * bits) := by
    calc
      base ^ chunks = 2 ^ (bits * chunks) := by
        simp [base, Nat.pow_mul]
      _ = 2 ^ (chunks * bits) := by rw [Nat.mul_comm]
  apply Nat.eq_of_base_digits_eq base chunks left right basePositive
  · simpa [basePowEq] using leftBound
  · simpa [basePowEq] using rightBound
  · intro digit
    let chunk : Fin chunks := Fin.rev digit
    have shiftEq :
        (⟨chunk⟩ : JoltRaChunkSelector chunks bits).shift =
          digit.val * bits := by
      simp [JoltRaChunkSelector.shift, chunk, Fin.rev]
      omega
    have chunkValues := congrArg Fin.val (chunksEq chunk)
    change
      left / 2 ^ (⟨chunk⟩ : JoltRaChunkSelector chunks bits).shift %
            2 ^ bits =
        right / 2 ^ (⟨chunk⟩ : JoltRaChunkSelector chunks bits).shift %
            2 ^ bits at chunkValues
    rw [shiftEq] at chunkValues
    simpa [base, pow_mul'] using chunkValues

/-- Products of digit-wise one-hot selectors reconstruct the one-hot selector
for the complete address whenever the digit selectors are jointly injective. -/
theorem product_oneHot_eq_oneHot_of_jointly_injective
    {chunks addressCount digitCount : Nat} {F : Type u} [Field F]
    (selector : Fin chunks → Fin addressCount → Fin digitCount)
    (jointlyInjective : ∀ {left right : Fin addressCount},
      (∀ chunk, selector chunk left = selector chunk right) → left = right)
    (left right : Fin addressCount) :
    (∏ chunk : Fin chunks,
        HonestWitness.oneHot (F := F) (selector chunk left).val
          (selector chunk right).val) =
      HonestWitness.oneHot (F := F) left.val right.val := by
  by_cases addressesEq : left = right
  · subst left
    simp [HonestWitness.oneHot, HonestWitness.fieldBool]
  · have differingChunk :
        ∃ chunk : Fin chunks, selector chunk left ≠ selector chunk right := by
      by_contra noDifferingChunk
      push_neg at noDifferingChunk
      exact addressesEq (jointlyInjective noDifferingChunk)
    rcases differingChunk with ⟨chunk, chunkNe⟩
    have chunkValuesNe :
        (selector chunk left).val ≠ (selector chunk right).val := by
      intro valuesEq
      exact chunkNe (Fin.ext valuesEq)
    have addressValuesNe : left.val ≠ right.val := by
      intro valuesEq
      exact addressesEq (Fin.ext valuesEq)
    rw [Finset.prod_eq_zero (Finset.mem_univ chunk)]
    · simp [HonestWitness.oneHot, HonestWitness.fieldBool,
        addressValuesNe]
    · simp [HonestWitness.oneHot, HonestWitness.fieldBool, chunkValuesNe]

private theorem Nat.nestedChunk
    (value outerShift innerShift outerBits innerBits : Nat)
    (windowFits : innerShift + innerBits ≤ outerBits) :
    ((value / 2 ^ outerShift % 2 ^ outerBits) /
          2 ^ innerShift) % 2 ^ innerBits =
      value / 2 ^ (outerShift + innerShift) % 2 ^ innerBits := by
  have innerShift_le : innerShift ≤ outerBits := by omega
  have innerBits_le : innerBits ≤ outerBits - innerShift := by omega
  have splitBits : innerShift + (outerBits - innerShift) = outerBits := by
    omega
  calc
    ((value / 2 ^ outerShift % 2 ^ outerBits) /
          2 ^ innerShift) % 2 ^ innerBits =
        ((value / 2 ^ outerShift %
              (2 ^ innerShift * 2 ^ (outerBits - innerShift))) /
            2 ^ innerShift) % 2 ^ innerBits := by
          rw [← Nat.pow_add, splitBits]
    _ = ((value / 2 ^ outerShift / 2 ^ innerShift) %
          2 ^ (outerBits - innerShift)) % 2 ^ innerBits := by
          rw [Nat.mod_mul_right_div_self]
    _ = (value / 2 ^ outerShift / 2 ^ innerShift) %
          2 ^ innerBits :=
          Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 innerBits_le)
    _ = value / 2 ^ (outerShift + innerShift) %
          2 ^ innerBits := by
          rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]

private theorem instructionCommittedSelector_shift_eq
    {params : JoltWitnessParams} (valid : params.Valid)
    (virtualChunk : Fin params.instructionVirtualRaCount)
    (localChunk : Fin params.instructionCommittedRaPerVirtual) :
    (params.instructionCommittedSelector
        (valid.instructionCommittedChunk virtualChunk localChunk)).shift =
      (params.instructionVirtualSelector virtualChunk).shift +
        (params.instructionCommittedLocalSelector localChunk).shift := by
  have virtual_lt := virtualChunk.isLt
  have local_lt := localChunk.isLt
  rcases valid.productionChunkPolicy with ⟨committedBits, virtualBits⟩
  by_cases small : params.logT < OneHotChunkThresholdLogT
  · norm_num [JoltWitnessParams.instructionCommittedSelector,
      JoltWitnessParams.instructionVirtualSelector,
      JoltWitnessParams.instructionCommittedLocalSelector,
      JoltWitnessParams.Valid.instructionCommittedChunk,
      JoltWitnessParams.instructionCommittedChunkIndex,
      JoltRaChunkSelector.shift, JoltWitnessParams.instructionCommittedRaCount,
      JoltWitnessParams.instructionVirtualRaCount,
      JoltWitnessParams.instructionCommittedRaPerVirtual,
      JoltWitnessParams.raPolynomialLayout, JoltWitnessParams.ceilDiv,
      JoltWitnessParams.productionCommittedChunkBits,
      JoltWitnessParams.productionLookupVirtualChunkBits,
      committedBits, virtualBits, small, InstructionLookupAddressBits, Xlen]
      at virtual_lt local_lt ⊢
    omega
  · norm_num [JoltWitnessParams.instructionCommittedSelector,
      JoltWitnessParams.instructionVirtualSelector,
      JoltWitnessParams.instructionCommittedLocalSelector,
      JoltWitnessParams.Valid.instructionCommittedChunk,
      JoltWitnessParams.instructionCommittedChunkIndex,
      JoltRaChunkSelector.shift, JoltWitnessParams.instructionCommittedRaCount,
      JoltWitnessParams.instructionVirtualRaCount,
      JoltWitnessParams.instructionCommittedRaPerVirtual,
      JoltWitnessParams.raPolynomialLayout, JoltWitnessParams.ceilDiv,
      JoltWitnessParams.productionCommittedChunkBits,
      JoltWitnessParams.productionLookupVirtualChunkBits,
      committedBits, virtualBits, small, InstructionLookupAddressBits, Xlen]
      at virtual_lt local_lt ⊢
    omega

private theorem instructionCommittedLocalSelector_windowFits
    {params : JoltWitnessParams} (valid : params.Valid)
    (localChunk : Fin params.instructionCommittedRaPerVirtual) :
    (params.instructionCommittedLocalSelector localChunk).shift +
        params.committedChunkBits ≤ params.lookupVirtualChunkBits := by
  have local_lt := localChunk.isLt
  rw [← valid.committedChunksTileVirtualChunk]
  simp only [JoltWitnessParams.instructionCommittedLocalSelector,
    JoltRaChunkSelector.shift]
  have chunksRemaining :
      params.instructionCommittedRaPerVirtual - (localChunk.val + 1) + 1 ≤
        params.instructionCommittedRaPerVirtual := by
    omega
  simpa [Nat.add_mul] using
    Nat.mul_le_mul_right params.committedChunkBits chunksRemaining

/-- A committed instruction selector underneath a virtual chunk extracts the
same bits as first selecting that virtual chunk and then its local subchunk. -/
theorem instructionCommittedSelector_chunk_eq
    {params : JoltWitnessParams} (valid : params.Valid)
    (virtualChunk : Fin params.instructionVirtualRaCount)
    (localChunk : Fin params.instructionCommittedRaPerVirtual)
    (value : Nat) :
    (params.instructionCommittedSelector
        (valid.instructionCommittedChunk virtualChunk localChunk)).chunk value =
      (params.instructionCommittedLocalSelector localChunk).chunk
        ((params.instructionVirtualSelector virtualChunk).chunk value).val := by
  apply Fin.ext
  change
    value /
          2 ^ (params.instructionCommittedSelector
            (valid.instructionCommittedChunk virtualChunk localChunk)).shift %
        2 ^ params.committedChunkBits =
      ((value / 2 ^ (params.instructionVirtualSelector virtualChunk).shift %
            2 ^ params.lookupVirtualChunkBits) /
          2 ^ (params.instructionCommittedLocalSelector localChunk).shift) %
        2 ^ params.committedChunkBits
  rw [Nat.nestedChunk value
    (params.instructionVirtualSelector virtualChunk).shift
    (params.instructionCommittedLocalSelector localChunk).shift
    params.lookupVirtualChunkBits params.committedChunkBits
    (instructionCommittedLocalSelector_windowFits valid localChunk)]
  rw [instructionCommittedSelector_shift_eq valid virtualChunk localChunk]

/-- The committed subchunk selectors recover a complete virtual instruction
chunk. -/
theorem instructionCommittedLocalSelectors_jointly_injective
    {params : JoltWitnessParams} (valid : params.Valid)
    {left right : Fin params.lookupVirtualChunkSize}
    (chunks_eq : ∀ chunk : Fin params.instructionCommittedRaPerVirtual,
      (params.instructionCommittedLocalSelector chunk).chunk left.val =
        (params.instructionCommittedLocalSelector chunk).chunk right.val) :
    left = right := by
  apply Fin.ext
  apply raChunkSelectors_jointly_injective
    valid.committedChunkBitsPositive
  · rw [valid.committedChunksTileVirtualChunk]
    exact left.isLt
  · rw [valid.committedChunksTileVirtualChunk]
    exact right.isLt
  · simpa [JoltWitnessParams.instructionCommittedLocalSelector] using
      chunks_eq

/-- The ceiling-divided committed RAM digits jointly determine a remapped RAM
address; their unused most-significant padding bits are necessarily zero. -/
theorem ramCommittedSelectors_jointly_injective
    {params : JoltWitnessParams} (valid : params.Valid)
    {left right : Fin params.ramK}
    (chunksEq : ∀ chunk : Fin params.ramCommittedRaCount,
      (params.ramCommittedSelector chunk).chunk left.val =
        (params.ramCommittedSelector chunk).chunk right.val) :
    left = right := by
  apply Fin.ext
  apply raChunkSelectors_jointly_injective
    valid.committedChunkBitsPositive
  · apply lt_of_lt_of_le left.isLt
    rw [valid.ramK_eq_two_pow_addressBits]
    exact Nat.pow_le_pow_right (by omega)
      valid.ramAddressBits_le_committedChunks
  · apply lt_of_lt_of_le right.isLt
    rw [valid.ramK_eq_two_pow_addressBits]
    exact Nat.pow_le_pow_right (by omega)
      valid.ramAddressBits_le_committedChunks
  · simpa [JoltWitnessParams.ramCommittedSelector] using chunksEq

/-- Honest committed RAM digits reconstruct the virtual full-address RAM
selector, including the all-zero no-access row. -/
theorem honest_ramCommittedRaProduct_eq_oneHot
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) (address : Fin params.ramK)
    (i : Fin params.traceLength) :
    (honest_witness (F := F) trace).ramCommittedRaProduct address i =
      match HonestWitness.remappedRamAddress trace (trace.rows i) with
      | some ramAddress =>
          HonestWitness.oneHot (F := F) address.val ramAddress
      | none => 0 := by
  let paramsValid := trace.metadataValid.paramsValid
  let row := trace.rows i
  have rowValid :
      JoltTraceRow.Valid trace.metadata.toJoltPublicInputs row
        (trace.preState i) (trace.postState i) := by
    simpa [row, HonestTrace.preState, HonestTrace.postState] using
      trace.rowValid i
  unfold JoltWitness.ramCommittedRaProduct JoltWitness.ramCommittedRa
  simp only [honest_witness]
  change
    (∏ chunk : Fin params.ramCommittedRaCount,
      match HonestWitness.remappedRamAddress trace row with
      | some ramAddress =>
          HonestWitness.oneHot (F := F)
            ((params.ramCommittedSelector chunk).chunk address.val).val
            ((params.ramCommittedSelector chunk).chunk ramAddress).val
      | none => 0) =
      match HonestWitness.remappedRamAddress trace row with
      | some ramAddress =>
          HonestWitness.oneHot (F := F) address.val ramAddress
      | none => 0
  cases remapped : HonestWitness.remappedRamAddress trace row with
  | none =>
      let firstChunk : Fin params.ramCommittedRaCount :=
        ⟨0, paramsValid.ramCommittedRaCountPositive⟩
      rw [Finset.prod_eq_zero (Finset.mem_univ firstChunk)]
      · rfl
  | some ramAddress =>
      have addressBound : ramAddress < params.ramK :=
        rowValid.ramAddressBound ramAddress (by
          simpa [row, HonestWitness.remappedRamAddress] using remapped)
      let selected : Fin params.ramK := ⟨ramAddress, addressBound⟩
      change
        (∏ chunk : Fin params.ramCommittedRaCount,
          HonestWitness.oneHot (F := F)
            ((params.ramCommittedSelector chunk).chunk address.val).val
            ((params.ramCommittedSelector chunk).chunk selected.val).val) =
          HonestWitness.oneHot (F := F) address.val selected.val
      exact product_oneHot_eq_oneHot_of_jointly_injective
        (fun chunk address =>
          (params.ramCommittedSelector chunk).chunk address.val)
        (ramCommittedSelectors_jointly_injective paramsValid)
        address selected

/-- On an honest witness, each virtual instruction-RA cell is the product of
the corresponding contiguous committed instruction-RA cells. -/
theorem honest_instructionCommittedRaProduct_eq_oneHot
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params)
    (virtualChunk : Fin params.instructionVirtualRaCount)
    (address : Fin params.lookupVirtualChunkSize)
    (i : Fin params.traceLength) :
    (honest_witness (F := F) trace).instructionCommittedRaProduct
        virtualChunk address i =
      HonestWitness.oneHot (F := F) address.val
        ((params.instructionVirtualSelector virtualChunk).chunk
          (HonestWitness.lookupIndex (trace.rows i)).toNat).val := by
  let valid := trace.metadataValid.paramsValid
  let selected : Fin params.lookupVirtualChunkSize :=
    (params.instructionVirtualSelector virtualChunk).chunk
      (HonestWitness.lookupIndex (trace.rows i)).toNat
  unfold JoltWitness.instructionCommittedRaProduct
  simp_rw [valid.instructionCommittedChunk?_eq_some]
  change
    (∏ localChunk : Fin params.instructionCommittedRaPerVirtual,
      HonestWitness.oneHot (F := F)
        ((params.instructionCommittedLocalSelector localChunk).chunk
          address.val).val
        ((params.instructionCommittedSelector
          (valid.instructionCommittedChunk virtualChunk localChunk)).chunk
            (HonestWitness.lookupIndex (trace.rows i)).toNat).val) =
      HonestWitness.oneHot (F := F) address.val selected.val
  simp_rw [instructionCommittedSelector_chunk_eq valid virtualChunk]
  change
    (∏ localChunk : Fin params.instructionCommittedRaPerVirtual,
      HonestWitness.oneHot (F := F)
        ((params.instructionCommittedLocalSelector localChunk).chunk
          address.val).val
        ((params.instructionCommittedLocalSelector localChunk).chunk
          selected.val).val) =
      HonestWitness.oneHot (F := F) address.val selected.val
  exact product_oneHot_eq_oneHot_of_jointly_injective
    (fun localChunk address =>
      (params.instructionCommittedLocalSelector localChunk).chunk address.val)
    (instructionCommittedLocalSelectors_jointly_injective valid)
    address selected

/-- The ceiling-divided committed bytecode digits jointly determine a compact
public bytecode index; unused most-significant padding bits remain zero. -/
theorem bytecodeCommittedSelectors_jointly_injective
    {params : JoltWitnessParams} (valid : params.Valid)
    {left right : Fin params.bytecodeK}
    (chunksEq : ∀ chunk : Fin params.bytecodeCommittedRaCount,
      (params.bytecodeCommittedSelector chunk).chunk left.val =
        (params.bytecodeCommittedSelector chunk).chunk right.val) :
    left = right := by
  apply Fin.ext
  apply raChunkSelectors_jointly_injective
    valid.committedChunkBitsPositive
  · apply lt_of_lt_of_le left.isLt
    rw [valid.bytecodeK_eq_two_pow_addressBits]
    exact Nat.pow_le_pow_right (by omega)
      valid.bytecodeAddressBits_le_committedChunks
  · apply lt_of_lt_of_le right.isLt
    rw [valid.bytecodeK_eq_two_pow_addressBits]
    exact Nat.pow_le_pow_right (by omega)
      valid.bytecodeAddressBits_le_committedChunks
  · simpa [JoltWitnessParams.bytecodeCommittedSelector] using chunksEq

/-- Honest committed bytecode digits reconstruct the one-hot selector for the
compact bytecode index read at one cycle. -/
theorem honest_bytecodeRaProduct_eq_oneHot
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) (address : Fin params.bytecodeK)
    (i : Fin params.traceLength) :
    (honest_witness (F := F) trace).bytecodeRaProduct address i =
      HonestWitness.oneHot (F := F) address.val (trace.rowMetadata i).pc := by
  let valid := trace.metadataValid.paramsValid
  have pcBound : (trace.rowMetadata i).pc < params.bytecodeK :=
    (trace.rowValid i).pcBound
  let selected : Fin params.bytecodeK :=
    ⟨(trace.rowMetadata i).pc, pcBound⟩
  unfold JoltWitness.bytecodeRaProduct JoltWitness.bytecodeRa
  change
    (∏ chunk : Fin params.bytecodeCommittedRaCount,
      HonestWitness.oneHot (F := F)
        ((params.bytecodeCommittedSelector chunk).chunk address.val).val
        ((params.bytecodeCommittedSelector chunk).chunk selected.val).val) =
      HonestWitness.oneHot (F := F) address.val selected.val
  exact product_oneHot_eq_oneHot_of_jointly_injective
    (fun chunk address =>
      (params.bytecodeCommittedSelector chunk).chunk address.val)
    (bytecodeCommittedSelectors_jointly_injective valid)
    address selected

/-- An honest bytecode read selects exactly the public table value at the
cycle's compact bytecode index. -/
theorem honest_bytecodeRead_eq_selected
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) (values : Column params.bytecodeK F)
    (i : Fin params.traceLength) :
    (honest_witness (F := F) trace).bytecodeRead values i =
      values ⟨(trace.rowMetadata i).pc, (trace.rowValid i).pcBound⟩ := by
  unfold JoltWitness.bytecodeRead
  rw [show
      (∑ address : Fin params.bytecodeK,
        (honest_witness (F := F) trace).bytecodeRaProduct address i *
          values address) =
        ∑ address : Fin params.bytecodeK,
          HonestWitness.oneHot (F := F) address.val
              (trace.rowMetadata i).pc * values address by
      apply Finset.sum_congr rfl
      intro address _
      rw [honest_bytecodeRaProduct_eq_oneHot]]
  simpa using sum_oneHot_mul
    (⟨(trace.rowMetadata i).pc, (trace.rowValid i).pcBound⟩ :
      Fin params.bytecodeK) values

end JoltConstraints.JoltConstraint.Completeness
