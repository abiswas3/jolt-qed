import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Itype.Family
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Expansions.ALU
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Instructions.VirtualMULI
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Instructions.VirtualSignExtendWord
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.StraightLine

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SLLIW: Jolt VirtualMULI + VSEW = Sail SLLIW

Jolt program sequence:
1. `VirtualMULI rd, rs1, 2^shamt` — multiply by power of two (= left shift)
2. `VirtualSignExtendWord rd, rd` — sign-extend lower 32 bits of `rd`

The bridge `extractLsb_mul_pow2` is specific to SLLIW (scalar shamt)
rather than the R-type variant; kept inline here since no other
instruction reuses it.
-/

private theorem extractLsb_mul_pow2 (v : BitVec 64) (shamt : BitVec 5) :
    Sail.BitVec.extractLsb (v * BitVec.ofNat 64 (2 ^ shamt.toNat)) 31 0 =
    shift_bits_left (Sail.BitVec.extractLsb v 31 0) shamt := by
  unfold shift_bits_left Sail.BitVec.extractLsb
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb, BitVec.toNat_mul, BitVec.toNat_ofNat,
        BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

private theorem slliw_mul_eq_shift (v : BitVec 64) (shamt : BitVec 5) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb (v * BitVec.ofNat 64 (2 ^ shamt.toNat)) 31 0) =
    sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v 31 0) shamt) := by
  rw [extractLsb_mul_pow2]

theorem execute_SHIFTIWOP_SLLIW_factored (shamt : BitVec 5) (rs1 rd : regidx) :
    execute_SHIFTIWOP shamt rs1 rd sopw.SLLIW = (do
      let v ← rX_bits rs1
      wX_bits rd (sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v 31 0) shamt))
      pure RETIRE_SUCCESS) := by
  simp [execute_SHIFTIWOP, bind_pure_comp, pure_bind]

/-- Program-level concrete theorem for `SLLIW`.

The Jolt-ISA program uses `VirtualMULI` with the immediate power of two, then
sign-extends the low word of `rd`. -/
theorem slliwProgram_concrete (shamt : BitVec 5) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v : BitVec 64),
      rX_bits rs1 js.sail = .ok v js.sail ∧
      (JoltISA.execProgram (JoltISA.slliwProgram shamt rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v 31 0) shamt)) := by
  obtain ⟨v, hok⟩ := hwf rs1

  -- Instruction 1: `VirtualMULI rd, rs1, 2^shamt` writes the shifted product to `rd`.
  let multiplier := BitVec.ofNat 64 (2 ^ shamt.toNat)
  let shiftedProduct := jolt_virtual_muli_value v multiplier
  obtain ⟨s_afterMuli, h_virtual_muli_run, h_virtual_muli_write⟩ :=
    JoltISA.exists_state_after_virtual_muli_run_xreg_xreg rd rs1 multiplier js v hok
  have h_muli_writes_shifted_product :
      wX_bits rd shiftedProduct js.sail = .ok () s_afterMuli := by
    simpa only [shiftedProduct, multiplier] using h_virtual_muli_write
  let js_afterMuli : SailJoltState := { sail := s_afterMuli, vregs := js.vregs }
  have h_sail_after_muli :
      js_afterMuli.sail = stateAfterWrite js.sail rd shiftedProduct := by
    simpa only [js_afterMuli, shiftedProduct] using
      wX_bits_eq_stateAfterWrite rd shiftedProduct js.sail s_afterMuli
        h_muli_writes_shifted_product
  have h_virtual_muli_succeeds :
      (JoltISA.execInstr (.VirtualMULI (.xreg rd) (.xreg rs1) multiplier)).run js =
        .ok RETIRE_SUCCESS js_afterMuli := by
    simpa only [js_afterMuli] using h_virtual_muli_run

  have h_rd_reads_shifted_product :
      rX_bits rd s_afterMuli = .ok shiftedProduct s_afterMuli := by
    exact wX_rX_roundtrip rd shiftedProduct js.sail s_afterMuli hrd
      h_muli_writes_shifted_product

  -- Instruction 2: `VirtualSignExtendWord rd, rd` writes the SLLIW result.
  let slliwResult := sign_extend (m := 64) (Sail.BitVec.extractLsb shiftedProduct 31 0)
  have h_slliw_result_eq_sail :
      slliwResult =
        sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v 31 0) shamt) := by
    dsimp only [slliwResult, shiftedProduct, multiplier, jolt_virtual_muli_value]
    rw [slliw_mul_eq_shift v shamt]
  obtain ⟨s_afterSignExtend, h_sign_extend_run, h_sign_extend_write⟩ :=
    JoltISA.exists_state_after_virtual_sign_extend_word_run_xreg_xreg rd rd js_afterMuli
      shiftedProduct (by simpa only [js_afterMuli] using h_rd_reads_shifted_product)
  have h_sign_extend_writes_result :
      wX_bits rd slliwResult s_afterMuli = .ok () s_afterSignExtend := by
    simpa only [js_afterMuli, slliwResult] using h_sign_extend_write

  let js' : SailJoltState := { sail := s_afterSignExtend, vregs := js.vregs }
  have h_sail_after_sign_extend :
      js'.sail = stateAfterWrite js_afterMuli.sail rd slliwResult := by
    simpa only [js', js_afterMuli, slliwResult] using
      wX_bits_eq_stateAfterWrite rd slliwResult s_afterMuli s_afterSignExtend
        h_sign_extend_writes_result
  have h_sign_extend_succeeds :
      (JoltISA.execInstr (.VirtualSignExtendWord (.xreg rd) (.xreg rd))).run js_afterMuli =
        .ok RETIRE_SUCCESS js' := by
    simpa only [js'] using h_sign_extend_run

  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.slliwProgram shamt rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' := by
    unfold JoltISA.slliwProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterMuli h_virtual_muli_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterMuli js' h_sign_extend_succeeds]
    rfl

  have h_sail_final :
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v 31 0) shamt)) := by
    calc
      js'.sail = stateAfterWrite js_afterMuli.sail rd slliwResult :=
        h_sail_after_sign_extend
      _ = stateAfterWrite (stateAfterWrite js.sail rd shiftedProduct) rd slliwResult := by
        rw [h_sail_after_muli]
      _ = stateAfterWrite js.sail rd slliwResult := by
        exact stateAfterWrite_stateAfterWrite rd shiftedProduct slliwResult js.sail
      _ = stateAfterWrite js.sail rd
            (sign_extend (m := 64)
              (shift_bits_left (Sail.BitVec.extractLsb v 31 0) shamt)) := by
        rw [h_slliw_result_eq_sail]

  exact ⟨js', v, hok, h_program_succeeds, h_sail_final⟩

/-- Main program-level equivalence for `SLLIW`. -/
theorem slliwProgram_eq_sail (shamt : BitVec 5) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((JoltISA.execProgram (JoltISA.slliwProgram shamt rs1 rd)).run js) =
    (execute_SHIFTIWOP shamt rs1 rd sopw.SLLIW).run js.sail :=
  itype_eq_sail_uniform
    (f := fun v => sign_extend (m := 64)
      (shift_bits_left (Sail.BitVec.extractLsb v 31 0) shamt))
    (execute_SHIFTIWOP_SLLIW_factored shamt rs1 rd)
    (slliwProgram_concrete shamt rs1 rd hrd js hwf)

end
