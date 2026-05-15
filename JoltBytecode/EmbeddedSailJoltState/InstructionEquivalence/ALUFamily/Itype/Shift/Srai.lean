import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Itype.Family
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Expansions.ALU
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Instructions.VirtualSRAI
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.StraightLine
import JoltBytecode.EmbeddedSailJoltState.ShiftDefs

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SRAI: Jolt VirtualSRAI via bitmask = Sail SRAI

Jolt program sequence:
1. `VirtualSRAI rd, rs1, sraiBitmask shamt` — arithmetic right shift by `ctz(bitmask)`
-/

def srai_bitmask (shamt : BitVec 64) : Nat :=
  let shift := (shamt.setWidth 6).toNat
  let ones := (1 <<< (64 - shift)) - 1
  ones <<< shift

lemma ctz_srai_bitmask (shamt : BitVec 64) :
    ctz (srai_bitmask shamt) = (shamt.setWidth 6).toNat := by
  unfold srai_bitmask
  simp only [Nat.shiftLeft_eq, one_mul]
  set shift := (shamt.setWidth 6).toNat
  have h_lt : shift < 64 := by have := (shamt.setWidth 6).isLt; norm_num at this; exact this
  have h_diff_pos : 0 < 64 - shift := by omega
  have h_m_pos : 0 < 2 ^ (64 - shift) - 1 := by
    have : 2 ≤ 2 ^ (64 - shift) :=
      le_trans (show (2 : Nat) ≤ 2 ^ 1 from by norm_num) (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  rw [mul_comm, ctz_mul_pow2 shift h_m_pos, ctz_of_odd (pow2_sub_one_odd h_diff_pos)]; omega

private lemma srai_bitmask_eq_arith_shift (v : BitVec 64) (shamt : BitVec 6) :
    v.sshiftRight (ctz (srai_bitmask (shamt.setWidth 64))) =
    shift_bits_right_arith v (Sail.BitVec.extractLsb shamt 5 0) := by
  unfold shift_bits_right_arith
  simp [Sail.BitVec.toNatInt, Sail.BitVec.extractLsb, ctz_srai_bitmask]
  congr 1; omega

/-- Widening a six-bit immediate to a machine word and truncating it back to
six bits is identity. -/
private theorem setWidth_6_roundtrip (shamt : BitVec 6) :
    (shamt.setWidth 64).setWidth 6 = shamt := by
  ext i; simp

/-- The program-level immediate bitmask matches the local bitvector
definition after widening the six-bit shift amount to a machine word. -/
private theorem sraiProgram_bitmask_eq (shamt : BitVec 6) :
    JoltISA.sraiBitmask shamt = srai_bitmask (shamt.setWidth 64) := by
  unfold JoltISA.sraiBitmask JoltISA.srliBitmask srai_bitmask
  rw [setWidth_6_roundtrip]

abbrev srai_sail_operation (shamt : BitVec 6) (v : BitVec 64) : BitVec 64 :=
  shift_bits_right_arith v (Sail.BitVec.extractLsb shamt 5 0)

abbrev srai_jolt_val (shamt : BitVec 6) (v : BitVec 64) : BitVec 64 :=
  jolt_virtual_srai_value v (JoltISA.sraiBitmask shamt)

private theorem srai_value_eq_sail (shamt : BitVec 6) (v : BitVec 64) :
    srai_jolt_val shamt v = srai_sail_operation shamt v := by
  simp only [srai_jolt_val, srai_sail_operation, jolt_virtual_srai_value]
  rw [sraiProgram_bitmask_eq]
  exact srai_bitmask_eq_arith_shift v shamt

theorem execute_SHIFTIOP_SRAI_factored (shamt : BitVec 6) (rs1 rd : regidx) :
  execute_SHIFTIOP shamt rs1 rd sop.SRAI = (do
      let v ← rX_bits rs1
      wX_bits rd (srai_sail_operation shamt v)
      pure RETIRE_SUCCESS) := by
  simp [execute_SHIFTIOP, LeanRV64D.Functions.log2_xlen, srai_sail_operation, bind_pure_comp]

/-- Program-level concrete theorem for `SRAI`.

The Jolt-ISA program contains `VirtualSRAI` with the encoded bitmask
immediate.  The local bridge lemma turns that encoding back into Sail's
ordinary arithmetic shift. -/
theorem sraiProgram_concrete (shamt : BitVec 6) (rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v : BitVec 64),
      rX_bits rs1 js.sail = .ok v js.sail ∧
      (JoltISA.execProgram (JoltISA.sraiProgram shamt rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd (srai_sail_operation shamt v) := by
  obtain ⟨v, hok⟩ := hwf rs1

  -- Instruction 1: `VirtualSRAI rd, rs1, sraiBitmask shamt` writes the shifted result to `rd`.
  let bitmask := JoltISA.sraiBitmask shamt
  let jolt_val := srai_jolt_val shamt v
  obtain ⟨js_afterSrai, h_srai_reads_rs1, h_srai_writes_jolt_val,
      h_srai_succeeds⟩ :=
    JoltISA.exists_jolt_state_after_virtual_srai_run_xreg_xreg rd rs1 bitmask js v hok

  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.sraiProgram shamt rs1 rd)).run js =
        .ok RETIRE_SUCCESS js_afterSrai := by
    unfold JoltISA.sraiProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterSrai h_srai_succeeds]
    rfl

  refine ⟨js_afterSrai, v, h_srai_reads_rs1, h_program_succeeds, ?_⟩

  -- The instruction trace leaves `rd` containing the Jolt SRAI value.
  have h_final_jolt_value :
      js_afterSrai.sail = stateAfterWrite js.sail rd jolt_val := by
    simp only [jolt_val, srai_jolt_val]
    exact h_srai_writes_jolt_val

  -- No more execution reasoning remains.
  -- The only real content left is the pure value equality:
  -- Jolt's bitmask immediate is Sail's SRAI value.
  have h_srai_value :
      jolt_val = srai_sail_operation shamt v := by
    simp only [jolt_val]
    -- NOTE: The core math theorem.
    exact srai_value_eq_sail shamt v

  -- After the value theorem, the final state claim is mechanical.
  rw [← h_srai_value]
  exact h_final_jolt_value

/-- Main program-level equivalence for `SRAI`. -/
theorem sraiProgram_eq_sail (shamt : BitVec 6) (rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((JoltISA.execProgram (JoltISA.sraiProgram shamt rs1 rd)).run js) =
    (execute_SHIFTIOP shamt rs1 rd sop.SRAI).run js.sail := by
  obtain ⟨js_afterSrai, v, h_read_rs1, h_program_succeeds, h_final_sail⟩ :=
    sraiProgram_concrete shamt rs1 rd js hwf

  rw [h_program_succeeds]
  simp only [projectResult, project]
  rw [h_final_sail]

  rw [execute_SHIFTIOP_SRAI_factored shamt rs1 rd]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  simp only [h_read_rs1]

  obtain ⟨s', h_write⟩ := wX_shape rd (srai_sail_operation shamt v) js.sail
  simp only [h_write]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd (srai_sail_operation shamt v) js.sail s' h_write).symm

end
