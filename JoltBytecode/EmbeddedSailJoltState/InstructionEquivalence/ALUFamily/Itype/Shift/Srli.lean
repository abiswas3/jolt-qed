import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Itype.Family
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Expansions.ALU
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Instructions.VirtualSRLI
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.StraightLine
import JoltBytecode.EmbeddedSailJoltState.ShiftDefs

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SRLI: Jolt VirtualSRLI via bitmask = Sail SRLI

Jolt program sequence:
1. `VirtualSRLI rd, rs1, srliBitmask shamt` — logical right shift by `ctz(bitmask)`
-/

def srli_bitmask (shamt : BitVec 64) : Nat :=
  let shift := (shamt.setWidth 6).toNat
  let ones := (1 <<< (64 - shift)) - 1
  ones <<< shift

theorem ctz_srli_bitmask (shamt : BitVec 64) :
    ctz (srli_bitmask shamt) = (shamt.setWidth 6).toNat := by
  unfold srli_bitmask
  simp only [Nat.shiftLeft_eq, one_mul]
  set shift := (shamt.setWidth 6).toNat
  have h_lt : shift < 64 := by have := (shamt.setWidth 6).isLt; norm_num at this; exact this
  have h_diff_pos : 0 < 64 - shift := by omega
  have h_m_pos : 0 < 2 ^ (64 - shift) - 1 := by
    have : 2 ≤ 2 ^ (64 - shift) :=
      le_trans (show (2 : Nat) ≤ 2 ^ 1 from by norm_num) (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  rw [mul_comm, ctz_mul_pow2 shift h_m_pos, ctz_of_odd (pow2_sub_one_odd h_diff_pos)]; omega

private theorem extractLsb_shamt6_id (shamt : BitVec 6) :
    Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0 = shamt := by
  simp only [LeanRV64D.Functions.log2_xlen, Sail.BitVec.extractLsb]
  ext i; simp; rfl

private theorem setWidth_roundtrip (shamt : BitVec 6) :
  (shamt.setWidth 64).setWidth 6 = shamt := by
  ext i; simp

private theorem ushiftRight_nat_eq_bv (v : BitVec 64) (s : BitVec 6) :
    v >>> s.toNat = v >>> s := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight]

private theorem srli_bitmask_eq_shift (v : BitVec 64) (shamt : BitVec 6) :
    v >>> ctz (srli_bitmask (shamt.setWidth 64)) =
    shift_bits_right v (Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0) := by
  unfold shift_bits_right
  rw [extractLsb_shamt6_id, ctz_srli_bitmask, setWidth_roundtrip]
  exact ushiftRight_nat_eq_bv v shamt

/-- The program-level immediate bitmask matches the local bitvector
definition after widening the six-bit shift amount to a machine word. -/
private theorem srliProgram_bitmask_eq (shamt : BitVec 6) :
    JoltISA.srliBitmask shamt = srli_bitmask (shamt.setWidth 64) := by
  unfold JoltISA.srliBitmask srli_bitmask
  rw [setWidth_roundtrip]

theorem execute_SHIFTIOP_SRLI_factored (shamt : BitVec 6) (rs1 rd : regidx) :
    execute_SHIFTIOP shamt rs1 rd sop.SRLI = (do
      let v ← rX_bits rs1
      wX_bits rd (shift_bits_right v (Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0))
      pure RETIRE_SUCCESS) := by
  simp [execute_SHIFTIOP, bind_pure_comp]

/-- Program-level concrete theorem for `SRLI`.

The Jolt-ISA program contains the real emitted operation: `VirtualSRLI` with
an encoded bitmask immediate.  The bridge lemma above converts that bitmask
back into Sail's ordinary logical shift amount. -/
theorem srliProgram_concrete (shamt : BitVec 6) (rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v : BitVec 64),
      rX_bits rs1 js.sail = .ok v js.sail ∧
      (JoltISA.execProgram (JoltISA.srliProgram shamt rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (shift_bits_right v
          (Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0)) := by
  obtain ⟨v, hok⟩ := hwf rs1

  -- Instruction 1: `VirtualSRLI rd, rs1, srliBitmask shamt` writes the shifted result to `rd`.
  let bitmask := JoltISA.srliBitmask shamt
  let shiftedResult := jolt_virtual_srli_value v bitmask
  obtain ⟨s_afterSrli, h_virtual_srli_run, h_virtual_srli_write⟩ :=
    JoltISA.exists_state_after_virtual_srli_run_xreg_xreg rd rs1 bitmask js v hok
  let js' : SailJoltState := { sail := s_afterSrli, vregs := js.vregs }
  have h_virtual_srli_succeeds :
      (JoltISA.execInstr (.VirtualSRLI (.xreg rd) (.xreg rs1) bitmask)).run js =
        .ok RETIRE_SUCCESS js' := by
    simpa only [js'] using h_virtual_srli_run

  -- Math bridge: the immediate bitmask decodes to Sail SRLI.
  have h_shifted_result_eq_sail :
      shiftedResult =
        shift_bits_right v
          (Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0) := by
    simpa only [shiftedResult, bitmask, jolt_virtual_srli_value, srliProgram_bitmask_eq] using
      srli_bitmask_eq_shift v shamt

  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.srliProgram shamt rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' := by
    unfold JoltISA.srliProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js' h_virtual_srli_succeeds]
    rfl

  have h_sail_final :
      js'.sail = stateAfterWrite js.sail rd
        (shift_bits_right v
          (Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0)) := by
    calc
      js'.sail = stateAfterWrite js.sail rd shiftedResult := by
        simpa only [js'] using
          wX_bits_eq_stateAfterWrite rd shiftedResult js.sail s_afterSrli
            h_virtual_srli_write
      _ = stateAfterWrite js.sail rd
            (shift_bits_right v
              (Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0)) := by
        rw [h_shifted_result_eq_sail]

  exact ⟨js', v, hok, h_program_succeeds, h_sail_final⟩

/-- Main program-level equivalence for `SRLI`. -/
theorem srliProgram_eq_sail (shamt : BitVec 6) (rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((JoltISA.execProgram (JoltISA.srliProgram shamt rs1 rd)).run js) =
    (execute_SHIFTIOP shamt rs1 rd sop.SRLI).run js.sail :=
  itype_eq_sail_uniform
    (f := fun v => shift_bits_right v
      (Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0))
    (execute_SHIFTIOP_SRLI_factored shamt rs1 rd)
    (srliProgram_concrete shamt rs1 rd js hwf)

end
