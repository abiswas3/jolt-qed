import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.Family
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Expansions.ALU
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Instructions.Mul
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Instructions.VirtualPow2
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.StraightLine
import JoltBytecode.EmbeddedSailJoltState.ShiftDefs

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SLL: Jolt VirtualPow2 + MUL = Sail SLL

Jolt program sequence:
1. `VirtualPow2 v0, rs2` — compute `2^(rs2[5:0])`
2. `MUL rd, rs1, v0` — multiply by power of two

Multiply-by-`2^s` = left-shift-by-`s`; the bridge fact is inlined here
because it is SLL-specific (not shared with other shift instructions).
-/

private theorem setWidth_eq_extractLsb
    (v : BitVec 64) :
    v.setWidth 6 = Sail.BitVec.extractLsb v (LeanRV64D.Functions.log2_xlen -i 1) 0 := by
  unfold Sail.BitVec.extractLsb
  ext i hi
  simp only [BitVec.getElem_setWidth]
  change v.getLsbD i =
    (BitVec.extractLsb (LeanRV64D.Functions.log2_xlen -i 1) 0 v).getLsbD i
  simp only [BitVec.getLsbD_extractLsb]
  have hlt : i < (LeanRV64D.Functions.log2_xlen -i 1) - 0 + 1 := by
    norm_num [LeanRV64D.Functions.log2_xlen] at hi ⊢
    omega
  simp only [hlt, decide_true, Bool.true_and, Nat.zero_add]

private theorem mul_pow2_eq_shiftLeft
    (v : BitVec 64)
    (s : BitVec 6) :
    v * BitVec.ofNat 64 (2 ^ s.toNat) = v <<< s := by
  exact (shiftLeft_eq_mul_pow2 v s.toNat).symm

private theorem sll_mul_eq_shift
    (v1 : BitVec 64)
    (v2 : BitVec 64) :
    v1 * BitVec.ofNat 64 (2 ^ (v2.setWidth 6).toNat) =
    shift_bits_left v1 (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0) := by
  unfold shift_bits_left
  rw [← setWidth_eq_extractLsb]
  exact mul_pow2_eq_shiftLeft v1 (v2.setWidth 6)

theorem execute_RTYPE_SLL_factored
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SLL = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (shift_bits_left v1 (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0))
      pure RETIRE_SUCCESS) := by
  simp only [execute_RTYPE]
  simp only [bind_pure_comp]
  simp only [map_eq_pure_bind]
  simp only [bind_assoc]
  simp only [pure_bind]

/-- Program-level concrete theorem for `SLL`.

The explicit Jolt-ISA program first writes `VirtualPow2 rs2` to scratch `v0`,
then multiplies `rs1` by that scratch value.  The arithmetic bridge below
identifies multiplication by `2^rs2[5:0]` with Sail's left shift. -/
theorem sllProgram_concrete
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v1 v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      rX_bits rs2 js.sail = .ok v2 js.sail ∧
      (JoltISA.execProgram (JoltISA.sllProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (shift_bits_left v1 (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0)) := by
  obtain ⟨v1, hok1⟩ := hwf rs1
  obtain ⟨v2, hok2⟩ := hwf rs2

  -- Instruction 1: `VirtualPow2 v0, rs2` writes `2 ^ rs2[5:0]` to `v0`.
  let pow2 := jolt_virtual_pow2_value v2
  let js_afterPow2 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (0 : JoltISA.VReg) then pow2 else js.vregs r }
  have h_pow2_succeeds :
      (JoltISA.execInstr (.VirtualPow2 (.vreg 0) (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js_afterPow2 := by
    simpa only [js_afterPow2, pow2] using
      (JoltISA.virtual_pow2_run_vreg_xreg (0 : JoltISA.VReg) rs2 js v2 hok2)

  -- Instruction 2: `MUL rd, rs1, v0` writes the shifted result to `rd`.
  let shiftedResult := v1 * pow2
  have h_rs1_reads_v1_after_pow2 :
      rX_bits rs1 js_afterPow2.sail = .ok v1 js_afterPow2.sail := by
    simpa only [js_afterPow2] using hok1
  obtain ⟨s_afterMul, h_mul_run, h_mul_write⟩ :=
    JoltISA.exists_state_after_mul_run_xreg_xreg_vreg rd rs1 (0 : JoltISA.VReg)
      js_afterPow2 v1 h_rs1_reads_v1_after_pow2
  have h_mul_writes_shifted_result :
      wX_bits rd shiftedResult js.sail = .ok () s_afterMul := by
    simpa only [js_afterPow2, shiftedResult, pow2] using h_mul_write
  let js' : SailJoltState := { sail := s_afterMul, vregs := js_afterPow2.vregs }
  have h_mul_succeeds :
      (JoltISA.execInstr (.MUL (.xreg rd) (.xreg rs1) (.vreg 0))).run js_afterPow2 =
        .ok RETIRE_SUCCESS js' := by
    simpa only [js'] using h_mul_run

  -- Math bridge: the Jolt multiply-by-power-of-two value is Sail SLL.
  have h_shifted_result_eq_sail :
      shiftedResult =
        shift_bits_left v1
          (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0) := by
    dsimp only [shiftedResult, pow2, jolt_virtual_pow2_value]
    rw [sll_mul_eq_shift]

  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.sllProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' := by
    unfold JoltISA.sllProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterPow2 h_pow2_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterPow2 js' h_mul_succeeds]
    rfl

  have h_sail_final :
      js'.sail = stateAfterWrite js.sail rd
        (shift_bits_left v1
          (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0)) := by
    calc
      js'.sail = stateAfterWrite js.sail rd shiftedResult := by
        simpa only [js'] using
          wX_bits_eq_stateAfterWrite rd shiftedResult js.sail s_afterMul
            h_mul_writes_shifted_result
      _ = stateAfterWrite js.sail rd
            (shift_bits_left v1
              (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0)) := by
        rw [h_shifted_result_eq_sail]

  exact ⟨js', v1, v2, hok1, hok2, h_program_succeeds, h_sail_final⟩

/-- Main program-level equivalence for `SLL`. -/
theorem sllProgram_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (hwf : WellFormed js) :
    projectResult ((JoltISA.execProgram (JoltISA.sllProgram rs2 rs1 rd)).run js) =
    (execute_RTYPE rs2 rs1 rd rop.SLL).run js.sail :=
  rtype_eq_sail_uniform
    (f := fun v1 v2 => shift_bits_left v1
      (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0))
    (execute_RTYPE_SLL_factored rs2 rs1 rd)
    (sllProgram_concrete rs2 rs1 rd js hwf)

end
