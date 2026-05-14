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

  -- Instruction 1: `VirtualPow2 v0, rs2` writes `vp = 2 ^ rs2[5:0]` to `v0`.
  let vp := jolt_virtual_pow2_value v2
  let js_pow : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (0 : JoltISA.VReg) then vp else js.vregs r }
  have instr1_VirtualPow2_writes_vp :
      (JoltISA.execInstr (.VirtualPow2 (.vreg 0) (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js_pow := by
    simpa [js_pow, vp] using
      (JoltISA.execInstr_virtualPow2_xreg_vreg_run (0 : JoltISA.VReg) rs2 js v2 hok2)

  -- Instruction 2: `MUL rd, rs1, v0` writes `raw = v1 * vp` to `rd`.
  let raw := v1 * vp
  have hread_rs1_from_pow : rX_bits rs1 js_pow.sail = .ok v1 js_pow.sail := by
    simpa [js_pow] using hok1
  obtain ⟨s', hrun_MUL, hw_raw_mul⟩ :=
    JoltISA.execInstr_mul_xreg_xreg_vreg_run_of_read rd rs1 (0 : JoltISA.VReg)
      js_pow v1 hread_rs1_from_pow
  have hw_raw : wX_bits rd raw js.sail = .ok () s' := by
    simpa [js_pow, raw, vp] using hw_raw_mul
  let js' : SailJoltState := { sail := s', vregs := js_pow.vregs }
  have instr2_MUL_writes_raw :
      (JoltISA.execInstr (.MUL (.xreg rd) (.xreg rs1) (.vreg 0))).run js_pow =
        .ok RETIRE_SUCCESS js' := by
    simpa [js'] using hrun_MUL
  refine ⟨js', v1, v2, hok1, hok2, ?_, ?_⟩
  · unfold JoltISA.sllProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_pow instr1_VirtualPow2_writes_vp]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_pow js' instr2_MUL_writes_raw]
    rfl
  · dsimp [js']
    -- NOTE: Math theorem: `sll_mul_eq_shift` matches pow2 multiplication with Sail SLL.
    have math_raw_shift :
        raw =
          shift_bits_left v1
            (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0) := by
      dsimp [raw, vp, jolt_virtual_pow2_value]
      rw [sll_mul_eq_shift]
    have final_write_from_initial :
        wX_bits rd
          (shift_bits_left v1
            (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0))
          js.sail = .ok () s' := by
      rw [← math_raw_shift]
      exact hw_raw
    exact wX_bits_eq_stateAfterWrite rd _ js.sail s' final_write_from_initial

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
