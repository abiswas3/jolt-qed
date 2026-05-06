import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.Shift.Family
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Expansions.ALU
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Compatibility
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.StraightLine

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SLL: Jolt VirtualPow2 + MUL = Sail SLL

Jolt decomposes SLL as (from `BytecodeExpansions/Sll.lean`):
1. `VirtualPow2 rs2 → v_pow` — compute `2^(rs2[5:0])`
2. `MUL rd, rs1, v_pow` — multiply by power of two (= left shift)

Multiply-by-`2^s` = left-shift-by-`s`; the bridge fact is inlined here
because it is SLL-specific (not shared with other shift instructions).
-/

private theorem setWidth_eq_extractLsb (v : BitVec 64) :
    v.setWidth 6 = Sail.BitVec.extractLsb v (LeanRV64D.Functions.log2_xlen -i 1) 0 := by
  unfold LeanRV64D.Functions.log2_xlen Sail.BitVec.extractLsb
  ext i
  simp [BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb]

private theorem mul_pow2_eq_shiftLeft (v : BitVec 64) (s : BitVec 6) :
    v * BitVec.ofNat 64 (2 ^ s.toNat) = v <<< s := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

private theorem sll_mul_eq_shift (v1 v2 : BitVec 64) :
    v1 * BitVec.ofNat 64 (2 ^ (v2.setWidth 6).toNat) =
    shift_bits_left v1 (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0) := by
  unfold shift_bits_left
  rw [← setWidth_eq_extractLsb]
  exact mul_pow2_eq_shiftLeft v1 (v2.setWidth 6)

theorem execute_RTYPE_SLL_factored (rs2 rs1 rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SLL = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (shift_bits_left v1 (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0))
      pure RETIRE_SUCCESS) := by
  simp [execute_RTYPE, bind_pure_comp]

/-- Program-level concrete theorem for `SLL`.

The explicit Jolt-ISA program first writes `VirtualPow2 rs2` to scratch `v0`,
then multiplies `rs1` by that scratch value.  The arithmetic bridge below
identifies multiplication by `2^rs2[5:0]` with Sail's left shift. -/
theorem sllProgram_concrete (rs2 rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v1 v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      rX_bits rs2 js.sail = .ok v2 js.sail ∧
      (JoltISA.execProgram (JoltISA.sllProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (shift_bits_left v1 (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0)) := by
  obtain ⟨v1, hok1⟩ := hwf rs1
  obtain ⟨v2, hok2⟩ := hwf rs2
  let vp := BitVec.ofNat 64 (2 ^ (v2.setWidth 6).toNat)
  obtain ⟨s', hw⟩ := wX_shape rd (v1 * vp) js.sail
  let js_pow : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (0 : JoltISA.VReg) then vp else js.vregs r }
  let js' : SailJoltState := { sail := s', vregs := js_pow.vregs }
  have hpow :
      (JoltISA.execInstr (.VirtualPow2 (.vreg 0) (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js_pow := by
    simpa [js_pow, vp, jolt_virtual_pow2_value] using
      (JoltISA.execInstr_virtualPow2_xreg_vreg_run (0 : JoltISA.VReg) rs2 js v2 hok2)
  have hmul :
      (JoltISA.execInstr (.MUL (.xreg rd) (.xreg rs1) (.vreg 0))).run js_pow =
        .ok RETIRE_SUCCESS js' := by
    have hread : rX_bits rs1 js_pow.sail = .ok v1 js_pow.sail := by
      simpa [js_pow] using hok1
    have hwrite : wX_bits rd (v1 * js_pow.vregs (0 : JoltISA.VReg)) js_pow.sail =
        .ok () s' := by
      simpa [js_pow, vp] using hw
    simpa [js'] using
      (JoltISA.execInstr_mul_xreg_xreg_vreg_run rd rs1 (0 : JoltISA.VReg)
        js_pow v1 s' hread hwrite)
  refine ⟨js', v1, v2, hok1, hok2, ?_, ?_⟩
  · unfold JoltISA.sllProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_pow hpow]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_pow js' hmul]
    rfl
  · dsimp [js']
    rw [← sll_mul_eq_shift v1 v2]
    exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

/-- Main program-level equivalence for `SLL`. -/
theorem sllProgram_eq_sail (rs2 rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((JoltISA.execProgram (JoltISA.sllProgram rs2 rs1 rd)).run js) =
    (execute_RTYPE rs2 rs1 rd rop.SLL).run js.sail :=
  rtype_eq_sail_uniform
    (f := fun v1 v2 => shift_bits_left v1
      (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0))
    (execute_RTYPE_SLL_factored rs2 rs1 rd)
    (sllProgram_concrete rs2 rs1 rd js hwf)

end
