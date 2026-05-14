import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Itype.Family
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Expansions.ALU
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.StraightLine

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SLLIW: Jolt VirtualMULI + VSEW = Sail SLLIW

Jolt decomposes SLLIW as:
1. `VirtualMULI rd, rs1, 2^shamt` — multiply by power of two (= left shift)
2. `VirtualSignExtendWord rd`

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
  let imm := BitVec.ofNat 64 (2 ^ shamt.toNat)
  let raw := jolt_virtual_muli_value v imm
  obtain ⟨s_raw, hw_raw⟩ := wX_shape rd raw js.sail
  let js_raw : SailJoltState := { sail := s_raw, vregs := js.vregs }
  have hmuli :
      (JoltISA.execInstr (.VirtualMULI (.xreg rd) (.xreg rs1) imm)).run js =
        .ok RETIRE_SUCCESS js_raw := by
    simpa [js_raw, raw] using
      (JoltISA.execInstr_virtualMULI_xreg_xreg_run rd rs1 imm
        js v s_raw hok hw_raw)
  have hread_rd : rX_bits rd js_raw.sail = .ok raw js_raw.sail := by
    simpa [js_raw] using (wX_rX_roundtrip rd raw js.sail s_raw hrd hw_raw)
  let final := sign_extend (m := 64) (Sail.BitVec.extractLsb raw 31 0)
  obtain ⟨s_final, hw_final⟩ := wX_shape rd final js_raw.sail
  let js' : SailJoltState := { sail := s_final, vregs := js.vregs }
  have hsextw :
      (JoltISA.execInstr (.VirtualSignExtendWord (.xreg rd) (.xreg rd))).run js_raw =
        .ok RETIRE_SUCCESS js' := by
    simpa [js', final] using
      (JoltISA.execInstr_sextw_xreg_xreg_run rd rd js_raw raw s_final
        hread_rd hw_final)
  refine ⟨js', v, hok, ?_, ?_⟩
  · unfold JoltISA.slliwProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_raw hmuli]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_raw js' hsextw]
    rfl
  · dsimp [js']
    have hc := wX_wX_collapse rd raw final js.sail s_raw s_final hw_raw hw_final
    rw [wX_bits_eq_stateAfterWrite rd _ js.sail s_final hc]
    dsimp [final, raw, imm, jolt_virtual_muli_value]
    rw [slliw_mul_eq_shift v shamt]

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
