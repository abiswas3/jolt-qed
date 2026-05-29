import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.JoltISA.Semantics.Instructions.Add
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualSignExtendWord
import JoltBytecode.JoltISA.Semantics.Instructions

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# ADDW: Jolt ADD + VirtualSignExtendWord = Sail ADDW

Jolt program sequence:
1. `ADD rd, rs1, rs2` — 64-bit add, writes `v1 + v2` to `rd`
2. `VirtualSignExtendWord rd, rd` — sign-extend lower 32 bits of `rd`

Sail's ADDW extracts lower 32 bits of each operand, adds them at 32
bits, and sign-extends to 64. The local value lemma says truncation
distributes over addition, so both sides produce the same result.
-/

abbrev addw_sail_operation (v1 v2 : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64)
    (Sail.BitVec.extractLsb v1 31 0 + Sail.BitVec.extractLsb v2 31 0)

abbrev addw_jolt_val (v1 v2 : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64) (Sail.BitVec.extractLsb (v1 + v2) 31 0)

/-- Factoring: `execute_RTYPEW rs2 rs1 rd ropw.ADDW` reads `rs1`, reads
`rs2`, writes `addw_sail_operation v1 v2` to `rd`, returns
`RETIRE_SUCCESS`. -/
theorem execute_RTYPEW_ADDW_factored
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.ADDW = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (addw_sail_operation v1 v2)
      pure RETIRE_SUCCESS) := by
  simp only [execute_RTYPEW]
  simp only [bind_pure_comp, pure_bind, addw_sail_operation]

/-- `(a + b)[31:0] = a[31:0] + b[31:0]`. -/
private theorem extractLsb_add (a b : BitVec 64) :
    Sail.BitVec.extractLsb (a + b) 31 0 =
    Sail.BitVec.extractLsb a 31 0 + Sail.BitVec.extractLsb b 31 0 := by
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, Nat.add_mod]

/-- Math bridge: the Jolt value `g(f(v1, v2))` equals the Sail ADDW value
`h(v1, v2)`. -/
private theorem addw_value_eq_sail (v1 v2 : BitVec 64) :
    addw_jolt_val v1 v2 = addw_sail_operation v1 v2 := by
  simp only [addw_jolt_val, addw_sail_operation]
  rw [extractLsb_add]

/-- Program-level concrete theorem for `ADDW`.

The new Jolt-ISA program states the Rust-style expansion directly:
architectural `ADD`, followed by the virtual sign-extend-word instruction.
The proof exposes the two real writes and collapses them to the final
sign-extended architectural write. -/
theorem addwProgram_concrete
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (v1 v2 : BitVec 64)
    (h_read_rs1 : rX_bits rs1 js.sail = .ok v1 js.sail)
    (h_read_rs2 : rX_bits rs2 js.sail = .ok v2 js.sail)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ (js' : SailJoltState),
      (JoltISA.execProgram (JoltISA.addwProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd (addw_sail_operation v1 v2) := by

    -- Instruction 1: `ADD rd, rs1, rs2` writes the 64-bit sum to `rd`.
    let sum := v1 + v2
    obtain ⟨js_afterAdd, h_add_reads_rs1, h_add_reads_rs2,
        h_add_writes_sum, h_add_succeeds⟩ :=
      JoltISA.exists_state_after_add_run_xreg_xreg_xreg rd rs1 rs2 js v1 v2
        h_read_rs1 h_read_rs2

    -- Instruction 2: `VirtualSignExtendWord rd, rd` writes the ADDW result.
    let jolt_val := addw_jolt_val v1 v2
    obtain ⟨js_afterSignExtend, h_sign_extend_writes_jolt_val,
        h_sign_extend_succeeds⟩ :=
      JoltISA.exists_state_after_virtual_sign_extend_word_run_xreg_xreg_of_same_register_write
        rd js_afterAdd js.sail sum h_add_writes_sum

    -- Full program succeeds by stepping through the two instruction runs.
    have h_program_succeeds :
        (JoltISA.execProgram (JoltISA.addwProgram rs2 rs1 rd)).run js =
          .ok RETIRE_SUCCESS js_afterSignExtend := by
      unfold JoltISA.addwProgram
      rw [JoltISA.pureWritebackTraceProgram_of_ne_zero hrd]
      rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterAdd h_add_succeeds]
      rw [JoltISA.execProgram_instr_run_retire _ _ js_afterAdd js_afterSignExtend
        h_sign_extend_succeeds]
      rfl

    refine ⟨js_afterSignExtend, h_program_succeeds, ?_⟩

    -- The instruction trace leaves `rd` containing the Jolt ADDW value.
    have h_final_jolt_value :
        js_afterSignExtend.sail = stateAfterWrite js.sail rd jolt_val := by
      exact h_sign_extend_writes_jolt_val

    -- No more execution reasoning remains.
    -- The only real content left is the pure value equality:
    -- Jolt's two-instruction value is Sail's ADDW value.
    have h_addw_value :
        jolt_val = addw_sail_operation v1 v2 := by
      simp only [jolt_val]
      -- NOTE: The core math theorem.
      exact addw_value_eq_sail v1 v2

    -- After the value theorem, the final state claim is mechanical.
    rw [← h_addw_value]
    exact h_final_jolt_value

/-- Rust's ADDW `rd = x0` replacement `ADDI x0, x0, 0` retires successfully
and leaves the projected Sail state unchanged. -/
private theorem addw_rd_zero_noop_concrete
    (rs2 : regidx)
    (rs1 : regidx)
    (js : SailJoltState) :
    (JoltISA.execProgram (JoltISA.addwProgram rs2 rs1 (regidx.Regidx 0))).run js =
      .ok RETIRE_SUCCESS js := by
  unfold JoltISA.addwProgram
  rw [JoltISA.pureWritebackTraceProgram_regidx_zero]
  exact JoltISA.pureWritebackRdZeroProgram_run js

/-- Main program-level equivalence for `ADDW`. -/
theorem addwProgram_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (v1 v2 : BitVec 64)
    (h_read_rs1 : rX_bits rs1 js.sail = .ok v1 js.sail)
    (h_read_rs2 : rX_bits rs2 js.sail = .ok v2 js.sail) :
    projectResult ((JoltISA.execProgram (JoltISA.addwProgram rs2 rs1 rd)).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.ADDW).run js.sail := by
  by_cases hrd : rd = regidx.Regidx 0
  · subst rd
    rw [addw_rd_zero_noop_concrete rs2 rs1 js]
    simp only [projectResult, project]
    rw [execute_RTYPEW_ADDW_factored rs2 rs1 (regidx.Regidx 0)]
    simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
    simp only [h_read_rs1, h_read_rs2]
    simp only [wX_bits_regidx_zero]

  obtain ⟨js_afterSignExtend, h_program_succeeds, h_final_sail⟩ :=
    addwProgram_concrete rs2 rs1 rd js v1 v2 h_read_rs1 h_read_rs2 hrd

  -- Use the concrete proof to collapse the Jolt side to its final Sail state.
  rw [h_program_succeeds]
  simp only [projectResult, project]
  rw [h_final_sail]

  -- Expand the Sail-side `ADDW`: it reads the same inputs and writes the same
  -- already-proved final value.
  rw [execute_RTYPEW_ADDW_factored rs2 rs1 rd]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  simp only [h_read_rs1, h_read_rs2]

  -- The only remaining mismatch is the concrete state chosen by `wX_bits`
  -- versus our `stateAfterWrite` spelling of that same register update.
  obtain ⟨s', h_write⟩ := wX_shape rd (addw_sail_operation v1 v2) js.sail
  simp only [h_write]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd (addw_sail_operation v1 v2) js.sail s' h_write).symm

end
