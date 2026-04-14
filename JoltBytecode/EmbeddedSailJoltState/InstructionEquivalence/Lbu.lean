import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Lb

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

/-!
# LBU: Jolt load-byte (unsigned) decomposition = Sail LBU

From `tracer/src/instruction/lbu.rs::inline_sequence_64`. Identical to LB
except the final arithmetic right shift (SRAI) is replaced by a logical
right shift (SRLI), yielding zero-extension instead of sign-extension.

Sail: `execute_LOAD imm rs1 rd true 1`.
-/

def jolt_lbu (imm : BitVec 12) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let base ← liftSail (rX_bits rs1)
  let ea := base + sign_extend (m := 64) imm
  writeVReg 0 ea
  let v0 ← readVReg 0
  writeVReg 1 (v0 &&& (-8 : BitVec 64))
  let v1 ← readVReg 1
  match ← jolt_load_dword (Virtaddr v1) 1 with
  | .Err e => pure e
  | .Ok () =>
      let v0 ← readVReg 0
      writeVReg 0 (v0 ^^^ (7 : BitVec 64))
      let v0 ← readVReg 0
      writeVReg 0 (v0 <<< 3)
      let v1 ← readVReg 1
      let v0 ← readVReg 0
      writeVReg 1 (v1 <<< (v0.setWidth 6).toNat)
      let v1 ← readVReg 1
      liftSail (wX_bits rd (v1 >>> 56))
      pure RETIRE_SUCCESS

theorem execute_LBU_reduces (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js)
    (v : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok v js.sail) :
    (execute_LOAD imm rs1 rd true 1).run js.sail =
    .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd
        (zero_extend (m := 64)
          (loaded_byte_at js.sail (v + sign_extend (m := 64) imm)))) := by
  sorry

theorem jolt_lbu_concrete (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js)
    (v : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok v js.sail) :
    ∃ js' : SailJoltState,
      (jolt_lbu imm rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (zero_extend (m := 64)
          (loaded_byte_at js.sail (v + sign_extend (m := 64) imm))) := by
  sorry

theorem jolt_lbu_eq_sail (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_lbu imm rs1 rd).run js) =
    (execute_LOAD imm rs1 rd true 1).run js.sail := by
  obtain ⟨v, hrx⟩ := hwf rs1
  obtain ⟨js', hjolt, hjolt_sail⟩ :=
    jolt_lbu_concrete imm rs1 rd hrd js hwf v hrx
  have hsail := execute_LBU_reduces imm rs1 rd js hwf v hrx
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail, hsail]

end
