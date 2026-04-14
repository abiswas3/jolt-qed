import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Lw

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

/-!
# LH: Jolt load-halfword (signed) decomposition = Sail LH

From `tracer/src/instruction/lh.rs::inline_sequence_64`:

    VirtualAssertHalfwordAlignment rs1, imm
    ADDI  v0, rs1, imm
    ANDI  v1, v0, -8
    LD    v1, v1, 0
    XORI  v0, v0, 6
    SLLI  v0, v0, 3
    SLL   v1, v1, v0
    SRAI  rd, v1, 48

Sail: `execute_LOAD imm rs1 rd false 2`.
-/

-- Placeholder: the 16-bit halfword at a given vaddr. Shared with LHU.
def loaded_halfword_at (_s : SailState) (_vaddr : BitVec 64) : BitVec 16 := 0

def jolt_lh (imm : BitVec 12) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let base ← liftSail (rX_bits rs1)
  let ea := base + sign_extend (m := 64) imm
  if ea &&& 1 ≠ 0 then
    throw (Error.Assertion "LH: effective address not halfword-aligned")
  else do
    writeVReg 0 ea
    let v0 ← readVReg 0
    writeVReg 1 (v0 &&& (-8 : BitVec 64))
    let v1 ← readVReg 1
    match ← jolt_load_dword (Virtaddr v1) 1 with
    | .Err e => pure e
    | .Ok () =>
        let v0 ← readVReg 0
        writeVReg 0 (v0 ^^^ (6 : BitVec 64))
        let v0 ← readVReg 0
        writeVReg 0 (v0 <<< 3)
        let v1 ← readVReg 1
        let v0 ← readVReg 0
        writeVReg 1 (v1 <<< (v0.setWidth 6).toNat)
        let v1 ← readVReg 1
        liftSail (wX_bits rd (v1.sshiftRight 48))
        pure RETIRE_SUCCESS

theorem execute_LH_reduces (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js)
    (halign : ∀ v, rX_bits rs1 js.sail = .ok v js.sail →
        (v + sign_extend (m := 64) imm) &&& 1 = 0)
    (v : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok v js.sail) :
    (execute_LOAD imm rs1 rd false 2).run js.sail =
    .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (loaded_halfword_at js.sail (v + sign_extend (m := 64) imm)))) := by
  sorry

theorem jolt_lh_concrete (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js)
    (halign : ∀ v, rX_bits rs1 js.sail = .ok v js.sail →
        (v + sign_extend (m := 64) imm) &&& 1 = 0)
    (v : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok v js.sail) :
    ∃ js' : SailJoltState,
      (jolt_lh imm rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (loaded_halfword_at js.sail (v + sign_extend (m := 64) imm))) := by
  sorry

theorem jolt_lh_eq_sail (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js)
    (halign : ∀ v, rX_bits rs1 js.sail = .ok v js.sail →
        (v + sign_extend (m := 64) imm) &&& 1 = 0) :
    projectResult ((jolt_lh imm rs1 rd).run js) =
    (execute_LOAD imm rs1 rd false 2).run js.sail := by
  obtain ⟨v, hrx⟩ := hwf rs1
  obtain ⟨js', hjolt, hjolt_sail⟩ :=
    jolt_lh_concrete imm rs1 rd hrd js hwf halign v hrx
  have hsail := execute_LH_reduces imm rs1 rd js hwf halign v hrx
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail, hsail]

end
