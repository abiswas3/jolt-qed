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
# LB: Jolt load-byte (signed) decomposition = Sail LB

From `tracer/src/instruction/lb.rs::inline_sequence_64`:

    ADDI  v0, rs1, imm
    ANDI  v1, v0, -8
    LD    v1, v1, 0
    XORI  v0, v0, 7
    SLLI  v0, v0, 3
    SLL   v1, v1, v0
    SRAI  rd, v1, 56

No alignment assert — byte loads are naturally aligned at every address.
Sail: `execute_LOAD imm rs1 rd false 1`.
-/

-- The 8-bit byte at a given vaddr. Under Jolt's bare-MMU configuration
-- vaddr = paddr, so we index the Sail memory hash map directly by vaddr.toNat.
-- Unpopulated addresses default to 0; the memory precondition bundle keeps
-- the happy-path proofs away from the default branch.
def loaded_byte_at (s : SailState) (vaddr : BitVec 64) : BitVec 8 :=
  (s.mem.get? vaddr.toNat).getD 0

-- Memory precondition for a load of `width` bytes starting at `vaddr`.
-- Currently asserts populatedness only; will grow to include
-- ext_data_get_addr success, translateAddr identity, and PMP permission
-- as the helper proofs demand them.
def MemReadable (s : SailState) (vaddr : BitVec 64) (width : Nat) : Prop :=
  ∀ i : Nat, i < width → (s.mem.get? ((vaddr + BitVec.ofNat 64 i).toNat)).isSome

def jolt_lb (imm : BitVec 12) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
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
      liftSail (wX_bits rd (v1.sshiftRight 56))
      pure RETIRE_SUCCESS

theorem execute_LB_reduces (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js)
    (v : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok v js.sail)
    (hmem : MemReadable js.sail (v + sign_extend (m := 64) imm) 1) :
    (execute_LOAD imm rs1 rd false 1).run js.sail =
    .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (loaded_byte_at js.sail (v + sign_extend (m := 64) imm)))) := by
  sorry

theorem jolt_lb_concrete (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js)
    (v : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok v js.sail)
    (hmem : MemReadable js.sail ((v + sign_extend (m := 64) imm) &&& (-8 : BitVec 64)) 8) :
    ∃ js' : SailJoltState,
      (jolt_lb imm rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (loaded_byte_at js.sail (v + sign_extend (m := 64) imm))) := by
  sorry

theorem jolt_lb_eq_sail (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js)
    (hmem_byte : ∀ v, rX_bits rs1 js.sail = .ok v js.sail →
        MemReadable js.sail (v + sign_extend (m := 64) imm) 1)
    (hmem_dword : ∀ v, rX_bits rs1 js.sail = .ok v js.sail →
        MemReadable js.sail ((v + sign_extend (m := 64) imm) &&& (-8 : BitVec 64)) 8) :
    projectResult ((jolt_lb imm rs1 rd).run js) =
    (execute_LOAD imm rs1 rd false 1).run js.sail := by
  obtain ⟨v, hrx⟩ := hwf rs1
  obtain ⟨js', hjolt, hjolt_sail⟩ :=
    jolt_lb_concrete imm rs1 rd hrd js hwf v hrx (hmem_dword v hrx)
  have hsail := execute_LB_reduces imm rs1 rd js hwf v hrx (hmem_byte v hrx)
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail, hsail]

end
