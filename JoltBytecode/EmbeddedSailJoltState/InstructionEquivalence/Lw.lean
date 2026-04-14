import JoltBytecode.EmbeddedSailJoltState.RtypeW

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

/-!
# LW: Jolt load-word decomposition = Sail LW

Faithful model of Jolt's RV64 LW inline sequence from
`tracer/src/instruction/lw.rs::inline_sequence_64`:

    VirtualAssertWordAlignment rs1, imm
    ADDI  v0, rs1, imm
    ANDI  v1, v0, -8
    LD    v1, v1, 0
    SLLI  v0, v0, 3
    SRL   v1, v1, v0
    VirtualSignExtendWord rd, v1, 0
-/

-- ============================================================================
-- Placeholder: the 32-bit word at a given vaddr in a SailState.
-- Both the Sail- and Jolt-side concrete lemmas reference this opaque function;
-- it will be replaced by a real byte-assembly spec when we discharge the sorries.
-- ============================================================================
def loaded_word_at (_s : SailState) (_vaddr : BitVec 64) : BitVec 32 := 0

-- ============================================================================
-- Helper: aligned 8-byte load into a virtual register
-- ============================================================================

def jolt_load_dword (vaddr : virtaddr) (vr : BitVec 7) :
    JoltMonad (Result Unit ExecutionResult) := do
  match ← liftSail (vmem_read_addr vaddr 0 8 (Load Data) false false false) with
  | .Ok dword =>
      writeVReg vr dword
      pure (Ok ())
  | .Err e =>
      pure (Err e)

-- ============================================================================
-- Jolt LW decomposition
-- ============================================================================

def jolt_lw (imm : BitVec 12) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let base ← liftSail (rX_bits rs1)
  let ea := base + sign_extend (m := 64) imm
  if ea &&& 3 ≠ 0 then
    throw (Error.Assertion "LW: effective address not word-aligned")
  else do
    writeVReg 0 ea
    let v0 ← readVReg 0
    writeVReg 1 (v0 &&& (-8 : BitVec 64))
    let v1 ← readVReg 1
    match ← jolt_load_dword (Virtaddr v1) 1 with
    | .Err e => pure e
    | .Ok () =>
        let v0 ← readVReg 0
        writeVReg 0 (v0 <<< 3)
        let v1 ← readVReg 1
        let v0 ← readVReg 0
        writeVReg 1 (v1 >>> (v0.setWidth 6).toNat)
        let v1 ← readVReg 1
        liftSail (wX_bits rd
          (sign_extend (m := 64) (Sail.BitVec.extractLsb v1 31 0)))
        pure RETIRE_SUCCESS

-- ============================================================================
-- Layer 1 (Sail side): execute_LOAD reduces to a single register write.
-- Under alignment + memory preconditions, the entire Sail memory pipeline
-- (vmem_read → ext_data_get_addr → vmem_read_addr → translateAddr → mem_read
-- + the fueled misalignment loop) collapses to one `stateAfterWrite`.
-- ============================================================================

theorem execute_LW_reduces (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js)
    (halign : ∀ v, rX_bits rs1 js.sail = .ok v js.sail →
        (v + sign_extend (m := 64) imm) &&& 3 = 0)
    (v : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok v js.sail) :
    (execute_LOAD imm rs1 rd false 4).run js.sail =
    .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (loaded_word_at js.sail (v + sign_extend (m := 64) imm)))) := by
  sorry

-- ============================================================================
-- Layer 2 (Jolt side): the entire 7-step jolt_lw sequence reduces to a single
-- register write on the Sail component of the state. All vreg shuffling,
-- the dword load, the shift/extract, and the sign-extend are folded into
-- the same BitVec 64 that execute_LW_reduces produces.
-- ============================================================================

theorem jolt_lw_concrete (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js)
    (halign : ∀ v, rX_bits rs1 js.sail = .ok v js.sail →
        (v + sign_extend (m := 64) imm) &&& 3 = 0)
    (v : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok v js.sail) :
    ∃ js' : SailJoltState,
      (jolt_lw imm rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (loaded_word_at js.sail (v + sign_extend (m := 64) imm))) := by
  sorry

-- ============================================================================
-- Main theorem: Jolt LW = Sail LW
-- Proof uses only the two concrete helpers above; no sorry here.
-- ============================================================================

theorem jolt_lw_eq_sail (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js)
    (halign : ∀ v, rX_bits rs1 js.sail = .ok v js.sail →
        (v + sign_extend (m := 64) imm) &&& 3 = 0) :
    projectResult ((jolt_lw imm rs1 rd).run js) =
    (execute_LOAD imm rs1 rd false 4).run js.sail := by
  obtain ⟨v, hrx⟩ := hwf rs1
  obtain ⟨js', hjolt, hjolt_sail⟩ :=
    jolt_lw_concrete imm rs1 rd hrd js hwf halign v hrx
  have hsail := execute_LW_reduces imm rs1 rd js hwf halign v hrx
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail, hsail]

end
