import JoltBytecode.SailJoltState.RegisterLemmas

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# ADDW: Jolt ADD + VirtualSignExtendWord = Sail ADDW
-/

-- Truncating to 32 bits distributes over addition.
-- extractLsb(a + b, 31, 0) = extractLsb(a, 31, 0) + extractLsb(b, 31, 0)
--
-- This is the mathematical core of the ADDW proof: Jolt computes
-- v1 + v2 at 64 bits then truncates, while Sail truncates then adds.
-- Both give the same 32-bit result because addition mod 2^32 doesn't
-- depend on the upper bits.
theorem extractLsb_add (a b : BitVec 64) :
    Sail.BitVec.extractLsb (a + b) 31 0 =
    Sail.BitVec.extractLsb a 31 0 + Sail.BitVec.extractLsb b 31 0 := by
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, Nat.add_mod]

theorem execute_RTYPEW_ADDW_eq_factored (rs2 rs1 rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.ADDW = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sign_extend (m := 64)
        (Sail.BitVec.extractLsb v1 31 0 + Sail.BitVec.extractLsb v2 31 0))
      pure RETIRE_SUCCESS) := by
  unfold execute_RTYPEW; rfl

def jolt_addw (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let _ ← liftSail (execute_RTYPE rs2 rs1 rd rop.ADD)
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

theorem jolt_addw_eq_sail (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) :
    projectResult ((jolt_addw rs2 rs1 rd).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.ADDW).run (project js) := by
  rw [execute_RTYPEW_ADDW_eq_factored]
  unfold jolt_addw jolt_virtual_sign_extend_word liftSail inject projectResult project execute_RTYPE
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
  -- Case split on rX_bits rs1
  generalize rX_bits rs1 ⟨js.regs, js.choiceState, js.mem, js.tags, js.cycleCount, js.sailOutput⟩ = r1
  cases r1 with
  | error e s1 => simp
  | ok v1 s1 =>
    simp
    generalize rX_bits rs2 s1 = r2
    cases r2 with
    | error e s2 => simp
    | ok v2 s2 =>
      simp
      -- Both reads succeeded. v1, v2 are the register values, s2 is the state.
      obtain ⟨s3, hwx⟩ := wX_shape rd (v1 + v2) s2
      simp [hwx]
      have hrx := wX_rX_roundtrip rd (v1 + v2) s2 s3 hrd hwx
      simp [hrx]
      rw [extractLsb_add v1 v2]
      obtain ⟨s4, hwx2⟩ := wX_shape rd
          (sign_extend (Sail.BitVec.extractLsb v1 31 0 + Sail.BitVec.extractLsb v2 31 0)) s3
      have hcollapse := wX_wX_collapse rd (v1 + v2)
          (sign_extend (Sail.BitVec.extractLsb v1 31 0 + Sail.BitVec.extractLsb v2 31 0))
          s2 s3 s4 hwx hwx2
      simp [hwx2, hcollapse]

end
