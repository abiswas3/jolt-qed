import JoltBytecode.SailJoltState.EmbeddedArch.RegisterOps

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-! ## ADDW -/

def jolt_addw (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let _ ← liftSail (execute_RTYPE rs2 rs1 rd rop.ADD)
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

theorem jolt_addw_eq_sail (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) :
    projectResult ((jolt_addw rs2 rs1 rd).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.ADDW).run js.sail := by
  unfold execute_RTYPEW jolt_addw jolt_virtual_sign_extend_word liftSail projectResult execute_RTYPE
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
  -- Case-split on reads. With embedded arch, we use js.sail directly.
  sail_cases rX_bits rs1 js.sail
  rename_i v1 s1
  sail_cases rX_bits rs2 s1
  rename_i v2 s2
  -- Both reads succeeded.
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
