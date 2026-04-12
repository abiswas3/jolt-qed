import JoltBytecode.EmbeddedSailJoltState.RtypeW
import JoltBytecode.BytecodeExpansions.Instructions.Srliw

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do

set_option autoImplicit true

noncomputable section

/-! ## SRLIW: Jolt SLLI 32 + VirtualSRLI + VSEW = Sail SRLIW

Jolt decomposes SRLIW as:
1. SLLI v_rs1, rs1, 32 — shift left by 32 (clears upper bits)
2. VirtualSRLI rd, v_rs1, bitmask — logical right shift via ctz(bitmask)
3. VirtualSignExtendWord rd — sign-extend lower 32 bits

The bitmask encodes shamt[4:0] + 32, so ctz recovers the adjusted shift.
-/

-- Bridge: Jolt's slli-32 + srli via bitmask = Sail's 32-bit logical right shift
private lemma srliw_shift_eq (v : BitVec 64) (shamt : BitVec 5) :
    sign_extend (m := 64)
      (Sail.BitVec.extractLsb
        ((v <<< 32) >>> ctz (srliw_imm (shamt.setWidth 64))) 31 0) =
    sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb v 31 0) shamt) := by
  sorry

-- Factoring: execute_SHIFTIWOP SRLIW reads rs1, extracts lower 32, right-shifts, sign-extends.
private theorem execute_SHIFTIWOP_SRLIW_eq_factored (shamt : BitVec 5) (rs1 rd : regidx) :
    execute_SHIFTIWOP shamt rs1 rd sopw.SRLIW = (do
      let v ← rX_bits rs1
      wX_bits rd (sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb v 31 0) shamt))
      pure RETIRE_SUCCESS) := by
  simp [execute_SHIFTIWOP, bind_pure_comp, pure_bind]

-- Jolt's SRLIW: read rs1, shift left 32 (vreg), logical right shift via bitmask, VSEW.
def jolt_srliw (shamt : BitVec 5) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let v ← liftSail (rX_bits rs1)
  writeVReg 0 (v <<< 32)
  let v_rs1 ← readVReg 0
  liftSail (wX_bits rd (v_rs1 >>> ctz (srliw_imm (shamt.setWidth 64))))
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

-- Concrete: characterise what jolt_srliw writes to rd.
theorem jolt_srliw_concrete (shamt : BitVec 5) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v : BitVec 64),
      rX_bits rs1 js.sail = .ok v js.sail ∧
      (jolt_srliw shamt rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64) (Sail.BitVec.extractLsb
          ((v <<< 32) >>> ctz (srliw_imm (shamt.setWidth 64))) 31 0)) := by
  sorry

-- Running Jolt's SRLIW and projecting equals running Sail's SRLIW.
theorem jolt_srliw_eq_sail (shamt : BitVec 5) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_srliw shamt rs1 rd).run js) =
    (execute_SHIFTIWOP shamt rs1 rd sopw.SRLIW).run js.sail := by
  obtain ⟨js', v, hj_rx, hj, hj_sail⟩ :=
    jolt_srliw_concrete shamt rs1 rd hrd js hwf
  rw [execute_SHIFTIWOP_SRLIW_eq_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hj_rx]
  show projectResult ((jolt_srliw shamt rs1 rd).run js) = _
  rw [hj]
  simp only [projectResult, project]
  rw [hj_sail, srliw_shift_eq v shamt]
  obtain ⟨s', hw⟩ := wX_shape rd _ js.sail
  rw [hw]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd _ js.sail s' hw).symm

end
