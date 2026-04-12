import JoltBytecode.EmbeddedSailJoltState.RtypeW
import JoltBytecode.BytecodeExpansions.Instructions.Srli

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do

set_option autoImplicit true

noncomputable section

/-! ## SRLI: Jolt VirtualSRLI via bitmask = Sail SRLI

Jolt decomposes SRLI as:
1. VirtualSRLI rd, rs1, bitmask — logical right shift by ctz(bitmask)

ctz(srli_bitmask(shamt)) = shamt[5:0], so this equals Sail's SRLI.
-/

-- extractLsb shamt 5 0 = shamt for BitVec 6
private lemma extractLsb_shamt6_id (shamt : BitVec 6) :
    Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0 = shamt := by
  simp only [LeanRV64D.Functions.log2_xlen, Sail.BitVec.extractLsb]
  ext i; simp [BitVec.getLsbD_extractLsb]; rfl

-- setWidth 64 then setWidth 6 = identity on BitVec 6
private lemma setWidth_roundtrip (shamt : BitVec 6) :
    (shamt.setWidth 64).setWidth 6 = shamt := by
  ext i; simp [BitVec.getLsbD_setWidth]

-- v >>> (n : Nat) = v >>> (BitVec.ofNat w n) when the shift is by toNat
private lemma ushiftRight_nat_eq_bv (v : BitVec 64) (s : BitVec 6) :
    v >>> s.toNat = v >>> s := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight]

-- Bridge: Jolt's logical shift via ctz(bitmask) = Sail's shift_bits_right
private lemma srli_bitmask_eq_shift (v : BitVec 64) (shamt : BitVec 6) :
    v >>> ctz (srli_bitmask (shamt.setWidth 64)) =
    shift_bits_right v (Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0) := by
  unfold shift_bits_right
  rw [extractLsb_shamt6_id, ctz_srli_bitmask, setWidth_roundtrip]
  exact ushiftRight_nat_eq_bv v shamt

-- Jolt's SRLI: read rs1, logical right shift by ctz(bitmask), write to rd.
def jolt_srli (shamt : BitVec 6) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let v ← liftSail (rX_bits rs1)
  liftSail (wX_bits rd (v >>> ctz (srli_bitmask (shamt.setWidth 64))))
  pure RETIRE_SUCCESS

-- Factoring: execute_SHIFTIOP SRLI reads rs1, right-shifts by shamt.
private theorem execute_SHIFTIOP_SRLI_eq_factored (shamt : BitVec 6) (rs1 rd : regidx) :
    execute_SHIFTIOP shamt rs1 rd sop.SRLI = (do
      let v ← rX_bits rs1
      wX_bits rd (shift_bits_right v (Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0))
      pure RETIRE_SUCCESS) := by
  simp [execute_SHIFTIOP, bind_pure_comp]

-- Concrete: characterise what jolt_srli writes to rd.
theorem jolt_srli_concrete (shamt : BitVec 6) (rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v : BitVec 64),
      rX_bits rs1 js.sail = .ok v js.sail ∧
      (jolt_srli shamt rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (shift_bits_right v (Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0)) := by
  sorry

-- Running Jolt's SRLI and projecting equals running Sail's SRLI.
theorem jolt_srli_eq_sail (shamt : BitVec 6) (rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_srli shamt rs1 rd).run js) =
    (execute_SHIFTIOP shamt rs1 rd sop.SRLI).run js.sail := by
  obtain ⟨js', v, hj_rx, hj, hj_sail⟩ :=
    jolt_srli_concrete shamt rs1 rd js hwf
  rw [execute_SHIFTIOP_SRLI_eq_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hj_rx]
  show projectResult ((jolt_srli shamt rs1 rd).run js) = _
  rw [hj]
  simp only [projectResult, project]
  rw [hj_sail]
  obtain ⟨s', hw⟩ := wX_shape rd _ js.sail
  rw [hw]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd _ js.sail s' hw).symm

end
