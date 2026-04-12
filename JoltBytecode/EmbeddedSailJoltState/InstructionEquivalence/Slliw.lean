import JoltBytecode.EmbeddedSailJoltState.RtypeW
import JoltBytecode.BytecodeExpansions.Instructions.Slliw

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do

set_option autoImplicit true

noncomputable section

/-! ## SLLIW: Jolt VirtualMULI + VSEW = Sail SLLIW

Jolt decomposes SLLIW as:
1. VirtualMULI rd, rs1, 2^(shamt[4:0]) — multiply rs1 by 2^shift
2. VirtualSignExtendWord rd — sign-extend lower 32 bits
-/

-- extractLsb of multiply by 2^n = shift_bits_left of extractLsb
-- Both take lower 32 bits; multiplication mod 2^32 = shift mod 2^32
private lemma extractLsb_mul_pow2 (v : BitVec 64) (shamt : BitVec 5) :
    Sail.BitVec.extractLsb (v * BitVec.ofNat 64 (2 ^ shamt.toNat)) 31 0 =
    shift_bits_left (Sail.BitVec.extractLsb v 31 0) shamt := by
  unfold shift_bits_left Sail.BitVec.extractLsb
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb, BitVec.toNat_mul, BitVec.toNat_ofNat,
        BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

-- Bridge: Jolt's multiply + truncate = Sail's 32-bit shift
private lemma slliw_mul_eq_shift (v : BitVec 64) (shamt : BitVec 5) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb (v * BitVec.ofNat 64 (2 ^ shamt.toNat)) 31 0) =
    sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v 31 0) shamt) := by
  rw [extractLsb_mul_pow2]

-- Factoring: execute_SHIFTIWOP SLLIW reads rs1, extracts lower 32, left-shifts, sign-extends.
private theorem execute_SHIFTIWOP_SLLIW_eq_factored (shamt : BitVec 5) (rs1 rd : regidx) :
    execute_SHIFTIWOP shamt rs1 rd sopw.SLLIW = (do
      let v ← rX_bits rs1
      wX_bits rd (sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v 31 0) shamt))
      pure RETIRE_SUCCESS) := by
  simp [execute_SHIFTIWOP, bind_pure_comp, pure_bind]

-- Jolt's SLLIW: read rs1, multiply by 2^shamt, write to rd, sign-extend word.
def jolt_slliw (shamt : BitVec 5) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let v ← liftSail (rX_bits rs1)
  liftSail (wX_bits rd (v * BitVec.ofNat 64 (2 ^ shamt.toNat)))
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

-- Concrete: characterise what jolt_slliw writes to rd.
theorem jolt_slliw_concrete (shamt : BitVec 5) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v : BitVec 64),
      rX_bits rs1 js.sail = .ok v js.sail ∧
      (jolt_slliw shamt rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v 31 0) shamt)) := by
  sorry

-- Running Jolt's SLLIW and projecting equals running Sail's SLLIW.
theorem jolt_slliw_eq_sail (shamt : BitVec 5) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_slliw shamt rs1 rd).run js) =
    (execute_SHIFTIWOP shamt rs1 rd sopw.SLLIW).run js.sail := by
  obtain ⟨js', v, hj_rx, hj, hj_sail⟩ :=
    jolt_slliw_concrete shamt rs1 rd hrd js hwf
  rw [execute_SHIFTIWOP_SLLIW_eq_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hj_rx]
  show projectResult ((jolt_slliw shamt rs1 rd).run js) = _
  rw [hj]
  simp only [projectResult, project]
  rw [hj_sail]
  obtain ⟨s', hw⟩ := wX_shape rd _ js.sail
  rw [hw]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd _ js.sail s' hw).symm

end
