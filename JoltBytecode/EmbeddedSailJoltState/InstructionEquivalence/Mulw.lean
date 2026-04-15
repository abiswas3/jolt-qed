import JoltBytecode.EmbeddedSailJoltState.RtypeW
import Mathlib

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do

set_option autoImplicit true

noncomputable section

/-!
# MULW: Jolt MUL + VirtualSignExtendWord = Sail MULW

From `tracer/src/instruction/mulw.rs::inline_sequence_64`:

    MUL    rd, rs1, rs2
    VirtualSignExtendWord rd, rd, 0
-/

private theorem mod33_toNat_mod32 (x : Int) :
    (x % 8589934592).toNat % 4294967296 = (x % 4294967296).toNat := by
  apply Int.ofNat.inj
  simp [Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num : (8589934592 : Int) ≠ 0)),
        Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num : (4294967296 : Int) ≠ 0))]

private theorem trunc32_eq_intCast (x : Int) :
    to_bits_truncate (l := 32) x = (x : BitVec 32) := by
  apply BitVec.eq_of_toFin_eq
  rw [show to_bits_truncate (l := 32) x = BitVec.ofNat 32 ((x % 8589934592).toNat) by
        simp [to_bits_truncate, get_slice_int, BitVec.extractLsb']]
  rw [BitVec.toFin_ofNat, BitVec.toFin_intCast]
  ext
  simpa [Fin.ofNat] using mod33_toNat_mod32 x

private theorem intCast_mul_toInt_32 (a b : BitVec 32) :
    (((BitVec.toInt a *i BitVec.toInt b : Int) : BitVec 32)) = a * b := by
  change BitVec.ofInt 32 (a.toInt * b.toInt) = a * b
  rw [BitVec.ofInt_mul]
  have h1 : BitVec.ofInt 32 a.toInt = a := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toInt]; omega
  have h2 : BitVec.ofInt 32 b.toInt = b := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toInt]; omega
  rw [h1, h2]

private theorem mulw32_eq_mul (a b : BitVec 32) :
    to_bits_truncate (l := 32) (BitVec.toInt a *i BitVec.toInt b) = a * b := by
  rw [trunc32_eq_intCast]
  exact intCast_mul_toInt_32 a b

private theorem execute_MULW_factored (rs2 rs1 rd : regidx) :
    execute_MULW rs2 rs1 rd = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sign_extend (m := 64)
        (to_bits_truncate (l := 32)
          (BitVec.toInt (Sail.BitVec.extractLsb v1 31 0) *i
           BitVec.toInt (Sail.BitVec.extractLsb v2 31 0))))
      pure RETIRE_SUCCESS) := by
  simp [execute_MULW, bind_pure_comp, pure_bind]

private theorem extractLsb_mul (v1 v2 : BitVec 64) :
    Sail.BitVec.extractLsb (v1 * v2) 31 0 =
      Sail.BitVec.extractLsb v1 31 0 * Sail.BitVec.extractLsb v2 31 0 := by
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul]

def jolt_mulw (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let v1 ← liftSail (rX_bits rs1)
  let v2 ← liftSail (rX_bits rs2)
  liftSail (wX_bits rd (v1 * v2))
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

private theorem jolt_mulw_concrete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v1 v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      rX_bits rs2 js.sail = .ok v2 js.sail ∧
      (jolt_mulw rs2 rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (to_bits_truncate (l := 32)
            (BitVec.toInt (Sail.BitVec.extractLsb v1 31 0) *i
             BitVec.toInt (Sail.BitVec.extractLsb v2 31 0)))) := by
  unfold jolt_mulw liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
  obtain ⟨v1, h1⟩ := hwf rs1
  obtain ⟨v2, h2⟩ := hwf rs2
  simp only [h1, h2]
  obtain ⟨s3, hw1⟩ := wX_shape rd (v1 * v2) js.sail
  simp only [hw1]
  have hrx := wX_rX_roundtrip rd _ js.sail s3 hrd hw1
  obtain ⟨js4, hvsew, hsail⟩ :=
    jolt_virtual_sign_extend_word_concrete rd { sail := s3, vregs := js.vregs } (v1 * v2) hrd hrx
  simp only [EStateM.run] at hvsew
  simp only [hvsew]
  refine ⟨js4, v1, v2, rfl, rfl, rfl, ?_⟩
  rw [hsail, show ({ sail := s3, vregs := js.vregs } : SailJoltState).sail = s3 from rfl,
      wX_bits_eq_stateAfterWrite rd (v1 * v2) js.sail s3 hw1,
      stateAfterWrite_stateAfterWrite]
  congr 1; congr 1
  rw [extractLsb_mul, ← mulw32_eq_mul]

theorem jolt_mulw_eq_sail (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_mulw rs2 rs1 rd).run js) =
    (execute_MULW rs2 rs1 rd).run js.sail := by
  obtain ⟨js', v1, v2, hj_rx1, hj_rx2, hj, hj_sail⟩ :=
    jolt_mulw_concrete rs2 rs1 rd hrd js hwf
  rw [execute_MULW_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hj_rx1, hj_rx2]
  show projectResult ((jolt_mulw rs2 rs1 rd).run js) = _
  rw [hj]
  simp only [projectResult, project]
  rw [hj_sail]
  obtain ⟨s', hw⟩ := wX_shape rd _ js.sail
  rw [hw]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd _ js.sail s' hw).symm

end
