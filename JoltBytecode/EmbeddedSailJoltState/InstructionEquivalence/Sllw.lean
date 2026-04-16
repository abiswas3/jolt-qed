import JoltBytecode.EmbeddedSailJoltState.RtypeW
import JoltBytecode.EmbeddedSailJoltState.ShiftDefs

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do

set_option autoImplicit true

noncomputable section

-- From BytecodeExpansions/Instructions/Sllw.lean
def sllwJolt (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  let v_pow := Jolt.virtualPow2W rs2_val
  let product := Riscv.mul rs1_val v_pow
  Jolt.virtualSignExtendWord product

private lemma sll_32_eq_mul_trunc (x : BitVec 64) (s : Nat) (hs : s < 32) :
    x.setWidth 32 <<< s = (x * BitVec.ofNat 64 (2 ^ s)).setWidth 32 := by
  sorry

theorem sllw_eq_sllwJolt (rs1_val rs2_val : BitVec 64) :
    Riscv.sllw rs1_val rs2_val = sllwJolt rs1_val rs2_val := by
  unfold Riscv.sllw sllwJolt Jolt.virtualPow2W Riscv.mul Jolt.virtualSignExtendWord
  congr 1
  exact sll_32_eq_mul_trunc rs1_val (rs2_val.setWidth 5).toNat (by
    have := (rs2_val.setWidth 5).isLt; norm_num at this; exact this)

/-! ## SLLW: Jolt's VirtualPow2W + MUL + VSEW = Sail SLLW

Jolt decomposes SLLW into (from BytecodeExpansions/Sllw.lean):
1. VirtualPow2W v_pow, rs2      — compute 2^(rs2[4:0])
2. MUL rd, rs1, v_pow           — multiply rs1 by 2^shift (= left shift)
3. VirtualSignExtendWord rd, rd  — sign-extend lower 32 bits

Left-shifting by s equals multiplying by 2^s. The MUL is a full 64-bit
multiply; truncating to 32 bits and sign-extending gives the SLLW result.

Sail's SLLW extracts lower 32 bits of rs1 and rs2, left-shifts the
32-bit value by rs2[4:0], sign-extends to 64, writes to rd.
-/

-- ============================================================================
-- Bridge lemma
-- ============================================================================

-- Jolt computes rs1 * 2^(rs2[4:0]), truncates to 32, sign-extends.
-- Sail computes (rs1[31:0]) << rs2[4:0], sign-extends.
-- These are equal: multiplying by 2^s and taking lower 32 bits = left shift mod 2^32.
-- LHS helper: Jolt's MUL-based computation equals sllwJolt.
private lemma mul_eq_sllwJolt (v1 v2 : BitVec 64) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb (v1 * BitVec.ofNat 64 (2 ^ (v2.setWidth 5).toNat)) 31 0) =
    sllwJolt v1 v2 := by
  unfold sllwJolt Jolt.virtualSignExtendWord Jolt.virtualPow2W Riscv.mul sign_extend
  simp [Sail.BitVec.signExtend, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb']
  congr 1; apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.toNat_mul, BitVec.toNat_ofNat]

-- RHS helper: Sail's SLLW value equals Riscv.sllw.
private lemma sail_sllw_eq_riscv (v1 v2 : BitVec 64) :
    sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v1 31 0)
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)) =
    Riscv.sllw v1 v2 := by
  unfold Riscv.sllw sign_extend shift_bits_left
  simp [Sail.BitVec.signExtend, Sail.BitVec.extractLsb,
        BitVec.extractLsb, BitVec.extractLsb']

-- The MUL-based Jolt SLLW computation produces the same value as Sail's SLLW.
-- Chains: LHS = sllwJolt = Riscv.sllw = RHS.
-- Note: sllw_eq_sllwJolt depends on sll_32_eq_mul_trunc (sorry in BytecodeExpansions).
private lemma sllw_mul_eq_shift (v1 v2 : BitVec 64) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb (v1 * BitVec.ofNat 64 (2 ^ (v2.setWidth 5).toNat)) 31 0) =
    sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v1 31 0)
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)) := by
  rw [mul_eq_sllwJolt, sail_sllw_eq_riscv, sllw_eq_sllwJolt]

-- ============================================================================
-- Factoring
-- ============================================================================

-- Sail's SLLW reads rs1, rs2, extracts lower 32 bits, left-shifts by rs2[4:0],
-- sign-extends, writes to rd.
theorem execute_RTYPEW_SLLW_eq_factored (rs2 rs1 rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.SLLW = (do
      let v1 ← rX_bits rs1; let v2 ← rX_bits rs2
      wX_bits rd (sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v1 31 0)
        (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)))
      pure RETIRE_SUCCESS) := by
  simp [execute_RTYPEW, bind_pure_comp, pure_bind]

-- ============================================================================
-- Jolt SLLW definition (faithful to BytecodeExpansions/Sllw.lean)
-- ============================================================================

-- Jolt's SLLW decomposition: VirtualPow2W + MUL + VirtualSignExtendWord.
-- Step 1: Compute 2^(rs2[4:0]) and store in virtual register.
-- Step 2: Multiply rs1 by that power of 2 (= left shift), write to rd.
-- Step 3: Sign-extend lower 32 bits of rd (VSEW).
def jolt_sllw (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  -- Step 1: VirtualPow2W — compute 2^(rs2[4:0])
  let v2 ← liftSail (rX_bits rs2)
  let v_pow := BitVec.ofNat 64 (2 ^ (v2.setWidth 5).toNat)
  writeVReg 0 v_pow
  -- Step 2: MUL rd, rs1, v_pow
  let v1 ← liftSail (rX_bits rs1)
  let v_pow ← readVReg 0
  liftSail (wX_bits rd (v1 * v_pow))
  -- Step 3: VirtualSignExtendWord rd
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

-- ============================================================================
-- Concrete characterization
-- ============================================================================

-- After running Jolt's SLLW, rd holds sign_extend(shift_bits_left(extractLsb v1, extractLsb(extractLsb v2))).
theorem jolt_sllw_concrete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v1 v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      rX_bits rs2 js.sail = .ok v2 js.sail ∧
      (jolt_sllw rs2 rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v1 31 0)
          (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0))) := by
  unfold jolt_sllw jolt_virtual_sign_extend_word liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
             writeVReg, readVReg, modify, modifyGet, MonadStateOf.modifyGet,
             EStateM.modifyGet, get]
  obtain ⟨v1, hok1⟩ := hwf rs1
  obtain ⟨v2, hok2⟩ := hwf rs2
  simp only [hok1, hok2]
  dsimp only [getThe, MonadStateOf.get, EStateM.get]
  simp (config := { decide := true }) only [ite_true]
  obtain ⟨s3, hw1⟩ := wX_shape rd (v1 * BitVec.ofNat 64 (2 ^ (v2.setWidth 5).toNat)) js.sail
  simp only [hw1]
  have hrx := wX_rX_roundtrip rd _ js.sail s3 hrd hw1
  simp only [hrx]
  obtain ⟨s4, hw2⟩ := wX_shape rd
    (sign_extend (m := 64) (Sail.BitVec.extractLsb (v1 * BitVec.ofNat 64 (2 ^ (v2.setWidth 5).toNat)) 31 0)) s3
  simp only [hw2]
  have hc := wX_wX_collapse rd _ _ js.sail s3 s4 hw1 hw2
  refine ⟨_, v1, v2, rfl, rfl, rfl, ?_⟩
  rw [← sllw_mul_eq_shift v1 v2]
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s4 hc

-- ============================================================================
-- Main theorem: Jolt SLLW = Sail SLLW
-- ============================================================================

-- Running Jolt's SLLW decomposition (VirtualPow2W + MUL + VSEW) and
-- projecting onto Sail state equals running Sail's native SLLW instruction.
theorem jolt_sllw_eq_sail (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_sllw rs2 rs1 rd).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.SLLW).run js.sail := by
  obtain ⟨js', v1, v2, hj_rx1, hj_rx2, hj, hj_sail⟩ :=
    jolt_sllw_concrete rs2 rs1 rd hrd js hwf
  rw [execute_RTYPEW_SLLW_eq_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hj_rx1, hj_rx2]
  show projectResult ((jolt_sllw rs2 rs1 rd).run js) = _
  rw [hj]
  simp only [projectResult, project]
  rw [hj_sail]
  obtain ⟨s', hw⟩ := wX_shape rd _ js.sail
  rw [hw]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd _ js.sail s' hw).symm

end
