import JoltBytecode.EmbeddedSailJoltState.RtypeW

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do

set_option autoImplicit true

noncomputable section

/-! ## MULH: Jolt's 7-step decomposition = Sail MULH

Jolt decomposes MULH as:
1. VirtualMovSign v_sx, rs1 — extract sign of rs1
2. VirtualMovSign v_sy, rs2 — extract sign of rs2
3. MUL v_sx, v_sx, rs2      — s_x * y
4. MUL v_sy, v_sy, rs1      — s_y * x
5. MULHU v_tmp, rs1, rs2     — unsigned high multiply
6. ADD v_tmp, v_tmp, v_sx    — add s_x * y
7. ADD rd, v_tmp, v_sy       — add s_y * x

The key insight: signed high multiply = unsigned high multiply + sign corrections.
-/

-- VirtualMovSign: extract sign as 0 or -1 (all ones)
def virtualMovSign (v : BitVec 64) : BitVec 64 :=
  if v.msb then BitVec.allOnes 64 else 0

-- MULHU: unsigned high multiply
def mulhu (v1 v2 : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (v1.toNat * v2.toNat / 2^64)

-- The mul_op for MULH: signed × signed, high half
def mulh_mul_op : mul_op := ⟨VectorHalf.High, Signedness.Signed, Signedness.Signed⟩

-- Factoring: execute_MUL with MULH mul_op reads rs1, rs2, computes signed high multiply.
private theorem execute_MUL_MULH_factored (rs2 rs1 rd : regidx) :
    execute_MUL rs2 rs1 rd mulh_mul_op = (do
      let v1 ← rX_bits rs1; let v2 ← rX_bits rs2
      wX_bits rd (mult_to_bits_half (l := xlen) Signedness.Signed Signedness.Signed v1 v2 VectorHalf.High)
      pure RETIRE_SUCCESS) := by
  sorry

-- Jolt's MULH: 7-step decomposition with virtual registers.
def jolt_mulh (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let v1 ← liftSail (rX_bits rs1)
  let v2 ← liftSail (rX_bits rs2)
  let v_sx := virtualMovSign v1
  let v_sy := virtualMovSign v2
  let v_mulhu := mulhu v1 v2
  let v_sx_mul := v_sx * v2
  let v_sy_mul := v_sy * v1
  let v_tmp := v_mulhu + v_sx_mul
  liftSail (wX_bits rd (v_tmp + v_sy_mul))
  pure RETIRE_SUCCESS

-- Bridge: Jolt's 7-step computation = Sail's mult_to_bits_half
private lemma mulh_bridge (v1 v2 : BitVec 64) :
    (mulhu v1 v2 + virtualMovSign v1 * v2 + virtualMovSign v2 * v1) =
    mult_to_bits_half (l := xlen) Signedness.Signed Signedness.Signed v1 v2 VectorHalf.High := by
  sorry

-- Concrete: Jolt writes the signed high multiply value to rd.
theorem jolt_mulh_concrete (rs2 rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v1 v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      rX_bits rs2 js.sail = .ok v2 js.sail ∧
      (jolt_mulh rs2 rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (mult_to_bits_half (l := xlen) Signedness.Signed Signedness.Signed v1 v2 VectorHalf.High) := by
  sorry

-- Running Jolt's MULH and projecting equals running Sail's MULH.
theorem jolt_mulh_eq_sail (rs2 rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_mulh rs2 rs1 rd).run js) =
    (execute_MUL rs2 rs1 rd mulh_mul_op).run js.sail := by
  obtain ⟨js', v1, v2, hj_rx1, hj_rx2, hj, hj_sail⟩ :=
    jolt_mulh_concrete rs2 rs1 rd js hwf
  rw [execute_MUL_MULH_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hj_rx1, hj_rx2]
  show projectResult ((jolt_mulh rs2 rs1 rd).run js) = _
  rw [hj]
  simp only [projectResult, project]
  rw [hj_sail]
  obtain ⟨s', hw⟩ := wX_shape rd _ js.sail
  rw [hw]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd _ js.sail s' hw).symm

end
