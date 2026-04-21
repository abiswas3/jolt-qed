import JoltBytecode.EmbeddedSailJoltState.RtypeW

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# I-type W family plumbing

Uniform equivalence closer for I-type W ALU instructions. I-type W
instructions (`ADDIW`, `SLLIW`, `SRLIW`, `SRAIW`) have the same surface
shape on the Sail side as R-type W, differing only in that they read a
single source register (`rs1`) rather than two. The immediate (`imm` or
`shamt`) is a compile-time parameter; the generic closer sees it only
through the closure over `exec` and `f`.

See `ALUFamily/Rtype/W/Family.lean` for the analogous R-type W closer
and the rationale for extracting this plumbing.
-/

/-- Uniform I-type W equivalence closer.

Given a Jolt sequence `jolt`, a Sail execution function `exec` factoring
as "read `rs1`, write `f v` to `rd`, return `RETIRE_SUCCESS`", and a
concrete characterisation of `jolt` with the same `f`, the projected
Jolt result equals the Sail result. -/
theorem itype_eq_sail_uniform
    {rs1 rd : regidx}
    {jolt : JoltMonad ExecutionResult}
    {exec : SailM ExecutionResult}
    (f : BitVec 64 → BitVec 64)
    (hexec : exec = do
      let v ← rX_bits rs1
      wX_bits rd (f v)
      pure RETIRE_SUCCESS)
    {js : SailJoltState}
    (hconcrete : ∃ (js' : SailJoltState) (v : BitVec 64),
      rX_bits rs1 js.sail = .ok v js.sail ∧
      jolt.run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd (f v)) :
    projectResult (jolt.run js) = exec.run js.sail := by
  obtain ⟨js', v, hrx1, hj, hj_sail⟩ := hconcrete
  rw [hexec]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hrx1]
  show projectResult (jolt.run js) = _
  rw [hj]
  simp only [projectResult, project]
  rw [hj_sail]
  obtain ⟨s', hw⟩ := wX_shape rd _ js.sail
  rw [hw]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd _ js.sail s' hw).symm

end
