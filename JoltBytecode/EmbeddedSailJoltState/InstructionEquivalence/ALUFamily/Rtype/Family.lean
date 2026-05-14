import JoltBytecode.EmbeddedSailJoltState.RtypeW

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# R-type family plumbing

This file provides the generic theorem shared by R-type ALU instructions
with the same Sail-side surface shape: read `rs1`, read `rs2`, write a
value to `rd`, and return `RETIRE_SUCCESS`.

It serves R-type W instructions (`ADDW`, `SUBW`, `MULW`, `SLLW`, `SRLW`,
`SRAW`), non-W shifts (`SLL`, `SRL`, `SRA`), and selected multiply-family
instructions using the same two-register/write-one-register plumbing.
They differ in *what* gets written. The closer only needs a concrete
Jolt characterisation and a factoring of the Sail target.
-/

/-- Uniform R-type equivalence closer.

Given:
* a Jolt sequence `jolt`,
* a Sail execution function `exec` with a factoring that reads `rs1`,
  reads `rs2`, writes `f v1 v2` to `rd`, and returns `RETIRE_SUCCESS`,
* a concrete characterisation witnessing that `jolt` succeeds and
  leaves the Sail component of the state equal to `stateAfterWrite
  js.sail rd (f v1 v2)` for the same values `v1`, `v2` read on the Sail
  side,

the Jolt sequence and the Sail target produce equal results on the Sail
state. -/
theorem rtype_eq_sail_uniform
    {rs1 : regidx}
    {rs2 : regidx}
    {rd : regidx}
    {jolt : JoltMonad ExecutionResult}
    {exec : SailM ExecutionResult}
    (f : BitVec 64 → BitVec 64 → BitVec 64)
    (hexec : exec = do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (f v1 v2)
      pure RETIRE_SUCCESS)
    {js : SailJoltState}
    (hconcrete : ∃ (js' : SailJoltState) (v1 v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      rX_bits rs2 js.sail = .ok v2 js.sail ∧
      jolt.run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd (f v1 v2)) :
    projectResult (jolt.run js) = exec.run js.sail := by
  obtain ⟨js', v1, v2, hrx1, hrx2, hj, hj_sail⟩ := hconcrete
  rw [hexec]
  simp only [EStateM.run]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  simp only [hrx1, hrx2]
  simp only [EStateM.run] at hj
  rw [hj]
  simp only [projectResult, project]
  rw [hj_sail]
  obtain ⟨s', hw⟩ := wX_shape rd (f v1 v2) js.sail
  simp only [hw]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd (f v1 v2) js.sail s' hw).symm

end
