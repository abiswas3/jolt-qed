import JoltBytecode.EmbeddedSailJoltState.RtypeW

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# R-type W family plumbing

This file provides the one generic theorem shared by every R-type W ALU
instruction: the uniform equivalence closer.

All R-type W instructions (ADDW, SUBW, MULW, SLLW, SRLW, SRAW) share the
same surface shape on the Sail side: read `rs1`, read `rs2`, write a
value to `rd`, return `RETIRE_SUCCESS`. They differ in *what* gets
written (the arithmetic), and on the Jolt side some build the sequence
via `execute_RTYPE op + VSEW` while others stack their own virtual
register operations. None of that matters to the plumbing: once an
instruction has a `_concrete` characterisation (final sail state =
`stateAfterWrite js.sail rd (f v1 v2)`) and a factoring of its Sail
target (`exec = read rs1, read rs2, write (f v1 v2), return`), the main
`_eq_sail` proof is mechanical.

We capture that mechanical proof here, once, as
`rtype_eq_sail_uniform`. Every per-instruction file in `Rtype/W/`
invokes it in a single line.

This file deliberately avoids `mvcgen`, `@[spec]`, and `Std.Do`. The
load family and the blog's original 8-step template both use a direct
tactic style; we match that here so the ALU plumbing is the same shape
as the plumbing readers have already seen elsewhere.
-/

/-- Uniform R-type W equivalence closer.

Given:
* a Jolt sequence `jolt`,
* a Sail execution function `exec` with a factoring that reads `rs1`,
  reads `rs2`, writes `f v1 v2` to `rd`, and returns `RETIRE_SUCCESS`,
* a concrete characterisation witnessing that `jolt` succeeds and
  leaves the Sail component of the state equal to `stateAfterWrite
  js.sail rd (f v1 v2)` for the same values `v1`, `v2` read on the Sail
  side,

the Jolt sequence and the Sail target produce equal results on the Sail
state. The proof is the 14-line plumbing factored out of every
per-instruction `_eq_sail` theorem. -/
theorem rtype_eq_sail_uniform
    {rs1 rs2 rd : regidx}
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
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hrx1, hrx2]
  show projectResult (jolt.run js) = _
  rw [hj]
  simp only [projectResult, project]
  rw [hj_sail]
  obtain ⟨s', hw⟩ := wX_shape rd _ js.sail
  rw [hw]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd _ js.sail s' hw).symm

end
