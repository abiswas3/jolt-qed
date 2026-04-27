import JoltBytecode.EmbeddedSailJoltState.Defs
import JoltBytecode.EmbeddedSailJoltState.RegisterOps

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# ALU-advice-family primitives

Constraint primitives shared by the advice-verified ALU instructions
(`DIV`, `REM`, `DIVU`, `REMU`). These encode invariants specific to
signed/unsigned division and remainder verification — they do not
belong in `VirtualInstructions.lean` (which models generic Jolt-ISA
ops), but neither do they belong in any single instruction file once
more than one instruction uses them.

Scope: imported by `ALUAdviceFamily/*` only. Generic assertions and
advice-load primitives live in `VirtualInstructions.lean`.
-/

/-- Pure overflow-folding rule: when a signed division would overflow
(`dividend = 0x8000…0` and `divisor = -1`), the Jolt `VirtualChangeDivisor`
substitutes `1` for `divisor`; otherwise passes `divisor` through unchanged.
This makes `q · adj` fit in 64 bits signed (since the honest quotient
under overflow is `INT_MIN`, and `INT_MIN · 1 = INT_MIN`). Matches the
Rust impl in `tracer/src/instruction/virtual_change_divisor.rs`. -/
def change_divisor_value (dividend divisor : BitVec 64) : BitVec 64 :=
  let mostNeg : BitVec 64 := (1 : BitVec 64) <<< 63
  let negOne  : BitVec 64 := -1
  if dividend = mostNeg ∧ divisor = negOne then 1 else divisor

/-- `VirtualChangeDivisor vd, rs1, rs2`: read real `rs1` (dividend) and
    real `rs2` (divisor); if the pair would overflow signed division,
    write `1` to `vd`, otherwise write the divisor. -/
def vreg_change_divisor (vd : BitVec 7) (rs1 rs2 : regidx) : JoltMonad ExecutionResult := do
  let dividend ← liftSail (rX_bits rs1)
  let divisor ← liftSail (rX_bits rs2)
  writeVReg vd (change_divisor_value dividend divisor)
  pure RETIRE_SUCCESS

/-- `VirtualAssertValidDiv0 rs2, vq`: if the *real* divisor `rs2` is zero,
    the virtual register `vq` must hold `-1` (signed `u64::MAX`). Aborts
    the Jolt run otherwise. -/
def vreg_assert_valid_div0 (rs2 : regidx) (vq : BitVec 7) : JoltMonad ExecutionResult := do
  let divisor ← liftSail (rX_bits rs2)
  let q ← readVReg vq
  if divisor = 0#64 ∧ q ≠ (-1 : BitVec 64) then
    throw (Error.Assertion "VirtualAssertValidDiv0: divisor = 0 but quotient ≠ -1")
  else
    pure RETIRE_SUCCESS

/-- `VirtualAssertValidUnsignedRemainder vr, vd`: asserts that either
    the divisor `vd` is zero (in which case the check is vacuous, since
    the protocol's div-by-zero case sets the adjusted divisor to zero
    and supplies `|dividend|` as the remainder advice), or `vr < vd`
    unsigned (i.e. `|remainder| < |adjusted divisor|`). Matches the
    Rust impl in `tracer/src/instruction/virtual_assert_valid_unsigned_remainder.rs`:
    `assert!(divisor == 0 || remainder < divisor)`. -/
def vreg_assert_valid_unsigned_remainder (vr vd : BitVec 7) : JoltMonad ExecutionResult := do
  let r ← readVReg vr
  let d ← readVReg vd
  if d = 0#64 ∨ r.toNat < d.toNat then pure RETIRE_SUCCESS
  else throw (Error.Assertion "VirtualAssertValidUnsignedRemainder: r ≥ d ∧ d ≠ 0")

end
