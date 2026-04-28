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

/-- DIVU variant of `VirtualAssertValidUnsignedRemainder`: divisor lives
    in a *real* register (DIVU does no sign-fixup, so the divisor is
    simply `rs2` rather than the absolute value of an adjusted divisor). -/
def vreg_assert_valid_unsigned_remainder_real
    (vr : BitVec 7) (rs : regidx) : JoltMonad ExecutionResult := do
  let r ← readVReg vr
  let d ← liftSail (rX_bits rs)
  if d = 0#64 ∨ r.toNat < d.toNat then pure RETIRE_SUCCESS
  else throw (Error.Assertion "VirtualAssertValidUnsignedRemainder: r ≥ d ∧ d ≠ 0")

/-- `VirtualAssertMulUNoOverflow va, rs`: asserts the unsigned 64×64
    product `va.toNat * rs.toNat` fits in 64 bits (no overflow). Matches
    the Rust impl in `tracer/src/instruction/virtual_assert_mulu_no_overflow.rs`:
    `assert!((a as u128) * (b as u128) <= u64::MAX as u128)`. -/
def vreg_assert_mulu_no_overflow
    (va : BitVec 7) (rs : regidx) : JoltMonad ExecutionResult := do
  let a ← readVReg va
  let b ← liftSail (rX_bits rs)
  if a.toNat * b.toNat < 2^64 then pure RETIRE_SUCCESS
  else throw (Error.Assertion "VirtualAssertMulUNoOverflow")

/-- `VirtualAssertLTE va, rs`: asserts `va ≤ rs` (unsigned). Used by
    DIVU to check `quotient * divisor ≤ dividend`. -/
def vreg_assert_lte_real
    (va : BitVec 7) (rs : regidx) : JoltMonad ExecutionResult := do
  let a ← readVReg va
  let b ← liftSail (rX_bits rs)
  if a.toNat ≤ b.toNat then pure RETIRE_SUCCESS
  else throw (Error.Assertion "VirtualAssertLTE")

/-- DIVW variant of `VirtualAssertValidDiv0`: divisor is in a *virtual*
    register (DIVW first sign-extends the real divisor into `t3`, then
    runs all subsequent constraints over the virtual `t3`). -/
def vreg_assert_valid_div0_v
    (vd : BitVec 7) (vq : BitVec 7) : JoltMonad ExecutionResult := do
  let divisor ← readVReg vd
  let q ← readVReg vq
  if divisor = 0#64 ∧ q ≠ (-1 : BitVec 64) then
    throw (Error.Assertion "VirtualAssertValidDiv0: divisor = 0 but quotient ≠ -1")
  else
    pure RETIRE_SUCCESS

/-- `VirtualSignExtendWord vd, vs1`: sign-extend the low 32 bits of
    virtual `vs1` to 64 bits, write virtual `vd`. -/
def vreg_sign_extend_word (vd vs1 : BitVec 7) : JoltMonad ExecutionResult := do
  let v ← readVReg vs1
  writeVReg vd (sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0))
  pure RETIRE_SUCCESS

/-- `VirtualSignExtendWord vd, rs1`: sign-extend the low 32 bits of
    *real* `rs1` to 64 bits, write virtual `vd`. -/
def vreg_sign_extend_word_from_real
    (vd : BitVec 7) (rs1 : regidx) : JoltMonad ExecutionResult := do
  let v ← liftSail (rX_bits rs1)
  writeVReg vd (sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0))
  pure RETIRE_SUCCESS

/-- `VirtualSignExtendWord rd, vs1`: sign-extend the low 32 bits of
    virtual `vs1` to 64 bits, write *real* `rd`. -/
def vreg_sign_extend_word_to_real
    (rd : regidx) (vs1 : BitVec 7) : JoltMonad ExecutionResult := do
  let v ← readVReg vs1
  liftSail (wX_bits rd (sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0)))
  pure RETIRE_SUCCESS

/-- 32-bit version of `change_divisor_value`: the dividend and divisor
    arguments are sign-extended 32-bit values living in 64-bit BitVecs.
    The overflow pair is `(i32::MIN, -1)`, where `i32::MIN` sign-extended
    to 64 bits is `0xFFFFFFFF80000000`. Matches the Rust impl in
    `tracer/src/instruction/virtual_change_divisor_w.rs`. -/
def change_divisor_w_value (dividend divisor : BitVec 64) : BitVec 64 :=
  let i32MinSext : BitVec 64 := -((1 : BitVec 64) <<< 31)
  let negOne     : BitVec 64 := -1
  if dividend = i32MinSext ∧ divisor = negOne then 1 else divisor

/-- `VirtualChangeDivisorW vd, vs1, vs2`: 32-bit version of
    `vreg_change_divisor`, taking sign-extended dividend `vs1` and
    sign-extended divisor `vs2` from virtual registers. -/
def vreg_change_divisor_w
    (vd vs1 vs2 : BitVec 7) : JoltMonad ExecutionResult := do
  let dividend ← readVReg vs1
  let divisor  ← readVReg vs2
  writeVReg vd (change_divisor_w_value dividend divisor)
  pure RETIRE_SUCCESS

end
