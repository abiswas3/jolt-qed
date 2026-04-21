import JoltBytecode.EmbeddedSailJoltState.Defs
import JoltBytecode.EmbeddedSailJoltState.RegisterOps
import JoltBytecode.EmbeddedSailJoltState.RtypeW
import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# DIV: Jolt inline sequence with oracle advice

Transcribed from `tracer/src/instruction/div.rs::inline_sequence`
(XLEN = 64, so `shmat = 63`). The Rust inline sequence contains 18
instructions; each one appears below as a single step with the Rust
mnemonic in the trailing comment.

Virtual register allocation:
```
v0 = a2 = quotient             (from oracle)
v1 = a3 = |remainder|          (from oracle)
v2 = t0 = adjusted divisor
v3 = t1 = temporary
v4 = t2 = temporary
v5 = t3 = temporary
```

The proof structure for DIV will differ from the rest of the ALU family
because correctness relies on (a) oracle advice, (b) constraint
assertions (`VirtualAssertEQ`, `VirtualAssertValidDiv0`,
`VirtualAssertValidUnsignedRemainder`), and (c) special-case handling
for division by zero and signed overflow. The virtual-assert and
change-divisor primitives are stubbed below; their semantics will be
pinned down when the DIV proof is written.
-/

-- ----------------------------------------------------------------------------
-- Virtual assertions: throw `Error.Assertion` on failure
-- ----------------------------------------------------------------------------
-- These instructions are *constraints* in the zkVM; they succeed silently
-- when the predicate holds and abort the Jolt run when it does not.
-- Modelling them as `pure ()` would make completeness vacuous and
-- soundness unstatable, so each one raises `Error.Assertion` on the
-- violated branch.

/-- Pure adjusted-divisor function: returns `dividend` when the pair
would overflow signed division (most-negative ÷ -1), else `divisor`. -/
def change_divisor_value (dividend divisor : BitVec 64) : BitVec 64 :=
  let mostNeg : BitVec 64 := (1 : BitVec 64) <<< 63
  let negOne  : BitVec 64 := -1
  if dividend = mostNeg ∧ divisor = negOne then dividend else divisor

-- ----------------------------------------------------------------------------
-- Jolt-ISA virtual instructions used by DIV
-- ----------------------------------------------------------------------------
-- These mirror Jolt's own `VirtualAdvice`, `VirtualAssert*`, and
-- `VirtualChangeDivisor` bytecode instructions. Each is a one-line
-- combinator so `jolt_div` below reads one Lean line per Rust `emit_X`.

/-- `VirtualAdvice vd, advice`: write the oracle-provided value into a
    virtual register. -/
def vreg_advice (vd : BitVec 7) (advice : BitVec 64) : JoltMonad ExecutionResult := do
  writeVReg vd advice
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

/-- `VirtualChangeDivisor vd, rs1, rs2`: read real `rs1` (dividend) and
    real `rs2` (divisor); if the pair would overflow signed division,
    write the dividend to `vd`, otherwise write the divisor. -/
def vreg_change_divisor (vd : BitVec 7) (rs1 rs2 : regidx) : JoltMonad ExecutionResult := do
  let dividend ← liftSail (rX_bits rs1)
  let divisor ← liftSail (rX_bits rs2)
  writeVReg vd (change_divisor_value dividend divisor)
  pure RETIRE_SUCCESS

/-- `VirtualAssertEQ va, vb`: asserts two virtual registers are equal. -/
def vreg_assert_eq (va vb : BitVec 7) : JoltMonad ExecutionResult := do
  let a ← readVReg va
  let b ← readVReg vb
  if a = b then pure RETIRE_SUCCESS
  else throw (Error.Assertion "VirtualAssertEQ")

/-- `VirtualAssertEQ va, rb`: asserts a virtual register equals a real
    register (used at step 13 to check `t2 = a0`). -/
def vreg_assert_eq_real (va : BitVec 7) (rb : regidx) : JoltMonad ExecutionResult := do
  let a ← readVReg va
  let b ← liftSail (rX_bits rb)
  if a = b then pure RETIRE_SUCCESS
  else throw (Error.Assertion "VirtualAssertEQ (vreg vs real)")

/-- `VirtualAssertValidUnsignedRemainder vr, vd`: asserts
    `vr < vd` unsigned (i.e. `|remainder| < |adjusted divisor|`). -/
def vreg_assert_valid_unsigned_remainder (vr vd : BitVec 7) : JoltMonad ExecutionResult := do
  let r ← readVReg vr
  let d ← readVReg vd
  if r.toNat < d.toNat then pure RETIRE_SUCCESS
  else throw (Error.Assertion "VirtualAssertValidUnsignedRemainder: r ≥ d")

-- ----------------------------------------------------------------------------
-- Jolt DIV inline sequence
-- ----------------------------------------------------------------------------

/-- The Jolt inline expansion of RISC-V `DIV` at `XLEN = 64`. Takes the
oracle's advice (`quotient`, `rem_abs`) as explicit parameters. Each
line below is one Jolt-ISA instruction, mirroring the `emit_X` calls in
`tracer/src/instruction/div.rs::inline_sequence`. -/
def jolt_div (rs2 rs1 rd : regidx)
    (quotient rem_abs : BitVec 64) : JoltMonad ExecutionResult := do
  let _ ← vreg_advice 0 quotient                      -- VirtualAdvice v0, 0    (quotient)
  let _ ← vreg_advice 1 rem_abs                       -- VirtualAdvice v1, 0    (|remainder|)
  let _ ← vreg_assert_valid_div0 rs2 0                -- VirtualAssertValidDiv0 rs2, v0, 0
  let _ ← vreg_change_divisor 2 rs1 rs2               -- VirtualChangeDivisor   v2, rs1, rs2
  let _ ← vreg_MULH 3 0 2                             -- MULH                   v3, v0, v2
  let _ ← vreg_MUL 4 0 2                              -- MUL                    v4, v0, v2
  let _ ← vreg_SRAI 5 4 63                            -- SRAI                   v5, v4, 63
  let _ ← vreg_assert_eq 3 5                          -- VirtualAssertEQ        v3, v5, 0
  let _ ← vreg_SRAI_from_real 3 rs1 63                -- SRAI                   v3, rs1, 63
  let _ ← vreg_XOR 5 1 3                              -- XOR                    v5, v1, v3
  let _ ← vreg_SUB 5 5 3                              -- SUB                    v5, v5, v3
  let _ ← vreg_ADD 4 4 5                              -- ADD                    v4, v4, v5
  let _ ← vreg_assert_eq_real 4 rs1                   -- VirtualAssertEQ        v4, rs1, 0
  let _ ← vreg_SRAI 3 2 63                            -- SRAI                   v3, v2, 63
  let _ ← vreg_XOR 5 2 3                              -- XOR                    v5, v2, v3
  let _ ← vreg_SUB 5 5 3                              -- SUB                    v5, v5, v3
  let _ ← vreg_assert_valid_unsigned_remainder 1 5    -- VirtualAssertValidUnsignedRemainder v1, v5, 0
  vreg_ADDI_to_real rd 0 0                            -- ADDI                   rd, v0, 0   (move quotient)

-- ----------------------------------------------------------------------------
-- Honest advice: the pure value functions that `execute_DIV` and
-- `execute_REM` write to `rd`, extracted directly from the transpiled
-- Sail bodies. These are the definitions of "honest quotient" and
-- "honest remainder" — not a re-implementation of RISC-V semantics, but
-- a re-statement of what the trusted side computes.
-- ----------------------------------------------------------------------------

/-- The pure 64-bit value `execute_DIV rs2 rs1 rd is_unsigned` writes to
`rd`, given the values read from `rs1` and `rs2`. Verbatim copy of the
`execute_DIV` body (minus the monadic read/write/return wrapper),
transcribed from `LeanRV64D/InstsEnd.lean:71105`. -/
def sail_div_value (rs1_bits rs2_bits : BitVec 64) (is_unsigned : Bool) : BitVec 64 :=
  let rs1_int :=
    if (is_unsigned : Bool) then (BitVec.toNatInt rs1_bits) else (BitVec.toInt rs1_bits)
  let rs2_int :=
    if (is_unsigned : Bool) then (BitVec.toNatInt rs2_bits) else (BitVec.toInt rs2_bits)
  let quotient :=
    if ((rs2_int == 0) : Bool) then (Neg.neg 1) else (Int.tdiv rs1_int rs2_int)
  let quotient :=
    if (((!is_unsigned) && (quotient ≥b (2 ^i (LeanRV64D.Functions.xlen -i 1)))) : Bool)
    then (Neg.neg (2 ^i (LeanRV64D.Functions.xlen -i 1))) else quotient
  to_bits_truncate (l := 64) quotient

/-- The pure 64-bit value `execute_REM rs2 rs1 rd is_unsigned` writes to
`rd`. Verbatim copy of the `execute_REM` body, transcribed from
`LeanRV64D/InstsEnd.lean:67637`. -/
def sail_rem_value (rs1_bits rs2_bits : BitVec 64) (is_unsigned : Bool) : BitVec 64 :=
  let rs1_int :=
    if (is_unsigned : Bool) then (BitVec.toNatInt rs1_bits) else (BitVec.toInt rs1_bits)
  let rs2_int :=
    if (is_unsigned : Bool) then (BitVec.toNatInt rs2_bits) else (BitVec.toInt rs2_bits)
  let remainder :=
    if ((rs2_int == 0) : Bool) then rs1_int else (Int.tmod rs1_int rs2_int)
  to_bits_truncate (l := 64) remainder

/-- Factoring lemma: `execute_DIV` collapses to one `rX_bits` per source,
one `wX_bits` of `sail_div_value`, and a `pure RETIRE_SUCCESS`. Proof is
elided while we focus on statements. -/
theorem execute_DIV_factored (rs2 rs1 rd : regidx) (is_unsigned : Bool) :
    execute_DIV rs2 rs1 rd is_unsigned = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sail_div_value v1 v2 is_unsigned)
      pure RETIRE_SUCCESS) := by
  sorry

theorem execute_REM_factored (rs2 rs1 rd : regidx) (is_unsigned : Bool) :
    execute_REM rs2 rs1 rd is_unsigned = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sail_rem_value v1 v2 is_unsigned)
      pure RETIRE_SUCCESS) := by
  sorry

/-- Absolute value of a signed 64-bit bit-vector: `-x` when the MSB is
set, `x` otherwise. The oracle provides `|remainder|` rather than the
signed remainder, so the `rem_abs` advice is `bv_abs ∘ sail_rem_value`. -/
def bv_abs (x : BitVec 64) : BitVec 64 :=
  if x.msb then -x else x

-- ----------------------------------------------------------------------------
-- Completeness
-- ----------------------------------------------------------------------------

/-- **Completeness.** When the oracle's advice is exactly what
`execute_DIV` and `execute_REM` would produce for the current register
values, Jolt's DIV inline sequence (a) never triggers an assertion
failure and (b) leaves the Sail state equal to running `execute_DIV`
directly.

The advice is phrased as `sail_div_value dividend divisor false` and
`bv_abs (sail_rem_value dividend divisor false)` — both pulled from the
trusted side's pure-value bodies, not from a separate reimplementation
of RISC-V division. -/
theorem jolt_div_complete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    projectResult ((jolt_div rs2 rs1 rd
                      (sail_div_value dividend divisor false)
                      (bv_abs (sail_rem_value dividend divisor false))).run js) =
    (execute_DIV rs2 rs1 rd false).run js.sail := by
  sorry

end
