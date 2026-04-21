import JoltBytecode.EmbeddedSailJoltState.Defs
import JoltBytecode.EmbeddedSailJoltState.RegisterOps
import JoltBytecode.EmbeddedSailJoltState.RtypeW

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

/-- `VirtualAssertValidDiv0 divisor, quotient`: if `divisor = 0` then
`quotient` must equal `u64::MAX` (signed `-1`). -/
def jolt_assert_valid_div0 (divisor quotient : BitVec 64) : JoltMonad Unit :=
  if divisor = 0#64 ∧ quotient ≠ (-1 : BitVec 64) then
    throw (Error.Assertion "VirtualAssertValidDiv0: divisor = 0 but quotient ≠ -1")
  else
    pure ()

/-- `VirtualAssertEQ a, b`: asserts `a = b`. -/
def jolt_assert_eq (a b : BitVec 64) : JoltMonad Unit :=
  if a = b then pure () else throw (Error.Assertion "VirtualAssertEQ")

/-- `VirtualAssertValidUnsignedRemainder r, d`: asserts `r < d` unsigned. -/
def jolt_assert_valid_unsigned_remainder (r d : BitVec 64) : JoltMonad Unit :=
  if r.toNat < d.toNat then pure ()
  else throw (Error.Assertion "VirtualAssertValidUnsignedRemainder: r ≥ d")

/-- `VirtualChangeDivisor dividend, divisor`: returns `dividend` if the
pair would overflow signed division (dividend = most-negative and
divisor = -1); otherwise returns `divisor` unchanged. -/
def jolt_change_divisor (dividend divisor : BitVec 64) : BitVec 64 :=
  let mostNeg : BitVec 64 := (1 : BitVec 64) <<< 63
  let negOne  : BitVec 64 := -1
  if dividend = mostNeg ∧ divisor = negOne then dividend else divisor

/-- Upper 64 bits of a signed 64×64 multiply (MULH). -/
def jolt_mulhs (a b : BitVec 64) : BitVec 64 :=
  BitVec.ofInt 64 ((a.toInt * b.toInt) / (2 ^ 64))

-- ----------------------------------------------------------------------------
-- Jolt DIV inline sequence
-- ----------------------------------------------------------------------------

/-- The Jolt inline expansion of RISC-V `DIV` at `XLEN = 64`. Takes the
oracle's advice (`quotient`, `rem_abs`) as explicit parameters. -/
def jolt_div (rs2 rs1 rd : regidx)
    (quotient rem_abs : BitVec 64) : JoltMonad ExecutionResult := do
  -- emit_j VirtualAdvice v0, 0         -- v0 = quotient
  writeVReg 0 quotient
  -- emit_j VirtualAdvice v1, 0         -- v1 = |remainder|
  writeVReg 1 rem_abs
  -- emit_b VirtualAssertValidDiv0 rs2, v0, 0
  let divisor ← liftSail (rX_bits rs2)
  let q0 ← readVReg 0
  jolt_assert_valid_div0 divisor q0
  -- emit_r VirtualChangeDivisor v2, rs1, rs2    -- v2 = adjusted divisor
  let dividend ← liftSail (rX_bits rs1)
  writeVReg 2 (jolt_change_divisor dividend divisor)
  -- emit_r MULH v3, v0, v2             -- v3 = high bits of q × adj_div
  let q1 ← readVReg 0
  let t0a ← readVReg 2
  writeVReg 3 (jolt_mulhs q1 t0a)
  -- emit_r MUL v4, v0, v2              -- v4 = low bits of q × adj_div
  let q2 ← readVReg 0
  let t0b ← readVReg 2
  writeVReg 4 (q2 * t0b)
  -- emit_i SRAI v5, v4, 63             -- v5 = sign extension of v4
  let t2a ← readVReg 4
  writeVReg 5 (t2a.sshiftRight 63)
  -- emit_b VirtualAssertEQ v3, v5, 0
  let t1a ← readVReg 3
  let t3a ← readVReg 5
  jolt_assert_eq t1a t3a
  -- emit_i SRAI v3, rs1, 63            -- v3 = sign bit of dividend
  let dividend' ← liftSail (rX_bits rs1)
  writeVReg 3 (dividend'.sshiftRight 63)
  -- emit_r XOR v5, v1, v3
  let r_abs ← readVReg 1
  let t1b ← readVReg 3
  writeVReg 5 (r_abs ^^^ t1b)
  -- emit_r SUB v5, v5, v3
  let t3b ← readVReg 5
  let t1c ← readVReg 3
  writeVReg 5 (t3b - t1c)
  -- emit_r ADD v4, v4, v5
  let t2b ← readVReg 4
  let t3c ← readVReg 5
  writeVReg 4 (t2b + t3c)
  -- emit_b VirtualAssertEQ v4, rs1, 0
  let t2c ← readVReg 4
  let dividend'' ← liftSail (rX_bits rs1)
  jolt_assert_eq t2c dividend''
  -- emit_i SRAI v3, v2, 63             -- v3 = sign bit of adjusted divisor
  let t0c ← readVReg 2
  writeVReg 3 (t0c.sshiftRight 63)
  -- emit_r XOR v5, v2, v3
  let t0d ← readVReg 2
  let t1d ← readVReg 3
  writeVReg 5 (t0d ^^^ t1d)
  -- emit_r SUB v5, v5, v3              -- v5 = |adjusted divisor|
  let t3d ← readVReg 5
  let t1e ← readVReg 3
  writeVReg 5 (t3d - t1e)
  -- emit_b VirtualAssertValidUnsignedRemainder v1, v5, 0
  let r_abs' ← readVReg 1
  let t3e ← readVReg 5
  jolt_assert_valid_unsigned_remainder r_abs' t3e
  -- emit_i ADDI rd, v0, 0              -- move quotient into rd
  let q3 ← readVReg 0
  liftSail (wX_bits rd q3)
  pure RETIRE_SUCCESS

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
