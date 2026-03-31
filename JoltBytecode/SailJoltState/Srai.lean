import JoltBytecode.SailJoltState.Common
import JoltBytecode.BytecodeExpansions.Instructions.Srai

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SRAI: Jolt VirtualSRAI via bitmask = Sail SRAI

## Jolt Decomposition

Jolt has no native SRAI. Instead it precomputes a bitmask from the
shift amount:
```
shift   := shamt & 0x3f
ones    := (1 << (64 - shift)) - 1
bitmask := ones << shift
```
and uses VirtualSRAI, which performs arithmetic right shift by
`ctz(bitmask)` bits. The key insight (proved in BytecodeExpansions):
`ctz(bitmask) = shamt`, so the bitmask roundtrip recovers the
original shift amount.
-/

-- In plain English: The Sail execute_SHIFTIOP for SRAI reads rs1,
-- arithmetically right-shifts by shamt, writes to rd, and returns success.
theorem execute_SHIFTIOP_SRAI_eq_factored (shamt : BitVec 6) (rs1 rd : regidx) :
    execute_SHIFTIOP shamt rs1 rd sop.SRAI = (do
      let v ← rX_bits rs1
      wX_bits rd (shift_bits_right_arith v (Sail.BitVec.extractLsb shamt 5 0))
      pure RETIRE_SUCCESS) := by
  simp [execute_SHIFTIOP, LeanRV64D.Functions.log2_xlen]

-- In plain English: Jolt decomposes SRAI by precomputing a bitmask
-- from the shift amount, then performing VirtualSRAI which does
-- arithmetic right shift by ctz(bitmask) bits. Since ctz(bitmask) = shamt,
-- this recovers the original SRAI semantics.
def jolt_srai (shamt : BitVec 6) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let v ← liftSail (rX_bits rs1)
  liftSail (wX_bits rd (v.sshiftRight (ctz (srai_bitmask (shamt.setWidth 64)))))
  pure RETIRE_SUCCESS

-- Bridge: Jolt's sshiftRight via ctz(bitmask) equals Sail's shift_bits_right_arith
-- after extractLsb (which is identity for 6-bit shamt on RV64).
-- Follows from ctz_srai_bitmask and the setWidth/extractLsb roundtrips.
lemma srai_bitmask_eq_arith_shift (v : BitVec 64) (shamt : BitVec 6) :
    v.sshiftRight (ctz (srai_bitmask (shamt.setWidth 64))) =
    shift_bits_right_arith v (Sail.BitVec.extractLsb shamt 5 0) := by
  unfold shift_bits_right_arith
  simp [Sail.BitVec.toNatInt, Sail.BitVec.extractLsb, ctz_srai_bitmask]
  congr 1; omega

/-! ## Main theorem -/

-- In plain English: Running Jolt's SRAI (VirtualSRAI via bitmask)
-- and projecting the result onto Sail state produces exactly the
-- same outcome as running Sail's native SRAI instruction directly.
-- This is the correctness proof that Jolt's decomposition is faithful
-- to the RISC-V specification.
theorem jolt_srai_eq_sail (shamt : BitVec 6) (rs1 rd : regidx) (js : JoltState) :
    projectResult ((jolt_srai shamt rs1 rd).run js) =
    (execute_SHIFTIOP shamt rs1 rd sop.SRAI).run (project js) := by
  rw [execute_SHIFTIOP_SRAI_eq_factored]
  simp only [jolt_srai,
        liftSail, projectResult, project,
        bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
  cases rX_bits rs1 ⟨js.regs, js.choiceState, js.mem, js.tags, js.cycleCount, js.sailOutput⟩ with
  | error e s => simp
  | ok v s1 =>
    simp only [srai_bitmask_eq_arith_shift]
    obtain ⟨regs, cs, mem, tags, cyc, out⟩ := s1
    cases wX_bits rd (shift_bits_right_arith v (Sail.BitVec.extractLsb shamt 5 0))
        ⟨regs, cs, mem, tags, cyc, out⟩ with
    | error e s => obtain ⟨_, _, _, _, _, _⟩ := s; rfl
    | ok _ s2 => obtain ⟨_, _, _, _, _, _⟩ := s2; rfl

end
