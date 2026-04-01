-- TODO: This file depends on sorry'd lemmas in Common.lean (wX_rX_roundtrip, wX_wX_collapse)
import JoltBytecode.SailJoltState.Common
import JoltBytecode.BytecodeExpansions.Instructions.Sraiw

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SRAIW: Jolt decomposition = Sail SRAIW

## Jolt Decomposition (from Rust)

```rust
asm.emit_i::<VirtualSignExtendWord>(*v_rs1, self.operands.rs1, 0);
asm.emit_vshift_i::<VirtualSRAI>(self.operands.rd, *v_rs1, bitmask);
asm.emit_i::<VirtualSignExtendWord>(self.operands.rd, self.operands.rd, 0);
```

In pseudo-asm (v_rs1 is a virtual register):
```
VirtualSignExtendWord    v_rs1, rs1, 0       -- sign-extend rs1[31:0] to 64, write virtual reg
VirtualSRAI              rd, v_rs1, bitmask   -- read virtual reg, logical right shift, write rd
VirtualSignExtendWord    rd, rd, 0            -- sign-extend rd[31:0] to 64, write rd
```
The bitmask uses 5-bit truncation (shamt & 0x1f).
-/

-- In plain English: The Sail execute_SHIFTIWOP for SRAIW reads rs1,
-- extracts the lower 32 bits, arithmetically right-shifts by shamt,
-- sign-extends to 64, writes to rd, and returns success.
theorem execute_SHIFTIWOP_SRAIW_eq_factored (shamt : BitVec 5) (rs1 rd : regidx) :
    execute_SHIFTIWOP shamt rs1 rd sopw.SRAIW = (do
      let v ← rX_bits rs1
      let rs1_32 := Sail.BitVec.extractLsb v 31 0
      wX_bits rd (sign_extend (m := 64) (shift_bits_right_arith rs1_32 shamt))
      pure RETIRE_SUCCESS) := by
  simp [execute_SHIFTIWOP]

-- In plain English: Jolt decomposes SRAIW into three steps:
-- 1. Read rs1, sign-extend lower 32 bits, write to virtual register 1
-- 2. Read virtual register 1, logical right shift by ctz(bitmask), write to rd
-- 3. Read rd, sign-extend lower 32 bits, write to rd
def jolt_sraiw (shamt : BitVec 5) (rs1 rd : regidx) :
    JoltMonad ExecutionResult := do
  -- Step 1: VirtualSignExtendWord rs1 → virtual register 1
  let v ← liftSail (rX_bits rs1)
  writeVReg 1 (sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0))
  -- Step 2: VirtualSRAI virtual register 1 → rd
  let v_rs1 ← readVReg 1
  liftSail (wX_bits rd (v_rs1 >>> ctz (sraiw_bitmask (shamt.setWidth 64))))
  -- Step 3: VirtualSignExtendWord rd → rd
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

-- Virtual register expansion: writeVReg applied to a JoltState.
@[simp] private lemma writeVReg_apply (vr : BitVec 7) (val : BitVec 64) (js : JoltState) :
    writeVReg vr val js = .ok () { js with vregs := fun r => if r = vr then val else js.vregs r } := rfl

-- Virtual register expansion: readVReg applied to a JoltState.
@[simp] private lemma readVReg_apply (vr : BitVec 7) (js : JoltState) :
    readVReg vr js = .ok (js.vregs vr) js := rfl

-- LHS helper: the three-step Jolt value equals sraiwJolt.
private lemma three_step_eq_sraiwJolt (v : BitVec 64) (shamt : BitVec 5) :
    sign_extend (m := 64)
      (Sail.BitVec.extractLsb
        (sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0) >>>
          ctz (sraiw_bitmask (shamt.setWidth 64))) 31 0) =
    sraiwJolt v (shamt.setWidth 64) := by
  unfold sraiwJolt Jolt.virtualSignExtendWord sign_extend
  simp [Sail.BitVec.signExtend, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb']
  congr 1

-- RHS helper: Sail's SRAIW value equals Riscv.sraiw.
private lemma sail_sraiw_eq_riscv (v : BitVec 64) (shamt : BitVec 5) :
    sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb v 31 0) shamt) =
    Riscv.sraiw v (shamt.setWidth 64) := by
  unfold Riscv.sraiw sign_extend shift_bits_right_arith
  simp [Sail.BitVec.signExtend, Sail.BitVec.toNatInt, Sail.BitVec.extractLsb,
        BitVec.extractLsb, BitVec.extractLsb']

-- Bridge: the three-step Jolt computation produces the same value as Sail's SRAIW.
lemma sraiw_three_step_value (v : BitVec 64) (shamt : BitVec 5) :
    sign_extend (m := 64)
      (Sail.BitVec.extractLsb
        (sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0) >>>
          ctz (sraiw_bitmask (shamt.setWidth 64))) 31 0) =
    sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb v 31 0) shamt) := by
  rw [three_step_eq_sraiwJolt, sail_sraiw_eq_riscv, sraiw_eq_sraiwJolt]

/-! ## Main theorem -/

-- In plain English: Running Jolt's three-step SRAIW decomposition
-- and projecting the result onto Sail state produces exactly the same
-- outcome as running Sail's native SRAIW instruction directly.
theorem jolt_sraiw_eq_sail (shamt : BitVec 5) (rs1 rd : regidx) (js : JoltState) :
    projectResult ((jolt_sraiw shamt rs1 rd).run js) =
    (execute_SHIFTIWOP shamt rs1 rd sopw.SRAIW).run (project js) := by
  rw [execute_SHIFTIWOP_SRAIW_eq_factored]
  simp only [jolt_sraiw, jolt_virtual_sign_extend_word,
        writeVReg_apply, readVReg_apply,
        liftSail, projectResult, project,
        bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
  cases rX_bits rs1 ⟨js.regs, js.choiceState, js.mem, js.tags, js.cycleCount, js.sailOutput⟩ with
  | error e s => simp
  | ok v s1 =>
    simp
    -- Two Sail-visible writes to rd (vreg round-trip is transparent to projection).
    obtain ⟨s2, hw1⟩ := wX_shape rd
        (sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0) >>>
          ctz (sraiw_bitmask (shamt.setWidth 64))) s1
    simp [hw1]
    have hrx := wX_rX_roundtrip rd
        (sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0) >>>
          ctz (sraiw_bitmask (shamt.setWidth 64))) s1 s2 hw1
    simp [hrx]
    rw [sraiw_three_step_value]
    obtain ⟨s3, hw2⟩ := wX_shape rd
        (sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb v 31 0) shamt)) s2
    have hc := wX_wX_collapse rd
        (sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0) >>>
          ctz (sraiw_bitmask (shamt.setWidth 64)))
        (sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb v 31 0) shamt))
        s1 s2 s3 hw1 hw2
    simp [hw2, hc]

end
