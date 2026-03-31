-- TODO: This file depends on sorry'd lemmas in Common.lean (wX_rX_roundtrip, wX_wX_collapse)
-- TODO: Main theorem needs shift-truncation commutativity BitVec lemma
import JoltBytecode.SailJoltState.Common

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SLLIW: Jolt SLLI + VirtualSignExtendWord = Sail SLLIW

Jolt decomposes SLLIW into: shift left (via SHIFTIOP SLLI), then VirtualSignExtendWord.
Sail's execute_SHIFTIWOP does: extract 32 bits, shift, sign-extend, write.

The key difference from ADDW: the Sail side extracts 32 bits BEFORE the shift,
while Jolt does the full 64-bit shift then sign-extends. These produce the same
result because left-shifting then truncating = truncating then left-shifting
(for shifts < 32 bits).
-/

-- Factored Sail SLLIW
theorem execute_SHIFTIWOP_SLLIW_eq_factored (shamt : BitVec 5) (rs1 rd : regidx) :
    execute_SHIFTIWOP shamt rs1 rd sopw.SLLIW = (do
      let v1 ← rX_bits rs1
      let rs1_32 := Sail.BitVec.extractLsb v1 31 0
      wX_bits rd (sign_extend (m := 64) (shift_bits_left rs1_32 shamt))
      pure RETIRE_SUCCESS) := by
  simp [execute_SHIFTIWOP]

-- Jolt's SLLIW: SLLI (64-bit shift) then VirtualSignExtendWord.
-- Uses execute_SHIFTIOP with the shamt zero-extended to 6 bits.
def jolt_slliw (shamt : BitVec 5) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let _ ← liftSail (execute_SHIFTIOP (shamt.setWidth 6) rs1 rd sop.SLLI)
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

-- Main theorem
theorem jolt_slliw_eq_sail (shamt : BitVec 5) (rs1 rd : regidx) (js : JoltState) :
    projectResult ((jolt_slliw shamt rs1 rd).run js) =
    (execute_SHIFTIWOP shamt rs1 rd sopw.SLLIW).run (project js) := by
  rw [execute_SHIFTIWOP_SLLIW_eq_factored]
  simp only [jolt_slliw, jolt_virtual_sign_extend_word,
        liftSail, projectResult, project,
        bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
  simp only [execute_SHIFTIOP, bind, EStateM.bind, pure, EStateM.pure]
  cases rX_bits rs1 ⟨js.regs, js.choiceState, js.mem, js.tags, js.cycleCount, js.sailOutput⟩ with
  | error e s => simp
  | ok v1 s1 =>
    simp
    -- Jolt writes shift_bits_left v1 shamt' to rd, then reads back, sign-extends.
    -- Sail writes sign_extend(shift_bits_left (extractLsb v1 31 0) shamt) to rd.
    -- Need: sign_extend(extractLsb(shift_bits_left v1 shamt')) = sign_extend(shift_bits_left (extractLsb v1) shamt)
    -- This requires a BitVec lemma about shift then truncate = truncate then shift.
    -- For now, use the write-then-read pattern.
    sorry

end
