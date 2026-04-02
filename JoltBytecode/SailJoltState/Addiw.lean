-- TODO: This file depends on sorry'd lemmas in Common.lean (wX_rX_roundtrip, wX_wX_collapse)
import JoltBytecode.SailJoltState.Common

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# ADDIW: Jolt ADDI + VirtualSignExtendWord = Sail ADDIW

## Instruction (RV64I)

`ADDIW rd, rs1, imm` adds sign-extended immediate to rs1, truncates to 32 bits,
sign-extends to 64 bits, writes to rd.

## Jolt Decomposition

```
ADDI                     rd, rs1, imm    -- add immediate (64-bit)
VirtualSignExtendWord    rd, rd           -- sign-extend lower 32 bits
```

## Proof

Same structure as ADDW: the intermediate ADD write gets read back and
overwritten by the sign-extended result. Uses wX_rX_roundtrip and
wX_wX_collapse from Common.lean.

The key BitVec fact: extractLsb(rs1 + signext(imm), 31, 0) = extractLsb(rs1, 31, 0) + extractLsb(signext(imm), 31, 0)
which follows from extractLsb_add in Common.lean.
-/

-- ============================================================================
-- Factored Sail ADDIW
-- ============================================================================

-- Sail's execute_ADDIW factored: read rs1, add imm, sign-extend 32→64, write rd.
theorem execute_ADDIW_eq_factored (imm : BitVec 12) (rs1 rd : regidx) :
    execute_ADDIW imm rs1 rd = (do
      let v1 ← rX_bits rs1
      let result := v1 + sign_extend (m := 64) imm
      wX_bits rd (sign_extend (m := 64) (Sail.BitVec.extractLsb result 31 0))
      pure RETIRE_SUCCESS) := by
  simp [execute_ADDIW]

-- ============================================================================
-- Jolt ADDIW: ADDI then VirtualSignExtendWord
-- ============================================================================

-- Jolt's ADDIW decomposition: ADDI (full 64-bit add), then sign-extend word.
def jolt_addiw (imm : BitVec 12) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let _ ← liftSail (execute_ITYPE imm rs1 rd iop.ADDI)
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

-- ============================================================================
-- Main theorem: Jolt ADDIW projected = Sail ADDIW
-- ============================================================================

theorem jolt_addiw_eq_sail (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState) :
    projectResult ((jolt_addiw imm rs1 rd).run js) =
    (execute_ADDIW imm rs1 rd).run (project js) := by
  rw [execute_ADDIW_eq_factored]
  simp only [jolt_addiw, jolt_virtual_sign_extend_word,
        liftSail, inject, projectResult, project,
        bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
  -- Unfold execute_ITYPE ADDI: reads rs1, adds signext(imm), writes to rd
  simp only [execute_ITYPE, bind, EStateM.bind, pure, EStateM.pure]
  -- Both sides read rs1
  sail_cases rX_bits rs1 ⟨js.regs, js.choiceState, js.mem, js.tags, js.cycleCount, js.sailOutput⟩
  rename_i v1 s1
  -- Jolt ADDI writes (v1 + signext(imm)) to rd. Sail ADDIW writes sign_extend(extractLsb(v1 + signext(imm))).
  -- Since ADDI writes the same value that ADDIW starts with, and VirtualSignExtendWord
  -- reads it back and sign-extends, the results match.
  -- Step 1: ADDI write succeeds
  obtain ⟨s2, hwx⟩ := wX_shape rd (v1 + sign_extend (m := 64) imm) s1
  simp [hwx]
  -- Step 2: read-back gives the written value
  have hrx := wX_rX_roundtrip rd (v1 + sign_extend (m := 64) imm) s1 s2 hwx
  simp [hrx]
  -- Step 3: the values written are the same (no extractLsb_add needed here —
  -- both sides sign-extend extractLsb of the same value: v1 + signext(imm))
  -- Step 4: double write collapses
  obtain ⟨s3, hwx2⟩ := wX_shape rd
      (sign_extend (m := 64) (Sail.BitVec.extractLsb (v1 + sign_extend (m := 64) imm) 31 0)) s2
  have hcollapse := wX_wX_collapse rd (v1 + sign_extend (m := 64) imm)
      (sign_extend (m := 64) (Sail.BitVec.extractLsb (v1 + sign_extend (m := 64) imm) 31 0))
      s1 s2 s3 hwx hwx2
  simp [hwx2, hcollapse]

end
