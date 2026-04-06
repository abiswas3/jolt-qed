import JoltBytecode.EmbeddedSailJoltState.RtypeW

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do

set_option autoImplicit true

noncomputable section

/-!
# LW: Jolt load-word decomposition = Sail LW

Jolt decomposes LW into:
1. Read rs1 (base address register)
2. Compute effective address: base + sign_extend(imm)
3. Dword-align the address: addr &&& -8
4. Load 64-bit dword from memory at the aligned address
5. Shift right to extract the 32-bit word
6. Sign-extend to 64 bits and write to rd

The Sail instruction is execute_LOAD imm rs1 rd false 4 (signed, width 4).
-/

-- ============================================================================
-- Jolt LW decomposition (faithful to Jolt bytecode expansion)
-- ============================================================================

-- Jolt's LW decomposition: compute address, dword-align, load dword,
-- shift to extract word, sign-extend, write to rd.
-- Virtual registers store intermediate values between steps.
def jolt_lw (imm : BitVec 12) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  -- Step 1: ADDI — compute effective address
  let base ← liftSail (rX_bits rs1)
  let v_address := base + sign_extend (m := 64) imm
  writeVReg 0 v_address
  -- Step 2: ANDI — dword-align the address
  let v_addr ← readVReg 0
  let v_dword_addr := v_addr &&& (-8 : BitVec 64)
  writeVReg 1 v_dword_addr
  -- Step 3: LD — load 64-bit dword from memory
  let v_dword_addr ← readVReg 1
  let v_dword ← liftSail (sailReadDword v_dword_addr)
  writeVReg 2 v_dword
  -- Step 4: SLLI — compute byte shift amount
  let v_addr ← readVReg 0
  let v_shift := v_addr <<< 3
  writeVReg 3 v_shift
  -- Step 5: SRL — shift dword to extract word
  let v_dword ← readVReg 2
  let v_shift ← readVReg 3
  let v_word := v_dword >>> v_shift.toNat
  -- Step 6: VirtualSignExtendWord — sign-extend lower 32 bits, write to rd
  liftSail (wX_bits rd (sign_extend (m := 64) (Sail.BitVec.extractLsb v_word 31 0)))
  pure RETIRE_SUCCESS

-- ============================================================================
-- Main theorem statement: Jolt LW = Sail LW
-- ============================================================================

-- Running Jolt's LW decomposition and projecting onto Sail state produces
-- exactly the same result as running Sail's native LW instruction.
--
-- The key bridge: Jolt loads a dword from the dword-aligned address and
-- shifts to extract the word. Sail's execute_LOAD with width=4 reads
-- the word directly via vmem_read. Under Jolt's execution assumptions
-- (M-mode, identity translation, flat memory), both produce the same value.
--
-- For LW: is_unsigned = false, width = 4.
-- Under WellFormed (registers readable) and JoltConfig (M-mode, flat memory),
-- Jolt's LW decomposition produces the same result as Sail's execute_LOAD.
--
-- The proof requires two bridges:
-- 1. Register bridge (WellFormed): rX_bits succeeds for rs1 and rd
-- 2. Memory bridge (JoltConfig): vmem_read reduces to sailReadDword,
--    and the dword-shift-extract produces the same 32-bit word as a direct
--    4-byte read at the effective address.
theorem jolt_lw_eq_sail (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) (hcfg : JoltConfig js.sail) :
    projectResult ((jolt_lw imm rs1 rd).run js) =
    (execute_LOAD imm rs1 rd false 4).run js.sail := by
  sorry

end
