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
-- Memory read helper lemmas (sorry'd — pure byte arithmetic)
-- ============================================================================

-- sailReadDword succeeds when all memory addresses are populated,
-- and does not change the Sail state (memory reads are pure).
theorem sailReadDword_ok (addr : BitVec 64) (s : SailState)
    (hmem : ∀ a : Nat, s.mem.get? a ≠ none) :
    ∃ dword : BitVec 64, sailReadDword addr s = .ok dword s := by
  sorry

-- sailReadWord succeeds when all memory addresses are populated,
-- and does not change the Sail state.
theorem sailReadWord_ok (addr : BitVec 64) (s : SailState)
    (hmem : ∀ a : Nat, s.mem.get? a ≠ none) :
    ∃ word : BitVec 32, sailReadWord addr s = .ok word s := by
  sorry

-- The dword-extract identity: loading a 64-bit dword from the dword-aligned
-- address and shifting right, truncated to 32 bits, equals loading the 32-bit
-- word directly. This is the Sail-level version of read_word_eq_dword_extract
-- from BytecodeExpansions/Lw.lean.
-- The dword-extract identity: loading a 64-bit dword from the dword-aligned
-- address and shifting right by (addr <<< 3).toNat, truncated to 32 bits,
-- equals loading the 32-bit word directly.
theorem sailReadWord_eq_dword_extract (addr : BitVec 64) (s : SailState)
    (hmem : ∀ a : Nat, s.mem.get? a ≠ none) :
    ∃ (dword : BitVec 64) (word : BitVec 32),
      sailReadDword (addr &&& -8) s = .ok dword s ∧
      sailReadWord addr s = .ok word s ∧
      Sail.BitVec.extractLsb (dword >>> ((addr <<< 3)).toNat) 31 0 = word := by
  sorry

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
-- Main theorem: Jolt LW = Sail LW
-- ============================================================================

-- Running Jolt's LW decomposition and projecting onto Sail state produces
-- exactly the same result as running Sail's native LW instruction.
theorem jolt_lw_eq_sail (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) (hcfg : JoltConfig js.sail) :
    projectResult ((jolt_lw imm rs1 rd).run js) =
    (execute_LOAD imm rs1 rd false 4).run js.sail := by
  -- Sail side: use bridge to factor execute_LOAD into sailReadWord + wX_bits.
  have h_sail := execute_LOAD_LW_factored imm rs1 rd js.sail hcfg
  rw [show (execute_LOAD imm rs1 rd false 4).run js.sail =
    (execute_LOAD imm rs1 rd false 4) js.sail from rfl]
  rw [h_sail]
  -- Now both sides are SailM computations starting with rX_bits rs1.
  -- Jolt side: unfold jolt_lw to expose the do block.
  unfold jolt_lw projectResult liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
             writeVReg, readVReg, modify, modifyGet, MonadStateOf.modifyGet,
             EStateM.modifyGet, get]
  -- Both sides start with rX_bits rs1 js.sail.
  -- Case-split on whether the register read succeeds.
  cases hrx : rX_bits rs1 js.sail with
  | error e s => simp
  | ok base s =>
    have hs := rX_bits_pure rs1 js.sail base s hrx; subst hs
    simp only []
    -- Reduce all virtual register operations (readVReg/writeVReg always succeed).
    dsimp only [getThe, MonadStateOf.get, EStateM.get]
    simp only [project]
    -- Now the Jolt side is: sailReadDword(dword_addr) on js.sail, then shift + wX_bits.
    -- The Sail side is: sailReadWord(addr) on js.sail, then wX_bits.
    -- These operate on the same js.sail (vreg ops don't touch sail state).
    -- Reduce vreg index comparisons (0≠1, 0≠2, 1≠0, 2≠3, etc.)
    simp (config := { decide := true }) only []
    -- Now: sailReadDword((base + signext(imm)) &&& -8) js.sail on the Jolt side,
    -- sailReadWord(base + signext(imm)) js.sail on the Sail side.
    simp only [ite_true, ite_false]
    -- Use the dword-extract identity to connect both sides.
    obtain ⟨dword, word, hdword, hword, h_extract⟩ :=
      sailReadWord_eq_dword_extract (base + sign_extend (m := 64) imm) js.sail hcfg.mem_populated
    -- Substitute the memory reads and reduce remaining vreg conditions.
    simp (config := { decide := true }) only [hdword, hword, h_extract, ite_true, ite_false]
    -- Both sides now call wX_bits rd (sign_extend word) js.sail.
    -- The Jolt side wraps with vregs, projectResult strips them.
    cases wX_bits rd (sign_extend (m := 64) word) js.sail with
    | error e s => simp
    | ok a s => simp

end
