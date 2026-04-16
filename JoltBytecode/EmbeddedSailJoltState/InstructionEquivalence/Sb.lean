import JoltBytecode.EmbeddedSailJoltState.Defs
import JoltBytecode.EmbeddedSailJoltState.MemoryUtils
import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
import JoltBytecode.EmbeddedSailJoltState.RtypeW

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

/-!
# SB: Jolt store-byte decomposition

From `tracer/src/instruction/sb.rs::inline_sequence_64`:

    ADDI  v0, rs1, imm                        -- v0 = effective address
    ANDI  v1, v0, -8                          -- v1 = dword-aligned address
    LD    v2, v1, 0                           -- v2 = current dword at aligned addr
    SLLI  v3, v0, 3                           -- v3 = byte offset * 8 (bit offset)
    LUI   v0, 0xff                            -- v0 = 0xFF (byte mask)
    SLL   v0, v0, v3                          -- v0 = mask shifted to target position
    SLL   v3, rs2, v3                         -- v3 = store value shifted to position
    XOR   v3, v2, v3                          -- v3 = dword ^ shifted value
    AND   v3, v3, v0                          -- v3 = (dword ^ shifted value) & mask
    XOR   v2, v2, v3                          -- v2 = dword with byte replaced
    SD    v1, v2, 0                           -- store modified dword back

No alignment check — byte stores are always aligned.

Note: Jolt's LUI in RV64 mode loads the immediate directly (no << 12 shift),
so `LUI v0, 0xff` puts 0xFF into v0.
-/

/-- Jolt's SB decomposition: 11-step read-modify-write via dword-aligned access. -/
def jolt_sb (imm : BitVec 12) (rs2 rs1 : regidx) : JoltMonad ExecutionResult := do
  let base ← liftSail (rX_bits rs1)
  let ea := base + sign_extend (m := 64) imm
  -- ADDI v0, rs1, imm
  writeVReg 0 ea
  -- ANDI v1, v0, -8
  let _ ← vreg_ANDI 1 0 (-8 : BitVec 12)
  -- LD v2, v1, 0
  match ← vreg_LD 2 1 0 with
  | .Retire_Success () =>
      -- SLLI v3, v0, 3
      let _ ← vreg_SLLI 3 0 3
      -- LUI v0, 0xff  (Jolt RV64 LUI loads immediate directly, no << 12)
      writeVReg 0 (0xFF : BitVec 64)
      -- SLL v0, v0, v3
      let _ ← vreg_SLL 0 0 3
      -- SLL v3, rs2, v3  (rs2 is a real register)
      let rs2_val ← liftSail (rX_bits rs2)
      let v3_shift ← readVReg 3
      writeVReg 3 (shift_bits_left rs2_val (Sail.BitVec.extractLsb v3_shift 5 0))
      -- XOR v3, v2, v3
      let _ ← vreg_XOR 3 2 3
      -- AND v3, v3, v0
      let _ ← vreg_AND 3 3 0
      -- XOR v2, v2, v3
      let _ ← vreg_XOR 2 2 3
      -- SD v1, v2, 0
      let _ ← vreg_SD 1 2 0
      pure RETIRE_SUCCESS
  | other => pure other

-- ============================================================================
-- Main theorem: Jolt SB = Sail SB
-- ============================================================================

-- Running Jolt's 11-step SB decomposition and projecting onto Sail state
-- produces exactly the same result as running Sail's native `execute_STORE`
-- at width 1.
theorem jolt_sb_eq_sail (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState) (hwf : WellFormed js) (hcfg : JoltConfig js.sail) :
    projectResult ((jolt_sb imm rs2 rs1).run js) =
    (execute_STORE imm rs2 rs1 1).run js.sail := by
  sorry

end
