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
# SW: Jolt store-word decomposition

From `tracer/src/instruction/sw.rs::inline_sequence_64`:

    VirtualAssertWordAlignment rs1, imm       -- check 4-byte alignment
    ADDI  v0, rs1, imm                        -- v0 = effective address
    ANDI  v1, v0, -8                          -- v1 = dword-aligned address
    LD    v2, v1, 0                           -- v2 = current dword at aligned addr
    SLLI  v0, v0, 3                           -- v0 = byte offset * 8 (bit offset)
    ORI   v3, x0, -1                          -- v3 = 0xFFFFFFFFFFFFFFFF
    SRLI  v3, v3, 32                          -- v3 = 0x00000000FFFFFFFF (32-bit mask)
    SLL   v3, v3, v0                          -- v3 = mask shifted to target position
    SLL   v0, rs2, v0                         -- v0 = store value shifted to position
    XOR   v0, v2, v0                          -- v0 = dword ^ shifted value
    AND   v0, v0, v3                          -- v0 = (dword ^ shifted value) & mask
    XOR   v2, v2, v0                          -- v2 = dword with word replaced
    SD    v1, v2, 0                           -- store modified dword back

The XOR-AND-XOR pattern: given dword `d`, new word `w` shifted to position,
and mask `m` covering the target 32 bits:
    d ^ ((d ^ w) & m) = (d & ~m) | (w & m)
This replaces exactly the 32 bits under the mask with the new word value.
-/

/-- Jolt's SW decomposition: 13-step read-modify-write via dword-aligned access. -/
def jolt_sw (imm : BitVec 12) (rs2 rs1 : regidx) : JoltMonad ExecutionResult := do
  let base ← liftSail (rX_bits rs1)
  let ea := base + sign_extend (m := 64) imm
  -- VirtualAssertWordAlignment
  if ea &&& 3 ≠ 0 then
    throw (Error.Assertion "SW: effective address not word-aligned")
  else do
    -- ADDI v0, rs1, imm
    writeVReg 0 ea
    -- ANDI v1, v0, -8
    let _ ← vreg_ANDI 1 0 (-8 : BitVec 12)
    -- LD v2, v1, 0
    match ← vreg_LD 2 1 0 with
    | .Retire_Success () =>
        -- SLLI v0, v0, 3
        let _ ← vreg_SLLI 0 0 3
        -- ORI v3, x0, -1  (x0 = 0, imm = -1 sign-extended = allOnes)
        writeVReg 3 0
        let _ ← vreg_ORI 3 3 (-1 : BitVec 12)
        -- SRLI v3, v3, 32
        let _ ← vreg_SRLI 3 3 32
        -- SLL v3, v3, v0
        let _ ← vreg_SLL 3 3 0
        -- SLL v0, rs2, v0  (rs2 is a real register)
        let rs2_val ← liftSail (rX_bits rs2)
        let v0_shift ← readVReg 0
        writeVReg 0 (shift_bits_left rs2_val (Sail.BitVec.extractLsb v0_shift 5 0))
        -- XOR v0, v2, v0
        let _ ← vreg_XOR 0 2 0
        -- AND v0, v0, v3
        let _ ← vreg_AND 0 0 3
        -- XOR v2, v2, v0
        let _ ← vreg_XOR 2 2 0
        -- SD v1, v2, 0
        let _ ← vreg_SD 1 2 0
        pure RETIRE_SUCCESS
    | other => pure other

-- ============================================================================
-- Main theorem: Jolt SW = Sail SW
-- ============================================================================

-- Running Jolt's 13-step SW decomposition (read-modify-write via dword-aligned
-- access) and projecting onto Sail state produces exactly the same result as
-- running Sail's native `execute_STORE` at width 4.
--
-- Assumptions will be refined as we fill in the proof — for now we include
-- the same shape used by the load proofs (WellFormed, JoltConfig) plus
-- placeholders for store-specific conditions (alignment, memory pipeline).
theorem jolt_sw_eq_sail (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState) (hwf : WellFormed js) (hcfg : JoltConfig js.sail) :
    projectResult ((jolt_sw imm rs2 rs1).run js) =
    (execute_STORE imm rs2 rs1 4).run js.sail := by
  sorry

end
