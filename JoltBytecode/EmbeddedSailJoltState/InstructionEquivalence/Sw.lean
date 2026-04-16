import JoltBytecode.EmbeddedSailJoltState.Defs
import JoltBytecode.EmbeddedSailJoltState.MemoryUtils
import JoltBytecode.EmbeddedSailJoltState.MemoryWriteReasoning
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
-- rs2 contains the actual value to be written 
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


/-- Jolt's SW decomposition up to just before the final `SD`. -/
def jolt_sw_compute_splice (imm : BitVec 12) (rs2 rs1 : regidx) :
    JoltMonad (BitVec 64 × BitVec 64 × BitVec 64) := do
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
        let base' ← readVReg 1
        let dword_new ← readVReg 2
        pure (ea, base', dword_new)
    | _ => throw (Error.Assertion "SW prefix: vreg_LD did not retire successfully")

/-- Jolt's SW decomposition: 13-step read-modify-write via dword-aligned access. -/
def jolt_sw (imm : BitVec 12) (rs2 rs1 : regidx) : JoltMonad ExecutionResult := do
  let _ ← jolt_sw_compute_splice imm rs2 rs1
  let _ ← vreg_SD 1 2 0
  pure RETIRE_SUCCESS
-- ============================================================================
-- Layer 2: The XOR-AND-XOR splice is correct (pure bitvector reasoning)
-- ============================================================================

-- This is the pure bitvector term computed by the inline SW sequence.
-- It replaces a 32-bit window inside a dword by masking, shifting, and XORing.
def xor_and_xor_splice (dword_orig : BitVec 64) (word_val : BitVec 32) (shift : Nat) : BitVec 64 :=
  let w_ext : BitVec 64 := (word_val.zeroExtend 64) <<< shift
  let mask : BitVec 64 := (0x00000000FFFFFFFF : BitVec 64) <<< shift
  dword_orig ^^^ ((dword_orig ^^^ w_ext) &&& mask)

-- `spliced` is obtained from `original` by replacing the 4 bytes
-- starting at `offset` with the bytes of `word`.
-- Given two 64-bit strings `original` and `spliced`, a target 32-bit string `word`,
-- and a natural number `offset`, this predicate asserts that
-- 1. `spliced[offset + j] = word[j]` for all `j ∈ {0,1,2,3}`;
-- 2. `spliced[k] = original[k]` for all `k < offset` or `k ≥ offset + 4`.
-- NOTE: if spliced, orignal and word satisfy these conditons, the SW at base + off with word 
-- is the same as SD at base with spliced
def IsWordSplice (original spliced : BitVec 64) (word : BitVec 32) (offset : Nat) : Prop :=
  (∀ j : Nat, j < 4 →
    dword_byte spliced (offset + j) = word_byte word j) ∧
  (∀ k : Nat, k < 8 →
    (k < offset ∨ k ≥ offset + 4) →
    dword_byte spliced k = dword_byte original k)

-- A word store inside a dword can start only at byte 0 or byte 4.
-- In other words, the effective address is `base + off` with `off = 0` or `off = 4`.
theorem sw_splice_offset_cases (ea base : BitVec 64) (hsetup : DwordStoreSetup ea base) :
    let off := (ea - base).toNat
    off = 0 ∨ off = 4 := by
  simpa using store_offset_cases ea base hsetup

-- The target bytes of the splice are the bytes of `word_val`.
-- Thus the splice replaces either bytes `0..3` or bytes `4..7` of the dword.
theorem sw_splice_target_bytes (dword_orig : BitVec 64) (word_val : BitVec 32)
    (off : Nat) (hoff : off = 0 ∨ off = 4) :
    ∀ j : Nat, j < 4 →
      dword_byte (xor_and_xor_splice dword_orig word_val (8 * off)) (off + j) =
      word_byte word_val j := by
  intro j hj
  rcases hoff with rfl | rfl
  · interval_cases j <;> simp [xor_and_xor_splice, dword_byte, word_byte] <;> bv_decide
  · interval_cases j <;> simp [xor_and_xor_splice, dword_byte, word_byte] <;> bv_decide

-- The non-target bytes of the splice remain unchanged.
-- Only one 4-byte window is replaced, so the other 4 bytes are preserved.
theorem sw_splice_other_bytes (dword_orig : BitVec 64) (word_val : BitVec 32)
    (off : Nat) (hoff : off = 0 ∨ off = 4) :
    ∀ k : Nat, k < 8 →
      (k < off ∨ k ≥ off + 4) →
      dword_byte (xor_and_xor_splice dword_orig word_val (8 * off)) k =
      dword_byte dword_orig k := by
  intro k hk hout
  rcases hoff with rfl | rfl
  · interval_cases k
    · omega
    · omega
    · omega
    · omega
    · simp [xor_and_xor_splice, dword_byte]
      bv_decide
    · simp [xor_and_xor_splice, dword_byte]
      bv_decide
    · simp [xor_and_xor_splice, dword_byte]
      bv_decide
    · simp [xor_and_xor_splice, dword_byte]
      bv_decide
  · interval_cases k
    · simp [xor_and_xor_splice, dword_byte]
      bv_decide
    · simp [xor_and_xor_splice, dword_byte]
      bv_decide
    · simp [xor_and_xor_splice, dword_byte]
      bv_decide
    · simp [xor_and_xor_splice, dword_byte]
      bv_decide
    · omega
    · omega
    · omega
    · omega

-- The XOR-AND-XOR expression computes the expected splice.
-- Here `spliced` denotes the dword produced by the bitvector sequence.
-- The main LAYER 2 lemma.
theorem sw_splice_spec (dword_orig : BitVec 64) (word_val : BitVec 32)
    (off : Nat) (hoff : off = 0 ∨ off = 4) :
    let spliced := xor_and_xor_splice dword_orig word_val (8 * off)
    IsWordSplice dword_orig spliced word_val off := by
  dsimp [IsWordSplice]
  refine ⟨?_, ?_⟩
  · intro j hj
    simpa using sw_splice_target_bytes dword_orig word_val off hoff j hj
  · intro k hk hout
    simpa using sw_splice_other_bytes dword_orig word_val off hoff k hk hout
end
