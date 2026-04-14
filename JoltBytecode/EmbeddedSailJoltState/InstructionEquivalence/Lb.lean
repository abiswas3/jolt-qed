import JoltBytecode.EmbeddedSailJoltState.MemoryUtils
import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
import JoltBytecode.EmbeddedSailJoltState.RtypeW
import Mathlib.Tactic.IntervalCases

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

/-!
# LB: Jolt load-byte (signed) decomposition

From `tracer/src/instruction/lb.rs::inline_sequence_64`:

    ADDI  v0, rs1, imm         -- real rs1 → virtual v0
    ANDI  v1, v0, -8           -- virtual → virtual
    LD    v1, v1, 0            -- virtual → virtual (memory load)
    XORI  v0, v0, 7            -- virtual → virtual
    SLLI  v0, v0, 3            -- virtual → virtual
    SLL   v1, v1, v0           -- virtual → virtual
    SRAI  rd, v1, 56           -- virtual v1 → real rd (arith-shift + sign-extend)
-/

def jolt_lb (imm : BitVec 12) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  -- ADDI v0, rs1, imm  (real → virtual, inlined)
  let rs1_val ← liftSail (rX_bits rs1)
  writeVReg 0 (rs1_val + sign_extend (m := 64) imm)
  -- ANDI v1, v0, -8
  let _ ← vreg_ANDI 1 0 (-8 : BitVec 12)
  -- LD v1, v1, 0 — the only op in this sequence that can trap; propagate.
  match ← vreg_LD 1 1 0 with
  | .Retire_Success () =>
      -- XORI v0, v0, 7
      let _ ← vreg_XORI 0 0 7
      -- SLLI v0, v0, 3
      let _ ← vreg_SLLI 0 0 3
      -- SLL v1, v1, v0
      let _ ← vreg_SLL 1 1 0
      -- SRAI rd, v1, 56  (virtual → real, inlined)
      let v1_val ← readVReg 1
      liftSail (wX_bits rd (shift_bits_right_arith v1_val (56 : BitVec 6)))
      pure RETIRE_SUCCESS
  | other => pure other

-- ============================================================================
-- Bridge lemma (the mathematical heart of LB).
--
-- Setup: memory is a hashmap keyed by Nat byte-addresses with BitVec 8
-- values. We look at two things:
--   (A) the single byte at `addr`;
--   (B) the 8-byte dword starting at `addr & -8` (nearest 8-byte boundary
--       at or below `addr`).
--
-- The byte in (A) lives inside the dword (B), occupying the bit range
-- `[8k+7 .. 8k]` where `k = addr & 7` (equivalently, `addr mod 8`, a value
-- 0..7). So e.g. for k = 3 the byte spans bits 31..24 of the dword.
--
-- Claim: the sign-extended version of (A) can be recovered from (B) by two
-- shifts:
--   1. Shift the dword LEFT by `(7 - (addr & 7)) * 8` bits — this pushes the
--      target byte all the way to the top of the 64-bit register
--      (bits 63..56).
--   2. Shift the result ARITHMETICALLY RIGHT by 56 — this pulls the byte
--      back down to the low 8 bits; because arithmetic right shift
--      replicates the sign bit, the upper 56 bits become the sign extension.
--
-- Result: a 64-bit value equal to `sign_extend (byte at addr)`.
--
-- Jolt's actual arithmetic computes the left-shift amount as
-- `(addr XOR 7) << 3`: on the low three bits, `addr XOR 7 = 7 - (addr & 7)`,
-- so the low six bits of the product give exactly `(7 - (addr & 7)) * 8`.
-- SLL uses only those six bits, so the shift amount is correct regardless
-- of the high bits of `addr`.
--
-- No assumptions about state beyond the byte values at specific Nat keys
-- in the `mem` hashmap — pure hashmap + bit-vector algebra, no monads,
-- no Sail pipeline.
-- ============================================================================

-- The two halves of the bridge:
--   (1) a hashmap-keying fact saying "byte at addr = byte at offset
--       (addr & 7) of the dword at (addr & -8)", and
--   (2) a pure bit-vector identity saying "Jolt's SLL+SRAI arithmetic on
--       a 64-bit value recovers the sign-extended byte at offset (addr & 7)".
--
-- Both are phrased using `byte_of_dword` below, which returns a clean
-- `BitVec 8` — no dependent-type shenanigans with `extractLsb`'s
-- `BitVec (hi - lo + 1)` return type.

-- Extract one byte (low 8 bits after a right-shift) from a 64-bit value.
-- `k` is the byte position 0..7 (larger values produce zero beyond the top).
def byte_of_dword (d : BitVec 64) (k : Nat) : BitVec 8 :=
  (d >>> (8 * k)).setWidth 8

-- Building block 1 — position extraction for a dword. The k-th byte of
-- `loaded_dword_at s V` equals the direct byte read at `V + k`, for any
-- k in 0..7. No recursion — `loaded_dword_at` is a flat 8-way concat.
theorem loaded_dword_byte_k (s : SailState) (V : BitVec 64) (k : Nat)
    (hk : k < 8) :
    ((loaded_dword_at s V) >>> (8 * k)).setWidth 8 =
    loaded_byte_at s (V + BitVec.ofNat 64 k) := by
  unfold loaded_dword_at
  interval_cases k <;> bv_decide

-- Building block 2 — address decomposition. Every 64-bit address splits
-- uniquely into its 8-byte-aligned base and its 3-bit byte-offset:
-- `addr = (addr & -8) + (addr & 7)`. Pure bit-vector identity.
theorem addr_split_aligned_offset (addr : BitVec 64) :
    (addr &&& (-8 : BitVec 64)) + BitVec.ofNat 64 (addr &&& 7).toNat = addr := by
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  bv_decide

-- Auxiliary: `(addr & 7).toNat < 8` — side condition for the position lemma.
-- Proof: push through `toNat` via `BitVec.toNat_and`, then apply the Nat
-- lemma `Nat.and_lt_two_pow`: for `y < 2^n`, `x &&& y < 2^n`. Here `y = 7`,
-- `n = 3`.
theorem addr_and_seven_lt_eight (addr : BitVec 64) : (addr &&& 7).toNat < 8 := by
  rw [BitVec.toNat_and]
  exact Nat.and_lt_two_pow addr.toNat (by decide : (7 : BitVec 64).toNat < 2^3)

-- Lemma 1: hashmap key fact. The byte at `addr` equals the byte at
-- position `(addr & 7).toNat` of the enclosing dword. Composes the two
-- building blocks above.
theorem loaded_byte_in_dword (s : SailState) (addr : BitVec 64) :
    loaded_byte_at s addr =
    byte_of_dword
      (loaded_dword_at s (addr &&& (-8 : BitVec 64)))
      (addr &&& 7).toNat := by
  unfold byte_of_dword
  rw [loaded_dword_byte_k s (addr &&& -8) (addr &&& 7).toNat
        (addr_and_seven_lt_eight addr)]
  rw [addr_split_aligned_offset]

-- Lemma 2: pure bit-vector identity. Jolt's XOR+SLLI+SLL+SRAI arithmetic
-- on `d` produces the sign-extension of `byte_of_dword d (addr & 7).toNat`.
theorem sll_srai_extracts_byte (d : BitVec 64) (addr : BitVec 64) :
    shift_bits_right_arith
      (shift_bits_left d
        (Sail.BitVec.extractLsb
          (shift_bits_left (addr ^^^ (7 : BitVec 64)) (3 : BitVec 6)) 5 0))
      (56 : BitVec 6)
    = sign_extend (m := 64)
        (byte_of_dword d (addr &&& 7).toNat) := by
  sorry

theorem jolt_lb_bridge (s : SailState) (addr : BitVec 64) :
    (let dword     := loaded_dword_at s (addr &&& (-8 : BitVec 64))
     let xor_addr  := addr ^^^ (7 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6   := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted   := shift_bits_left dword shift_6
     shift_bits_right_arith shifted (56 : BitVec 6))
    = sign_extend (m := 64) (loaded_byte_at s addr) := by
  simp only [sll_srai_extracts_byte, ← loaded_byte_in_dword]

-- ============================================================================
-- Memory pipeline collapse at width 8: under JoltConfig, vmem_read_addr
-- produces the little-endian dword assembled directly from state.mem.
-- Discharges the 5-layer Sail pipeline.
-- ============================================================================

theorem vmem_read_addr_dword_reduces (addr : BitVec 64) (s : SailState)
    (hcfg : JoltConfig s) :
    vmem_read_addr (Virtaddr addr) 0 8 (Load Data) false false false s =
    .ok (Ok (loaded_dword_at s addr)) s := by
  sorry

-- ============================================================================
-- LHS helper: the Jolt LB sequence writes `sign_extend (loaded_bytes_at … 1)`
-- to `rd` and leaves everything else unchanged.
-- ============================================================================

theorem jolt_lb_concrete (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) (hcfg : JoltConfig js.sail)
    (v : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok v js.sail) :
    ∃ js' : SailJoltState,
      (jolt_lb imm rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (loaded_byte_at js.sail (v + sign_extend (m := 64) imm))) := by
  unfold jolt_lb vreg_LD
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
             liftSail, writeVReg, readVReg, modify, modifyGet,
             getThe, MonadStateOf.get, MonadStateOf.modifyGet,
             EStateM.get, EStateM.modifyGet, get, hrx,
             vreg_ANDI_run, if_true]
  rw [vmem_read_addr_dword_reduces _ js.sail hcfg]
  simp only [RETIRE_SUCCESS, vreg_XORI_run, vreg_SLLI_run, vreg_SLL_run, if_true,
             bind, EStateM.bind, pure, EStateM.pure,
             EStateM.get, EStateM.modifyGet]
  simp (config := {decide := true}) only [if_true, if_false]
  -- Normalise the address arithmetic to match the bridge lemma's shape.
  have h_addr_sum : (v + sign_extend (m := 64) imm &&& sign_extend (m := 64) (-8 : BitVec 12))
                      + sign_extend (m := 64) (0 : BitVec 12) =
                    (v + sign_extend (m := 64) imm) &&& (-8 : BitVec 64) := by
    have h0 : sign_extend (m := 64) (0 : BitVec 12) = (0 : BitVec 64) := by decide
    have h8 : sign_extend (m := 64) (-8 : BitVec 12) = (-8 : BitVec 64) := by decide
    rw [h0, h8]
    bv_decide
  have h_xor : v + sign_extend (m := 64) imm ^^^ sign_extend (m := 64) (7 : BitVec 12) =
               (v + sign_extend (m := 64) imm) ^^^ (7 : BitVec 64) := by
    have h7 : sign_extend (m := 64) (7 : BitVec 12) = (7 : BitVec 64) := by decide
    rw [h7]
  rw [h_addr_sum, h_xor]
  rw [jolt_lb_bridge]
  -- Now liftSail (wX_bits rd (sign_extend (loaded_byte_at ...)))
  unfold liftSail
  obtain ⟨s', hw⟩ := wX_shape rd
    (sign_extend (m := 64) (loaded_byte_at js.sail (v + sign_extend (m := 64) imm)))
    js.sail
  rw [hw]
  refine ⟨_, rfl, ?_⟩
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

-- ============================================================================
-- RHS helper: Sail's execute_LOAD at width 1 (signed) writes the same value.
-- ============================================================================

theorem execute_LB_reduces (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) (hcfg : JoltConfig js.sail)
    (v : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok v js.sail) :
    (execute_LOAD imm rs1 rd false 1).run js.sail =
    .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (loaded_byte_at js.sail (v + sign_extend (m := 64) imm)))) := by
  sorry

-- ============================================================================
-- Main theorem: Jolt LB = Sail LB
-- ============================================================================

theorem jolt_lb_eq_sail (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) (hcfg : JoltConfig js.sail) :
    projectResult ((jolt_lb imm rs1 rd).run js) =
    (execute_LOAD imm rs1 rd false 1).run js.sail := by
  obtain ⟨v, hrx⟩ := hwf rs1
  obtain ⟨js', hjolt, hjolt_sail⟩ :=
    jolt_lb_concrete imm rs1 rd hrd js hwf hcfg v hrx
  have hsail := execute_LB_reduces imm rs1 rd js hwf hcfg v hrx
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail, hsail]

end
