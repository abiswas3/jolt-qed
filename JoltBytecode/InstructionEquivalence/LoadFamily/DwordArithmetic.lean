import JoltBytecode.InstructionEquivalence.Memory.Utils
import JoltBytecode.InstructionEquivalence.LoadDefUtils
import Mathlib.Tactic.IntervalCases

set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

/-!
# Pure dword-arithmetic helpers for the Jolt load family

This file collects every fact that is purely about

* extracting a byte / word / (TODO: halfword) slice from a 64-bit dword,
* how those slices relate to the hashmap-keyed `loaded_byte_at` /
  `loaded_word_at` calls the Sail side uses,
* how a 64-bit address decomposes as `(addr & -8)` plus the low-3-bit offset,
* the pure bit-vector identities that express a Jolt inline-sequence's
  logic-phase output as `sign_extend (byte_of_dword d k)` or
  `sign_extend (word_of_dword d k)`.

There are no monads here, no Sail pipeline reductions, no instruction-specific
signatures. Every load instruction (`LB`, `LBU`, `LH`, `LHU`, `LW`, `LWU`)
reuses the helpers in this file when closing its bridge lemma.

## What lives here (by shape)

* Slice definitions (`def`): `byte_of_dword`, `word_of_dword`.
* Slice-of-dword-equals-direct-load lemmas: `loaded_dword_byte_k`,
  `loaded_dword_word_k`, `word_of_dword_eq_bytes`.
* Address-decomposition facts: `addr_split_aligned_offset`,
  `addr_and_seven_lt_eight`, `addr_and_seven_word_lt_five`,
  `word_offset_cases`.
* Memory-shape bridges: `loaded_byte_in_dword`, `loaded_word_in_dword`.
* Jolt logic-phase bit-vector identities: `sll_srai_extracts_byte`,
  `srl_sign_extend_word_extracts_word`.
-/

-- ============================================================================
-- Slice definitions
-- ============================================================================

/-- The `k`-th byte (0-indexed from the low end) of a 64-bit dword. -/
def byte_of_dword (d : BitVec 64) (k : Nat) : BitVec 8 :=
  (d >>> (8 * k)).setWidth 8

/-- The halfword starting at byte-position `k` of a 64-bit dword. Well-
    defined for `k ∈ 0..6`. -/
def halfword_of_dword (d : BitVec 64) (k : Nat) : BitVec 16 :=
  (d >>> (8 * k)).setWidth 16

/-- The word starting at byte-position `k` of a 64-bit dword. Well-defined for
    `k ∈ 0..4`. -/
def word_of_dword (d : BitVec 64) (k : Nat) : BitVec 32 :=
  (d >>> (8 * k)).setWidth 32

-- ============================================================================
-- Slice-of-loaded-dword identities
-- ============================================================================

/-- The `k`-th byte of the loaded dword at `V` is the same as the direct byte
    load at `V + k`. Case-bashes on `k ∈ 0..7`. -/
theorem loaded_dword_byte_k (s : SailState) (V : BitVec 64) (k : Nat)
    (hk : k < 8) :
    byte_of_dword (loaded_dword_at s V) k =
    loaded_byte_at s (V + BitVec.ofNat 64 k) := by
  unfold byte_of_dword loaded_dword_at
  interval_cases k <;> bv_decide

/-- A 16-bit halfword of a dword is the concatenation of its two bytes
    (little-endian). Side condition `k < 7` because the halfword must fit
    within the dword's 8 bytes. -/
theorem halfword_of_dword_eq_bytes (d : BitVec 64) (k : Nat)
    (hk : k < 7) :
    halfword_of_dword d k =
    byte_of_dword d (k + 1) ++ byte_of_dword d k := by
  unfold halfword_of_dword byte_of_dword
  interval_cases k <;> bv_decide

/-- The halfword starting at byte-offset `k` of the loaded dword at `V` is
    the same as the direct halfword load at `V + k`. Stated in the
    *unfolded* shift-and-setWidth form (matching the convention of
    `loaded_dword_word_k`). -/
theorem loaded_dword_halfword_k (s : SailState) (V : BitVec 64) (k : Nat)
    (hk : k < 7) :
    ((loaded_dword_at s V) >>> (8 * k)).setWidth 16 =
    loaded_halfword_at s (V + BitVec.ofNat 64 k) := by
  change halfword_of_dword (loaded_dword_at s V) k =
    loaded_halfword_at s (V + BitVec.ofNat 64 k)
  rw [halfword_of_dword_eq_bytes (loaded_dword_at s V) k hk]
  unfold loaded_halfword_at
  rw [loaded_dword_byte_k s V (k + 1) (by omega), loaded_dword_byte_k s V k (by omega)]
  have haddr : V + BitVec.ofNat 64 (k + 1) = (1 : BitVec 64) + (V + BitVec.ofNat 64 k) := by
    interval_cases k <;> bv_decide
  rw [haddr]
  have haddr' : (1 : BitVec 64) + (V + BitVec.ofNat 64 k) = V + BitVec.ofNat 64 k + 1 := by
    interval_cases k <;> bv_decide
  rw [haddr']

/-- A 32-bit word of a dword is the concatenation of its four bytes (little-
    endian). Side condition `k < 5` because the word must fit within the
    dword's 8 bytes. -/
theorem word_of_dword_eq_bytes (d : BitVec 64) (k : Nat)
    (hk : k < 5) :
    word_of_dword d k =
    byte_of_dword d (k + 3) ++ byte_of_dword d (k + 2) ++
    byte_of_dword d (k + 1) ++ byte_of_dword d k := by
  unfold word_of_dword byte_of_dword
  interval_cases k <;> bv_decide

/-- The word starting at byte-offset `k` of the loaded dword at `V` is the
    same as the direct word load at `V + k`. Proof: decompose the word into
    four bytes via `word_of_dword_eq_bytes`, then translate each byte via
    `loaded_dword_byte_k`. Stated in the *unfolded* shift-and-setWidth form
    to match LW's `word_of_dword` unfolding style. -/
theorem loaded_dword_word_k (s : SailState) (V : BitVec 64) (k : Nat)
    (hk : k < 5) :
    ((loaded_dword_at s V) >>> (8 * k)).setWidth 32 =
    loaded_word_at s (V + BitVec.ofNat 64 k) := by
  change word_of_dword (loaded_dword_at s V) k =
    loaded_word_at s (V + BitVec.ofNat 64 k)
  rw [word_of_dword_eq_bytes (loaded_dword_at s V) k hk]
  unfold loaded_word_at
  rw [loaded_dword_byte_k s V (k + 3) (by omega)]
  rw [loaded_dword_byte_k s V (k + 2) (by omega)]
  rw [loaded_dword_byte_k s V (k + 1) (by omega)]
  rw [loaded_dword_byte_k s V k (by omega)]
  have h3 : V + BitVec.ofNat 64 (k + 3) = (3 : BitVec 64) + (V + BitVec.ofNat 64 k) := by
    interval_cases k <;> bv_decide
  have h2 : V + BitVec.ofNat 64 (k + 2) = (2 : BitVec 64) + (V + BitVec.ofNat 64 k) := by
    interval_cases k <;> bv_decide
  have h1 : V + BitVec.ofNat 64 (k + 1) = (1 : BitVec 64) + (V + BitVec.ofNat 64 k) := by
    interval_cases k <;> bv_decide
  rw [h3, h2, h1]
  have h3' : (3 : BitVec 64) + (V + BitVec.ofNat 64 k) = V + BitVec.ofNat 64 k + 3 := by
    interval_cases k <;> bv_decide
  have h2' : (2 : BitVec 64) + (V + BitVec.ofNat 64 k) = V + BitVec.ofNat 64 k + 2 := by
    interval_cases k <;> bv_decide
  have h1' : (1 : BitVec 64) + (V + BitVec.ofNat 64 k) = V + BitVec.ofNat 64 k + 1 := by
    interval_cases k <;> bv_decide
  rw [h3', h2', h1']

-- ============================================================================
-- Address decomposition facts
-- ============================================================================

/-- Every 64-bit address splits as `(addr & -8) + (addr & 7)`: the 8-aligned
    base plus the 3-bit byte offset. Pure bit-vector identity. -/
theorem addr_split_aligned_offset (addr : BitVec 64) :
    (addr &&& (-8 : BitVec 64)) + BitVec.ofNat 64 (addr &&& 7).toNat = addr := by
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  bv_decide

/-- The 3-bit offset `(addr & 7)` is always in the range `0..7`. Used as the
    side condition for `loaded_dword_byte_k`. -/
theorem addr_and_seven_lt_eight (addr : BitVec 64) : (addr &&& 7).toNat < 8 := by
  rw [BitVec.toNat_and]
  exact Nat.and_lt_two_pow addr.toNat (by decide : (7 : BitVec 64).toNat < 2^3)

/-- For a 2-aligned address, the 3-bit offset `(addr & 7)` is in the range
    `0..6`. Used as the side condition for `loaded_dword_halfword_k`
    applied to a halfword-aligned address. -/
theorem addr_and_seven_halfword_lt_seven (addr : BitVec 64)
    (halign : addr &&& 1 = 0) :
    (addr &&& 7).toNat < 7 := by
  have hk_lt : (addr &&& 7).toNat < 8 := addr_and_seven_lt_eight addr
  have hk_mod8 : (addr &&& 7).toNat = addr.toNat % 8 := by
    rw [BitVec.toNat_and]
    have h7 : BitVec.toNat (7 : BitVec 64) = 7 := by decide
    rw [h7]
    rw [show (7 : Nat) = 2^3 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  have h_even_addr : addr.toNat % 2 = 0 := by
    have h := congrArg BitVec.toNat halign
    rw [BitVec.toNat_and] at h
    have h1 : BitVec.toNat (1 : BitVec 64) = 1 := by decide
    have h0 : BitVec.toNat (0 : BitVec 64) = 0 := by decide
    rw [h1, h0] at h
    rw [show (1 : Nat) = 2^1 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod] at h
    exact h
  have hk_even : (addr &&& 7).toNat % 2 = 0 := by
    rw [hk_mod8]
    omega
  omega

/-- For a 4-aligned address, the 3-bit offset `(addr & 7)` is in the range
    `0..4`. Used as the side condition for `loaded_dword_word_k` applied to a
    word-aligned address. -/
theorem addr_and_seven_word_lt_five (addr : BitVec 64)
    (halign : addr &&& 3 = 0) :
    (addr &&& 7).toNat < 5 := by
  have hk_mod8 : (addr &&& 7).toNat = addr.toNat % 8 := by
    rw [BitVec.toNat_and]
    have h7 : BitVec.toNat (7 : BitVec 64) = 7 := by decide
    rw [h7]
    rw [show (7 : Nat) = 2^3 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  have h_word_addr : addr.toNat % 4 = 0 := by
    have h := congrArg BitVec.toNat halign
    rw [BitVec.toNat_and] at h
    have h3 : BitVec.toNat (3 : BitVec 64) = 3 := by decide
    have h0 : BitVec.toNat (0 : BitVec 64) = 0 := by decide
    rw [h3, h0] at h
    rw [show (3 : Nat) = 2^2 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod] at h
    exact h
  have hk_mod4 : (addr &&& 7).toNat % 4 = 0 := by
    rw [hk_mod8]
    omega
  have hk_lt : (addr &&& 7).toNat < 8 := addr_and_seven_lt_eight addr
  omega

/-- For a 2-aligned address, the only possible values of the 3-bit offset
    are `0`, `2`, `4`, or `6` (even offsets ≤ 6). -/
theorem halfword_offset_cases (addr : BitVec 64) (halign : addr &&& 1 = 0) :
    (addr &&& 7).toNat = 0 ∨ (addr &&& 7).toNat = 2 ∨
    (addr &&& 7).toNat = 4 ∨ (addr &&& 7).toNat = 6 := by
  have hk_lt : (addr &&& 7).toNat < 7 := addr_and_seven_halfword_lt_seven addr halign
  have hk_even : (addr &&& 7).toNat % 2 = 0 := by
    have hk_mod8 : (addr &&& 7).toNat = addr.toNat % 8 := by
      rw [BitVec.toNat_and]
      have h7 : BitVec.toNat (7 : BitVec 64) = 7 := by decide
      rw [h7]
      rw [show (7 : Nat) = 2^3 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
    have h_even_addr : addr.toNat % 2 = 0 := by
      have h := congrArg BitVec.toNat halign
      rw [BitVec.toNat_and] at h
      have h1 : BitVec.toNat (1 : BitVec 64) = 1 := by decide
      have h0 : BitVec.toNat (0 : BitVec 64) = 0 := by decide
      rw [h1, h0] at h
      rw [show (1 : Nat) = 2^1 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod] at h
      exact h
    rw [hk_mod8]
    omega
  omega

/-- For a 4-aligned address, the only possible values of the 3-bit offset are
    `0` (the word is in the low half of the dword) or `4` (high half). -/
theorem word_offset_cases (addr : BitVec 64) (halign : addr &&& 3 = 0) :
    (addr &&& 7).toNat = 0 ∨ (addr &&& 7).toNat = 4 := by
  have hk_lt : (addr &&& 7).toNat < 5 := addr_and_seven_word_lt_five addr halign
  have hk_mod4 : (addr &&& 7).toNat % 4 = 0 := by
    have hk_mod8 : (addr &&& 7).toNat = addr.toNat % 8 := by
      rw [BitVec.toNat_and]
      have h7 : BitVec.toNat (7 : BitVec 64) = 7 := by decide
      rw [h7]
      rw [show (7 : Nat) = 2^3 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
    have h_word_addr : addr.toNat % 4 = 0 := by
      have h := congrArg BitVec.toNat halign
      rw [BitVec.toNat_and] at h
      have h3 : BitVec.toNat (3 : BitVec 64) = 3 := by decide
      have h0 : BitVec.toNat (0 : BitVec 64) = 0 := by decide
      rw [h3, h0] at h
      rw [show (3 : Nat) = 2^2 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod] at h
      exact h
    rw [hk_mod8]
    omega
  omega

-- ============================================================================
-- Memory-shape bridges: the hashmap key fact for the direct load
-- ============================================================================

/-- The byte at an arbitrary address equals the appropriate byte-slice of the
    enclosing aligned dword. Composes `loaded_dword_byte_k` with
    `addr_split_aligned_offset`. -/
theorem loaded_byte_in_dword (s : SailState) (addr : BitVec 64) :
    loaded_byte_at s addr =
    byte_of_dword
      (loaded_dword_at s (addr &&& (-8 : BitVec 64)))
      (addr &&& 7).toNat := by
  rw [loaded_dword_byte_k s (addr &&& -8) (addr &&& 7).toNat
        (addr_and_seven_lt_eight addr)]
  rw [addr_split_aligned_offset]

/-- The halfword at a 2-aligned address equals the appropriate halfword-
    slice of the enclosing aligned dword. Requires `halign : addr & 1 = 0`. -/
theorem loaded_halfword_in_dword (s : SailState) (addr : BitVec 64)
    (halign : addr &&& 1 = 0) :
    loaded_halfword_at s addr =
    halfword_of_dword
      (loaded_dword_at s (addr &&& (-8 : BitVec 64)))
      (addr &&& 7).toNat := by
  unfold halfword_of_dword
  rw [loaded_dword_halfword_k s (addr &&& -8) (addr &&& 7).toNat
        (addr_and_seven_halfword_lt_seven addr halign)]
  rw [addr_split_aligned_offset]

/-- The word at a 4-aligned address equals the appropriate word-slice of the
    enclosing aligned dword. Requires `halign : addr & 3 = 0`. -/
theorem loaded_word_in_dword (s : SailState) (addr : BitVec 64)
    (halign : addr &&& 3 = 0) :
    loaded_word_at s addr =
    word_of_dword
      (loaded_dword_at s (addr &&& (-8 : BitVec 64)))
      (addr &&& 7).toNat := by
  unfold word_of_dword
  rw [loaded_dword_word_k s (addr &&& -8) (addr &&& 7).toNat
        (addr_and_seven_word_lt_five addr halign)]
  rw [addr_split_aligned_offset]

-- ============================================================================
-- Jolt logic-phase bit-vector identities
-- ============================================================================
-- These say: the 64-bit arithmetic performed by the logic phase of a Jolt
-- load sequence equals the expected `sign_extend (slice_of_dword d k)`. They
-- are the pure bit-vector heart of each instruction's bridge lemma.

/-- Byte-load arithmetic (signed): `XOR addr 7`, `SLL` by 3, `SLL` the dword
    by that, then **arithmetic**-shift right by 56, yields the
    sign-extended byte at offset `(addr & 7)` of the dword. Used by `LB`. -/
theorem sll_srai_extracts_byte (d : BitVec 64) (addr : BitVec 64) :
    (let xor_addr  := addr ^^^ (7 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6   := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted   := shift_bits_left d shift_6
     shift_bits_right_arith shifted (56 : BitVec 6))
    = sign_extend (m := 64) (byte_of_dword d (addr &&& 7).toNat) := by
  unfold byte_of_dword shift_bits_left shift_bits_right_arith sign_extend
    Sail.BitVec.signExtend Sail.BitVec.extractLsb Sail.BitVec.toNatInt
  have hk_lt : (addr &&& 7).toNat < 8 := addr_and_seven_lt_eight addr
  set k := (addr &&& 7).toNat with hk_def
  have hk_eq : addr &&& 7 = BitVec.ofNat 64 k := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, hk_def]
    omega
  interval_cases k <;> bv_decide

/-- Byte-load arithmetic (unsigned): same setup as `sll_srai_extracts_byte`
    but with a **logical** right shift by 56 (zero-fill instead of
    sign-fill), yielding the zero-extended byte at offset `(addr & 7)` of
    the dword. Used by `LBU`. -/
theorem sll_srli_extracts_byte (d : BitVec 64) (addr : BitVec 64) :
    (let xor_addr  := addr ^^^ (7 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6   := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted   := shift_bits_left d shift_6
     shift_bits_right shifted (56 : BitVec 6))
    = zero_extend (m := 64) (byte_of_dword d (addr &&& 7).toNat) := by
  unfold byte_of_dword shift_bits_left shift_bits_right zero_extend
    Sail.BitVec.zeroExtend Sail.BitVec.extractLsb
  have hk_lt : (addr &&& 7).toNat < 8 := addr_and_seven_lt_eight addr
  set k := (addr &&& 7).toNat with hk_def
  have hk_eq : addr &&& 7 = BitVec.ofNat 64 k := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, hk_def]
    omega
  interval_cases k <;> bv_decide

-- The halfword case-by-case helpers below are each `bv_decide` at a fixed
-- offset. `interval_cases` on a 3-bit offset would work in principle but
-- blows up `bv_decide` if combined with arbitrary `k`; fixing `k` makes
-- each branch small.

private lemma sll_srai_extracts_halfword_k0 (d addr : BitVec 64)
    (hk : (addr &&& 7).toNat = 0) :
    (let xor_addr := addr ^^^ (6 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted := shift_bits_left d shift_6
     shift_bits_right_arith shifted (48 : BitVec 6))
    = sign_extend (m := 64) (halfword_of_dword d 0) := by
  unfold halfword_of_dword shift_bits_left shift_bits_right_arith sign_extend
    Sail.BitVec.signExtend Sail.BitVec.extractLsb Sail.BitVec.toNatInt
  have hk_eq : addr &&& 7 = BitVec.ofNat 64 0 := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
  bv_decide

private lemma sll_srai_extracts_halfword_k2 (d addr : BitVec 64)
    (hk : (addr &&& 7).toNat = 2) :
    (let xor_addr := addr ^^^ (6 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted := shift_bits_left d shift_6
     shift_bits_right_arith shifted (48 : BitVec 6))
    = sign_extend (m := 64) (halfword_of_dword d 2) := by
  unfold halfword_of_dword shift_bits_left shift_bits_right_arith sign_extend
    Sail.BitVec.signExtend Sail.BitVec.extractLsb Sail.BitVec.toNatInt
  have hk_eq : addr &&& 7 = BitVec.ofNat 64 2 := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
  bv_decide

private lemma sll_srai_extracts_halfword_k4 (d addr : BitVec 64)
    (hk : (addr &&& 7).toNat = 4) :
    (let xor_addr := addr ^^^ (6 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted := shift_bits_left d shift_6
     shift_bits_right_arith shifted (48 : BitVec 6))
    = sign_extend (m := 64) (halfword_of_dword d 4) := by
  unfold halfword_of_dword shift_bits_left shift_bits_right_arith sign_extend
    Sail.BitVec.signExtend Sail.BitVec.extractLsb Sail.BitVec.toNatInt
  have hk_eq : addr &&& 7 = BitVec.ofNat 64 4 := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
  bv_decide

private lemma sll_srai_extracts_halfword_k6 (d addr : BitVec 64)
    (hk : (addr &&& 7).toNat = 6) :
    (let xor_addr := addr ^^^ (6 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted := shift_bits_left d shift_6
     shift_bits_right_arith shifted (48 : BitVec 6))
    = sign_extend (m := 64) (halfword_of_dword d 6) := by
  unfold halfword_of_dword shift_bits_left shift_bits_right_arith sign_extend
    Sail.BitVec.signExtend Sail.BitVec.extractLsb Sail.BitVec.toNatInt
  have hk_eq : addr &&& 7 = BitVec.ofNat 64 6 := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
  bv_decide

/-- Halfword-load arithmetic (signed): `XOR addr 6`, `SLL` by 3, `SLL` the
    dword by that, then arithmetic-shift right by 48, yields the sign-
    extended halfword at offset `(addr & 7)` of the dword. Requires
    halfword alignment `halign : addr & 1 = 0`. Used by `LH`. Dispatches
    on the four possible halfword offsets (0, 2, 4, 6). -/
theorem sll_srai_extracts_halfword (d : BitVec 64) (addr : BitVec 64)
    (halign : addr &&& 1 = 0) :
    (let xor_addr := addr ^^^ (6 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted := shift_bits_left d shift_6
     shift_bits_right_arith shifted (48 : BitVec 6))
    = sign_extend (m := 64) (halfword_of_dword d (addr &&& 7).toNat) := by
  rcases halfword_offset_cases addr halign with hk | hk | hk | hk
  · rw [hk]
    simpa using sll_srai_extracts_halfword_k0 d addr hk
  · rw [hk]
    simpa using sll_srai_extracts_halfword_k2 d addr hk
  · rw [hk]
    simpa using sll_srai_extracts_halfword_k4 d addr hk
  · rw [hk]
    simpa using sll_srai_extracts_halfword_k6 d addr hk

private lemma sll_srli_extracts_halfword_k0 (d addr : BitVec 64)
    (hk : (addr &&& 7).toNat = 0) :
    (let xor_addr := addr ^^^ (6 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted := shift_bits_left d shift_6
     shift_bits_right shifted (48 : BitVec 6))
    = zero_extend (m := 64) (halfword_of_dword d 0) := by
  unfold halfword_of_dword shift_bits_left shift_bits_right zero_extend
    Sail.BitVec.zeroExtend Sail.BitVec.extractLsb
  have hk_eq : addr &&& 7 = BitVec.ofNat 64 0 := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
  bv_decide

private lemma sll_srli_extracts_halfword_k2 (d addr : BitVec 64)
    (hk : (addr &&& 7).toNat = 2) :
    (let xor_addr := addr ^^^ (6 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted := shift_bits_left d shift_6
     shift_bits_right shifted (48 : BitVec 6))
    = zero_extend (m := 64) (halfword_of_dword d 2) := by
  unfold halfword_of_dword shift_bits_left shift_bits_right zero_extend
    Sail.BitVec.zeroExtend Sail.BitVec.extractLsb
  have hk_eq : addr &&& 7 = BitVec.ofNat 64 2 := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
  bv_decide

private lemma sll_srli_extracts_halfword_k4 (d addr : BitVec 64)
    (hk : (addr &&& 7).toNat = 4) :
    (let xor_addr := addr ^^^ (6 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted := shift_bits_left d shift_6
     shift_bits_right shifted (48 : BitVec 6))
    = zero_extend (m := 64) (halfword_of_dword d 4) := by
  unfold halfword_of_dword shift_bits_left shift_bits_right zero_extend
    Sail.BitVec.zeroExtend Sail.BitVec.extractLsb
  have hk_eq : addr &&& 7 = BitVec.ofNat 64 4 := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
  bv_decide

private lemma sll_srli_extracts_halfword_k6 (d addr : BitVec 64)
    (hk : (addr &&& 7).toNat = 6) :
    (let xor_addr := addr ^^^ (6 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted := shift_bits_left d shift_6
     shift_bits_right shifted (48 : BitVec 6))
    = zero_extend (m := 64) (halfword_of_dword d 6) := by
  unfold halfword_of_dword shift_bits_left shift_bits_right zero_extend
    Sail.BitVec.zeroExtend Sail.BitVec.extractLsb
  have hk_eq : addr &&& 7 = BitVec.ofNat 64 6 := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
  bv_decide

/-- Halfword-load arithmetic (unsigned): same setup as
    `sll_srai_extracts_halfword` but with a **logical** right shift by 48,
    yielding the zero-extended halfword at offset `(addr & 7)` of the
    dword. Used by `LHU`. -/
theorem sll_srli_extracts_halfword (d : BitVec 64) (addr : BitVec 64)
    (halign : addr &&& 1 = 0) :
    (let xor_addr := addr ^^^ (6 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted := shift_bits_left d shift_6
     shift_bits_right shifted (48 : BitVec 6))
    = zero_extend (m := 64) (halfword_of_dword d (addr &&& 7).toNat) := by
  rcases halfword_offset_cases addr halign with hk | hk | hk | hk
  · rw [hk]
    simpa using sll_srli_extracts_halfword_k0 d addr hk
  · rw [hk]
    simpa using sll_srli_extracts_halfword_k2 d addr hk
  · rw [hk]
    simpa using sll_srli_extracts_halfword_k4 d addr hk
  · rw [hk]
    simpa using sll_srli_extracts_halfword_k6 d addr hk

private lemma sll_srli_extracts_word_k0 (d addr : BitVec 64)
    (hk : (addr &&& 7).toNat = 0) :
    (let xor_addr := addr ^^^ (4 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted := shift_bits_left d shift_6
     shift_bits_right shifted (32 : BitVec 6))
    = zero_extend (m := 64) (word_of_dword d 0) := by
  unfold word_of_dword shift_bits_left shift_bits_right zero_extend
    Sail.BitVec.zeroExtend Sail.BitVec.extractLsb
  have hk_eq : addr &&& 7 = BitVec.ofNat 64 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    omega
  bv_decide

private lemma sll_srli_extracts_word_k4 (d addr : BitVec 64)
    (hk : (addr &&& 7).toNat = 4) :
    (let xor_addr := addr ^^^ (4 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted := shift_bits_left d shift_6
     shift_bits_right shifted (32 : BitVec 6))
    = zero_extend (m := 64) (word_of_dword d 4) := by
  unfold word_of_dword shift_bits_left shift_bits_right zero_extend
    Sail.BitVec.zeroExtend Sail.BitVec.extractLsb
  have hk_eq : addr &&& 7 = BitVec.ofNat 64 4 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    omega
  bv_decide

/-- Word-load arithmetic (unsigned): `XOR addr 4`, `SLL` by 3, `SLL` the
    dword by that, then logical-shift right by 32, yields the
    zero-extended word at offset `(addr & 7)` of the dword. Requires word
    alignment `halign : addr & 3 = 0`. Used by `LWU`. Dispatches on the
    two possible word offsets (0, 4). Note: this uses the SLL+SRLI pattern
    (like LB/LH), *not* the SRL+VirtualSignExtendWord pattern that LW
    uses on the signed side. -/
theorem sll_srli_extracts_word (d : BitVec 64) (addr : BitVec 64)
    (halign : addr &&& 3 = 0) :
    (let xor_addr := addr ^^^ (4 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted := shift_bits_left d shift_6
     shift_bits_right shifted (32 : BitVec 6))
    = zero_extend (m := 64) (word_of_dword d (addr &&& 7).toNat) := by
  rcases word_offset_cases addr halign with hk | hk
  · rw [hk]
    simpa using sll_srli_extracts_word_k0 d addr hk
  · rw [hk]
    simpa using sll_srli_extracts_word_k4 d addr hk

/-- Word-load arithmetic: `SLL addr` by 3 and use as shift amount on the
    dword with a logical right shift, then extract the lower 32 bits and
    sign-extend, yields the sign-extended word at offset `(addr & 7)` of the
    dword. Requires word alignment `halign : addr & 3 = 0`. -/
theorem srl_sign_extend_word_extracts_word (d : BitVec 64) (addr : BitVec 64)
    (halign : addr &&& 3 = 0) :
    (let shifted := shift_bits_right d (Sail.BitVec.extractLsb (shift_bits_left addr (3 : BitVec 6)) 5 0)
     sign_extend (m := 64) ((Sail.BitVec.extractLsb shifted 31 0) : BitVec 32))
    = sign_extend (m := 64) (word_of_dword d (addr &&& 7).toNat) := by
  rcases word_offset_cases addr halign with hk | hk
  · rw [hk]
    unfold shift_bits_left shift_bits_right sign_extend word_of_dword
      Sail.BitVec.signExtend Sail.BitVec.extractLsb
    have hk_eq : addr &&& 7 = BitVec.ofNat 64 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]
      omega
    bv_decide
  · rw [hk]
    unfold shift_bits_left shift_bits_right sign_extend word_of_dword
      Sail.BitVec.signExtend Sail.BitVec.extractLsb
    have hk_eq : addr &&& 7 = BitVec.ofNat 64 4 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]
      omega
    bv_decide
