import JoltBytecode.EmbeddedSailJoltState.Defs
import JoltBytecode.EmbeddedSailJoltState.MemoryUtils
import Mathlib.Tactic.IntervalCases

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

-- Inputs: ea (effective address), base (dword-aligned base address)
-- Assumptions: none (this is a definition, not a theorem)
-- Bundles the alignment and address relationship for a word store.
-- ea is the effective address (word-aligned), base is ea rounded down to 8.
structure DwordStoreSetup (ea base : BitVec 64) : Prop where
  word_aligned : ea &&& 3 = 0
  base_is_aligned : base = ea &&& (-8 : BitVec 64)
  no_ovf : base.toNat + 7 < 2 ^ 64

-- Inputs: dw (64-bit dword), k (byte index)
-- Assumptions: none
-- Extracts the k-th byte from a 64-bit dword in little-endian order.
-- Byte 0 is bits 7..0, byte 1 is bits 15..8, etc.
def dword_byte (dw : BitVec 64) (k : Nat) : BitVec 8 :=
  dw.extractLsb' (8 * k) 8

-- Inputs: s (Sail state), base (dword-aligned address), dword_new (64-bit value to write)
-- Assumptions: none
-- Constructs the state after writing 8 bytes of dword_new at base..base+7.
-- Uses s.mem.insert to match Sail's writeByte primitive.
-- `|>` is the pipeline operator: `x |>.f a` means `(x).f a`, chaining 8 inserts.
def state_after_dword_store (s : SailState) (base : BitVec 64) (dword_new : BitVec 64) :
    SailState :=
  { s with mem := s.mem
    |>.insert (base.toNat + 0) (dword_byte dword_new 0)
    |>.insert (base.toNat + 1) (dword_byte dword_new 1)
    |>.insert (base.toNat + 2) (dword_byte dword_new 2)
    |>.insert (base.toNat + 3) (dword_byte dword_new 3)
    |>.insert (base.toNat + 4) (dword_byte dword_new 4)
    |>.insert (base.toNat + 5) (dword_byte dword_new 5)
    |>.insert (base.toNat + 6) (dword_byte dword_new 6)
    |>.insert (base.toNat + 7) (dword_byte dword_new 7) }

-- Inputs: k (a natural number)
-- Assumptions: k < 8
-- A small natural number (< 8) fits in 64 bits, so converting to BitVec
-- and back to Nat is the identity: (ofNat 64 k).toNat = k.
theorem ofNat64_toNat (k : Nat) (hk : k < 8) :
    (BitVec.ofNat 64 k).toNat = k := by
  rw [BitVec.toNat_ofNat]
  have hk64 : k < 2 ^ 64 := by omega
  exact Nat.mod_eq_of_lt hk64

-- Inputs: base (64-bit address), k (byte offset)
-- Assumptions: k < 8, base.toNat + 7 < 2^64 (no overflow)
-- Adding a small offset to a 64-bit base does not overflow, so toNat
-- distributes over the addition: (base + k).toNat = base.toNat + k.
theorem toNat_base_add_small (base : BitVec 64) (k : Nat)
    (hk : k < 8) (h_no_ovf : base.toNat + 7 < 2 ^ 64) :
    (base + BitVec.ofNat 64 k).toNat = base.toNat + k := by
  have hk_toNat := ofNat64_toNat k hk
  have hsum : base.toNat + (BitVec.ofNat 64 k).toNat < 2 ^ 64 := by
    rw [hk_toNat]
    omega
  have hadd := BitVec.toNat_add_of_lt (x := base) (y := BitVec.ofNat 64 k) hsum
  rw [hk_toNat] at hadd
  exact hadd

-- Inputs: s (Sail state), ea, base (addresses), dword_new (dword written), k (byte index)
-- Assumptions: DwordStoreSetup ea base, k < 8
-- Binder-style alternative:
--   ∀ k : Nat, ∀ hk : k < 8,
--     let s' := state_after_dword_store s base dword_new
--     let addr := base + BitVec.ofNat 64 k
--     loaded_byte_at s' addr = dword_byte dword_new k
-- After writing dword_new at base, reading back the byte stored at address
-- base + k gives the k-th little-endian byte of dword_new.
-- That is, the 8 bytes at base..base+7 hold the little-endian bytes of dword_new.
theorem stored_dword_bytes (s : SailState) (ea base : BitVec 64) (dword_new : BitVec 64)
    (hsetup : DwordStoreSetup ea base) :
    ∀ k : Nat, k < 8 →
      let s' := state_after_dword_store s base dword_new
      let addr := base + BitVec.ofNat 64 k
      loaded_byte_at s' addr = dword_byte dword_new k := by
  intro k hk
  dsimp
  have haddr := toNat_base_add_small base k hk hsetup.no_ovf
  unfold loaded_byte_at state_after_dword_store dword_byte
  rw [haddr, Std.ExtHashMap.get?_eq_getElem?, ← Std.ExtHashMap.getD_eq_getD_getElem?]
  simp
  interval_cases k <;> simp [Std.ExtHashMap.getD_insert]

-- Inputs: m (hash map), k (inserted key), a (lookup key), v (inserted value)
-- Assumptions: a ≠ k
-- Looking up a different key after an insert gives the same result as before.
theorem extHashMap_get_insert_of_ne {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (m : Std.ExtHashMap α β) (k a : α) (v : β) (h : a ≠ k) :
    (m.insert k v).get? a = m.get? a := by
  rw [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.get?_eq_getElem?]
  rw [Std.ExtHashMap.getElem?_insert]
  by_cases hEq : k == a
  · have : k = a := by simpa using hEq
    exact False.elim (h this.symm)
  · simp [hEq]

-- Inputs: base (start of dword window), a (lookup address), i (byte offset)
-- Assumptions: i < 8, a lies outside the byte window [base, base+7]
-- An address outside the dword window cannot equal any byte address base+i in that window.
theorem outside_dword_window_ne (base a i : Nat) (hi : i < 8)
    (hout : a < base ∨ a ≥ base + 8) :
    a ≠ base + i := by
  intro hEq
  rcases hout with hlt | hge
  · omega
  · omega

-- Inputs: s (Sail state), ea, base (addresses), dword_new (dword written), a (any address)
-- Assumptions: DwordStoreSetup ea base, a is outside base..base+7
-- After writing dword_new at base, all addresses outside the 8-byte range
-- are unchanged in the memory hashmap.
theorem stored_dword_untouched (s : SailState) (ea base : BitVec 64) (dword_new : BitVec 64)
    (hsetup : DwordStoreSetup ea base) :
    ∀ a : Nat, (a < base.toNat ∨ a ≥ base.toNat + 8) →
      (state_after_dword_store s base dword_new).mem.get? a = s.mem.get? a := by
  intro a hout
  unfold state_after_dword_store
  simp only
  rw [extHashMap_get_insert_of_ne
      (((((((s.mem.insert (base.toNat + 0) (dword_byte dword_new 0)).insert (base.toNat + 1)
          (dword_byte dword_new 1)).insert (base.toNat + 2) (dword_byte dword_new 2)).insert
          (base.toNat + 3) (dword_byte dword_new 3)).insert (base.toNat + 4)
          (dword_byte dword_new 4)).insert (base.toNat + 5) (dword_byte dword_new 5)).insert
          (base.toNat + 6) (dword_byte dword_new 6))
      (base.toNat + 7) a (dword_byte dword_new 7)
      (outside_dword_window_ne base.toNat a 7 (by omega) hout)]
  rw [extHashMap_get_insert_of_ne
      ((((((s.mem.insert (base.toNat + 0) (dword_byte dword_new 0)).insert (base.toNat + 1)
          (dword_byte dword_new 1)).insert (base.toNat + 2) (dword_byte dword_new 2)).insert
          (base.toNat + 3) (dword_byte dword_new 3)).insert (base.toNat + 4)
          (dword_byte dword_new 4)).insert (base.toNat + 5) (dword_byte dword_new 5))
      (base.toNat + 6) a (dword_byte dword_new 6)
      (outside_dword_window_ne base.toNat a 6 (by omega) hout)]
  rw [extHashMap_get_insert_of_ne
      (((((s.mem.insert (base.toNat + 0) (dword_byte dword_new 0)).insert (base.toNat + 1)
          (dword_byte dword_new 1)).insert (base.toNat + 2) (dword_byte dword_new 2)).insert
          (base.toNat + 3) (dword_byte dword_new 3)).insert (base.toNat + 4)
          (dword_byte dword_new 4))
      (base.toNat + 5) a (dword_byte dword_new 5)
      (outside_dword_window_ne base.toNat a 5 (by omega) hout)]
  rw [extHashMap_get_insert_of_ne
      ((((s.mem.insert (base.toNat + 0) (dword_byte dword_new 0)).insert (base.toNat + 1)
          (dword_byte dword_new 1)).insert (base.toNat + 2) (dword_byte dword_new 2)).insert
          (base.toNat + 3) (dword_byte dword_new 3))
      (base.toNat + 4) a (dword_byte dword_new 4)
      (outside_dword_window_ne base.toNat a 4 (by omega) hout)]
  rw [extHashMap_get_insert_of_ne
      (((s.mem.insert (base.toNat + 0) (dword_byte dword_new 0)).insert (base.toNat + 1)
          (dword_byte dword_new 1)).insert (base.toNat + 2) (dword_byte dword_new 2))
      (base.toNat + 3) a (dword_byte dword_new 3)
      (outside_dword_window_ne base.toNat a 3 (by omega) hout)]
  rw [extHashMap_get_insert_of_ne
      ((s.mem.insert (base.toNat + 0) (dword_byte dword_new 0)).insert (base.toNat + 1)
          (dword_byte dword_new 1))
      (base.toNat + 2) a (dword_byte dword_new 2)
      (outside_dword_window_ne base.toNat a 2 (by omega) hout)]
  rw [extHashMap_get_insert_of_ne
      (s.mem.insert (base.toNat + 0) (dword_byte dword_new 0))
      (base.toNat + 1) a (dword_byte dword_new 1)
      (outside_dword_window_ne base.toNat a 1 (by omega) hout)]
  rw [extHashMap_get_insert_of_ne
      s.mem (base.toNat + 0) a (dword_byte dword_new 0)
      (outside_dword_window_ne base.toNat a 0 (by omega) hout)]
-- Inputs: word_val (32-bit value), k (byte index)
-- Assumptions: none
-- Extracts the k-th byte from a 32-bit word in little-endian order.
-- Byte 0 is bits 7..0, byte 1 is bits 15..8, etc.
def word_byte (word_val : BitVec 32) (k : Nat) : BitVec 8 :=
  word_val.extractLsb' (8 * k) 8

-- Inputs: s (Sail state), ea (word-aligned address), word_val (32-bit value to write)
-- Assumptions: none
-- Constructs the state after writing 4 bytes of word_val at ea..ea+3.
-- This is what Sail's execute_STORE at width 4 does at the hashmap level.
def state_after_word_store (s : SailState) (ea : BitVec 64) (word_val : BitVec 32) :
    SailState :=
  { s with mem := s.mem
    |>.insert (ea.toNat + 0) (word_byte word_val 0)
    |>.insert (ea.toNat + 1) (word_byte word_val 1)
    |>.insert (ea.toNat + 2) (word_byte word_val 2)
    |>.insert (ea.toNat + 3) (word_byte word_val 3) }

-- Inputs: base (start of word window), a (lookup address), i (byte offset)
-- Assumptions: i < 4, a lies outside the byte window [base, base+3]
-- An address outside the word window cannot equal any byte address base+i in that window.
theorem outside_word_window_ne (base a i : Nat) (hi : i < 4)
    (hout : a < base ∨ a ≥ base + 4) :
    a ≠ base + i := by
  intro hEq
  rcases hout with hlt | hge
  · omega
  · omega

-- Inputs: s (Sail state), ea (word address), word_val (word written), a (any address)
-- Assumptions: a is outside ea..ea+3
-- After writing word_val at ea, all addresses outside the 4-byte range
-- are unchanged in the memory hashmap.
theorem stored_word_untouched (s : SailState) (ea : BitVec 64) (word_val : BitVec 32) :
    ∀ a : Nat, (a < ea.toNat ∨ a ≥ ea.toNat + 4) →
      (state_after_word_store s ea word_val).mem.get? a = s.mem.get? a := by
  intro a hout
  unfold state_after_word_store
  simp only
  rw [extHashMap_get_insert_of_ne
      (((s.mem.insert (ea.toNat + 0) (word_byte word_val 0)).insert (ea.toNat + 1)
          (word_byte word_val 1)).insert (ea.toNat + 2) (word_byte word_val 2))
      (ea.toNat + 3) a (word_byte word_val 3)
      (outside_word_window_ne ea.toNat a 3 (by omega) hout)]
  rw [extHashMap_get_insert_of_ne
      ((s.mem.insert (ea.toNat + 0) (word_byte word_val 0)).insert (ea.toNat + 1)
          (word_byte word_val 1))
      (ea.toNat + 2) a (word_byte word_val 2)
      (outside_word_window_ne ea.toNat a 2 (by omega) hout)]
  rw [extHashMap_get_insert_of_ne
      (s.mem.insert (ea.toNat + 0) (word_byte word_val 0))
      (ea.toNat + 1) a (word_byte word_val 1)
      (outside_word_window_ne ea.toNat a 1 (by omega) hout)]
  rw [extHashMap_get_insert_of_ne
      s.mem (ea.toNat + 0) a (word_byte word_val 0)
      (outside_word_window_ne ea.toNat a 0 (by omega) hout)]

-- Inputs: s (Sail state), ea (word address), word_val (word written), j (byte index)
-- Assumptions: j < 4
-- Reading the byte just written at address ea + j returns the j-th byte of word_val.
theorem stored_word_get?_hit (s : SailState) (ea : BitVec 64) (word_val : BitVec 32) :
    ∀ j : Nat, j < 4 →
      (state_after_word_store s ea word_val).mem.get? (ea.toNat + j) =
      some (word_byte word_val j) := by
  intro j hj
  unfold state_after_word_store
  rw [Std.ExtHashMap.get?_eq_getElem?]
  interval_cases j
  · rw [Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert_self]
    simp
  · rw [Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert_self]
    simp
  · rw [Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert_self]
    simp
  · rw [Std.ExtHashMap.getElem?_insert_self]

-- Inputs: s (Sail state), base (dword address), dword_new (dword written), k (byte index)
-- Assumptions: k < 8
-- Reading the byte just written at address base + k returns the k-th byte of dword_new.
theorem stored_dword_get?_hit (s : SailState) (base : BitVec 64) (dword_new : BitVec 64) :
    ∀ k : Nat, k < 8 →
      (state_after_dword_store s base dword_new).mem.get? (base.toNat + k) =
      some (dword_byte dword_new k) := by
  intro k hk
  unfold state_after_dword_store
  rw [Std.ExtHashMap.get?_eq_getElem?]
  interval_cases k
  · rw [Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert_self]
    simp
  · rw [Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert_self]
    simp
  · rw [Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert_self]
    simp
  · rw [Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert_self]
    simp
  · rw [Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert_self]
    simp
  · rw [Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert,
        Std.ExtHashMap.getElem?_insert_self]
    simp
  · rw [Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert_self]
    simp
  · rw [Std.ExtHashMap.getElem?_insert_self]

-- Inputs: addr (effective address)
-- Assumptions: none
-- Splits a word-aligned address into its dword-aligned base plus the low 3-bit offset.
theorem addr_split_aligned_offset (addr : BitVec 64) :
    (addr &&& (-8 : BitVec 64)) + BitVec.ofNat 64 (addr &&& 7).toNat = addr := by
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  bv_decide

-- Inputs: addr (effective address)
-- Assumptions: addr is word aligned
-- The offset of a word-aligned address within its surrounding dword is either 0 or 4.
theorem word_offset_cases (addr : BitVec 64) (halign : addr &&& 3 = 0) :
    (addr &&& 7).toNat = 0 ∨ (addr &&& 7).toNat = 4 := by
  have hk_lt : (addr &&& 7).toNat < 8 := by
    rw [BitVec.toNat_and]
    exact Nat.and_lt_two_pow addr.toNat (by decide : (7 : BitVec 64).toNat < 2^3)
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
  omega

-- Inputs: ea, base (addresses)
-- Assumptions: DwordStoreSetup ea base
-- The word offset within the dword is either 0 or 4.
theorem store_offset_cases (ea base : BitVec 64) (hsetup : DwordStoreSetup ea base) :
    (ea - base).toNat = 0 ∨ (ea - base).toNat = 4 := by
  rw [hsetup.base_is_aligned]
  rcases word_offset_cases ea hsetup.word_aligned with hk | hk
  · left
    have hsplit := addr_split_aligned_offset ea
    rw [hk] at hsplit
    norm_num at hsplit
    have hsub : ea - (ea &&& (-8 : BitVec 64)) = 0 := by
      rw [hsplit]
      bv_decide
    simpa using congrArg BitVec.toNat hsub
  · right
    have hsplit := addr_split_aligned_offset ea
    rw [hk] at hsplit
    have hsub : ea - (ea &&& (-8 : BitVec 64)) = 4 := by
      rw [← hsplit]
      bv_decide
    simpa using congrArg BitVec.toNat hsub

-- Inputs: ea, base (addresses)
-- Assumptions: DwordStoreSetup ea base
-- The effective address is the dword base plus the 0-or-4 word offset, at the Nat level.
theorem ea_toNat_eq_base_plus_offset (ea base : BitVec 64)
    (hsetup : DwordStoreSetup ea base) :
    ea.toNat = base.toNat + (ea - base).toNat := by
  rcases store_offset_cases ea base hsetup with hoff | hoff
  · have hsub0 : ea - base = (0 : BitVec 64) := by
      apply BitVec.eq_of_toNat_eq
      simpa using hoff
    have hEq : ea = base := by
      have := hsub0
      bv_decide
    subst ea
    simp
  · have hsub4 : ea - base = (4 : BitVec 64) := by
      apply BitVec.eq_of_toNat_eq
      simpa using hoff
    have hEq : ea = base + (4 : BitVec 64) := by
      have := hsub4
      bv_decide
    rw [hEq]
    have hsub : ((base + (4 : BitVec 64)) - base : BitVec 64) = 4 := by
      bv_decide
    rw [hsub]
    have hsum : base.toNat + 4 < 2 ^ 64 := by
      calc
        base.toNat + 4 ≤ base.toNat + 7 := by omega
        _ < 2 ^ 64 := hsetup.no_ovf
    simpa using (BitVec.toNat_add_of_lt (x := base) (y := (4 : BitVec 64)) (by simpa using hsum))

-- Inputs: ea, base (addresses), j (word-byte offset)
-- Assumptions: DwordStoreSetup ea base, j < 4
-- The target dword index base + ((ea-base)+j) is the same address as ea + j.
theorem target_addr_eq (ea base : BitVec 64) (j : Nat)
    (hsetup : DwordStoreSetup ea base) (hj : j < 4) :
    base.toNat + ((ea - base).toNat + j) = ea.toNat + j := by
  rw [ea_toNat_eq_base_plus_offset ea base hsetup]
  omega

-- Inputs: ea, base (addresses), k (dword-byte offset)
-- Assumptions: DwordStoreSetup ea base, k < 8
-- Every dword byte index is either in the target 4-byte subwindow or outside it.
theorem k_in_target_or_outside (ea base : BitVec 64) (k : Nat)
    (hsetup : DwordStoreSetup ea base) (hk : k < 8) :
    (k < (ea - base).toNat ∨ k ≥ (ea - base).toNat + 4) ∨
    ∃ j : Nat, j < 4 ∧ k = (ea - base).toNat + j := by
  by_cases hlt : k < (ea - base).toNat
  · exact Or.inl (Or.inl hlt)
  · by_cases hge : k ≥ (ea - base).toNat + 4
    · exact Or.inl (Or.inr hge)
    · right
      refine ⟨k - (ea - base).toNat, ?_, ?_⟩
      · omega
      · omega

-- Inputs: s (Sail state), addr (memory address), b (byte value)
-- Assumptions:
--   - the memory entry at addr is populated
--   - loaded_byte_at returns b at addr
-- If loaded_byte_at reads b from a populated address, then the underlying get?
-- lookup must be exactly some b.
theorem get?_of_loaded_byte_at_eq
    (s : SailState) (addr : BitVec 64) (b : BitVec 8)
    (hpop : s.mem.get? addr.toNat ≠ none)
    (hload : loaded_byte_at s addr = b) :
    s.mem.get? addr.toNat = some b := by
  unfold loaded_byte_at at hload
  cases hget : s.mem.get? addr.toNat with
  | none =>
      exfalso
      exact hpop hget
  | some v =>
      have hv : v = b := by
        rw [hget] at hload
        simpa using hload
      simp [hv]

-- Inputs: ea, base (addresses), k (dword-window offset)
-- Assumptions:
--   - DwordStoreSetup ea base
--   - k lies outside the 4-byte target subwindow inside the dword
-- The corresponding absolute address base+k lies outside the word-write window ea..ea+3.
theorem outside_target_addr_outside_word_window
    (ea base : BitVec 64) (k : Nat)
    (hsetup : DwordStoreSetup ea base)
    (hout : k < (ea - base).toNat ∨ k ≥ (ea - base).toNat + 4) :
    base.toNat + k < ea.toNat ∨ base.toNat + k ≥ ea.toNat + 4 := by
  rw [ea_toNat_eq_base_plus_offset ea base hsetup]
  omega

-- Inputs: ea, base (addresses), a (lookup address)
-- Assumptions: DwordStoreSetup ea base, a is outside base..base+7
-- If an address lies outside the whole dword window, it also lies outside
-- the 4-byte word window ea..ea+3 inside that dword.
theorem outside_dword_window_implies_outside_word_window
    (ea base : BitVec 64) (a : Nat)
    (hsetup : DwordStoreSetup ea base)
    (hout : a < base.toNat ∨ a ≥ base.toNat + 8) :
    a < ea.toNat ∨ a ≥ ea.toNat + 4 := by
  rcases word_offset_cases ea hsetup.word_aligned with hk | hk
  · have hea : ea.toNat = base.toNat := by
      have hsplit := addr_split_aligned_offset ea
      rw [hk] at hsplit
      simp at hsplit
      have hEq : base = ea := by
        rw [hsetup.base_is_aligned]
        exact hsplit
      exact (congrArg BitVec.toNat hEq).symm
    rw [hea]
    rcases hout with hlt | hge
    · exact Or.inl hlt
    · exact Or.inr (by omega)
  · have hea : ea.toNat = base.toNat + 4 := by
      have hsplit := addr_split_aligned_offset ea
      rw [hk] at hsplit
      simp at hsplit
      have hEq : base + (4 : BitVec 64) = ea := by
        rw [hsetup.base_is_aligned]
        exact hsplit
      have h4 : (4 : BitVec 64).toNat = 4 := by decide
      have hsum : base.toNat + (4 : BitVec 64).toNat < 2 ^ 64 := by
        rw [h4]
        calc
          base.toNat + 4 ≤ base.toNat + 7 := by omega
          _ < 2 ^ 64 := hsetup.no_ovf
      have hnat : (base + (4 : BitVec 64)).toNat = base.toNat + 4 := by
        simpa [h4] using (BitVec.toNat_add_of_lt (x := base) (y := (4 : BitVec 64)) hsum)
      rw [hEq] at hnat
      exact hnat
    rw [hea]
    rcases hout with hlt | hge
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

-- Inputs: m1, m2 (memory hash maps)
-- Assumptions: pointwise equality of get? lookups at every key
-- Two ExtHashMaps are equal if they return the same value at every key.
theorem extHashMap_eq_of_get?_eq
    {m1 m2 : Std.ExtHashMap Nat (BitVec 8)}
    (h : ∀ a : Nat, m1.get? a = m2.get? a) :
    m1 = m2 := by
  apply Std.ExtHashMap.ext_getElem?
  intro a
  simpa [Std.ExtHashMap.get?_eq_getElem?] using h a

-- Inputs: base (start of dword window), a (address in the window)
-- Assumptions: base ≤ a, a < base + 8
-- Any address inside the dword window can be written uniquely as base + k for some k < 8.
theorem eq_base_add_of_mem_dword_window
    (base a : Nat)
    (hlo : base ≤ a) (hhi : a < base + 8) :
    ∃ k : Nat, k < 8 ∧ a = base + k := by
  refine ⟨a - base, ?_, ?_⟩
  · omega
  · omega

-- Inputs: base (start of dword window), m1, m2, orig (memory hash maps)
-- Assumptions:
--   - m1 agrees with orig outside base..base+7
--   - m2 agrees with orig outside base..base+7
--   - m1 and m2 agree on the 8 keys inside base..base+7
-- To prove equality of the two maps, it is enough to compare them on the 8-byte
-- dword window and show both revert to orig outside that window.
theorem mem_eq_of_eq_on_dword_window
    (base : Nat)
    (m1 m2 orig : Std.ExtHashMap Nat (BitVec 8))
    (h1_out : ∀ a : Nat, a < base ∨ a ≥ base + 8 -> m1.get? a = orig.get? a)
    (h2_out : ∀ a : Nat, a < base ∨ a ≥ base + 8 -> m2.get? a = orig.get? a)
    (h_in : ∀ k : Nat, k < 8 -> m1.get? (base + k) = m2.get? (base + k)) :
    m1 = m2 := by
  apply extHashMap_eq_of_get?_eq
  intro a
  by_cases hlo : a < base
  · rw [h1_out a (Or.inl hlo), h2_out a (Or.inl hlo)]
  · by_cases hhi : a ≥ base + 8
    · rw [h1_out a (Or.inr hhi), h2_out a (Or.inr hhi)]
    · have hbase_le : base ≤ a := by omega
      have hbase_hi : a < base + 8 := by omega
      obtain ⟨k, hk, rfl⟩ := eq_base_add_of_mem_dword_window base a hbase_le hbase_hi
      exact h_in k hk

-- Inputs:
--   s          : Sail state before the store
--   ea         : effective address (word-aligned, where the 32-bit word goes)
--   base       : dword-aligned base address (ea rounded down to 8)
--   word_val   : the 32-bit value being stored
--   dword_orig : the 64-bit dword loaded from memory at base (before the store)
--   dword_new  : the spliced 64-bit dword (dword_orig with word_val inserted)
--
-- Assumptions:
--   hsetup     : DwordStoreSetup ea base (alignment, base = ea &&& -8, no overflow)
--   hpop       : the 8 dword bytes at base..base+7 are populated in s.mem
--   hload      : dword_orig was loaded from memory at base
--   hsplice    : dword_new has word_val at the ea offset and dword_orig elsewhere
--
-- Statement:
--   Under populatedness of the dword window, writing dword_new at base produces
--   exactly the same .mem hashmap as writing word_val at ea.
theorem dword_store_splice_eq_word_store_populated
    (s : SailState) (ea base : BitVec 64)
    (word_val : BitVec 32) (dword_orig dword_new : BitVec 64)
    (hsetup : DwordStoreSetup ea base)
    (hpop : ∀ k : Nat, k < 8 -> s.mem.get? (base.toNat + k) ≠ none)
    (hload : ∀ k : Nat, k < 8 →
      dword_byte dword_orig k = loaded_byte_at s (base + BitVec.ofNat 64 k))
    (hsplice_target : ∀ j : Nat, j < 4 →
      dword_byte dword_new ((ea - base).toNat + j) = word_byte word_val j)
    (hsplice_other : ∀ k : Nat, k < 8 →
      (k < (ea - base).toNat ∨ k ≥ (ea - base).toNat + 4) →
      dword_byte dword_new k = dword_byte dword_orig k) :
    (state_after_dword_store s base dword_new).mem =
    (state_after_word_store s ea word_val).mem := by
  apply mem_eq_of_eq_on_dword_window base.toNat
      (state_after_dword_store s base dword_new).mem
      (state_after_word_store s ea word_val).mem
      s.mem
  · intro a ha
    simpa using stored_dword_untouched s ea base dword_new hsetup a ha
  · intro a ha
    have ha_word : a < ea.toNat ∨ a ≥ ea.toNat + 4 :=
      outside_dword_window_implies_outside_word_window ea base a hsetup ha
    simpa using stored_word_untouched s ea word_val a ha_word
  · intro k hk
    rcases k_in_target_or_outside ea base k hsetup hk with hout | ⟨j, hj, hk_eq⟩
    · rw [stored_dword_get?_hit s base dword_new k hk]
      rw [hsplice_other k hk hout]
      have haddr : (base + BitVec.ofNat 64 k).toNat = base.toNat + k :=
        toNat_base_add_small base k hk hsetup.no_ovf
      have hpop' : s.mem.get? (base + BitVec.ofNat 64 k).toNat ≠ none := by
        simpa [haddr] using hpop k hk
      have hload' : loaded_byte_at s (base + BitVec.ofNat 64 k) = dword_byte dword_orig k := by
        simpa using (hload k hk).symm
      have hsome : s.mem.get? (base.toNat + k) = some (dword_byte dword_orig k) := by
        simpa [haddr] using get?_of_loaded_byte_at_eq s (base + BitVec.ofNat 64 k)
          (dword_byte dword_orig k) hpop' hload'
      rw [← hsome]
      have haddr_out : base.toNat + k < ea.toNat ∨ base.toNat + k ≥ ea.toNat + 4 :=
        outside_target_addr_outside_word_window ea base k hsetup hout
      symm
      simpa using stored_word_untouched s ea word_val (base.toNat + k) haddr_out
    · rw [hk_eq]
      rw [stored_dword_get?_hit s base dword_new ((ea - base).toNat + j) (by omega)]
      rw [hsplice_target j hj]
      rw [target_addr_eq ea base j hsetup hj]
      symm
      simpa using stored_word_get?_hit s ea word_val j hj
