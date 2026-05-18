import JoltBytecode.InstructionEquivalence.Memory.WriteReasoning

/-!
# Pure splice facts for store-family expansions

The RV64 store inline sequences all use the same read-modify-write idea:

1. load the enclosing 64-bit dword;
2. shift a byte/halfword/word-sized mask into the target lane;
3. shift the low bits of `rs2` into the same lane; and
4. compute `dword ^ ((dword ^ shiftedValue) & shiftedMask)`.

This file proves the non-monadic facts about that expression.  The program
proofs should use these lemmas after the Jolt-ISA execution block has reduced
the bytecode sequence to a concrete spliced dword.
-/

set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace StoreSplice

/-- Facts about an effective address and its enclosing dword address that are
common to all byte/halfword/word store splice proofs.  `ea_toNat` is the Nat
level bridge used when comparing hashmap keys. -/
structure DwordWindowSetup (ea base : BitVec 64) : Prop where
  base_is_aligned : base = ea &&& (-8 : BitVec 64)
  no_ovf : base.toNat + 7 < 2 ^ 64
  ea_toNat : ea.toNat = base.toNat + (ea - base).toNat

/-- Byte-store setup: the target offset may be any byte lane in the dword. -/
structure ByteStoreSetup (ea base : BitVec 64) : Prop extends DwordWindowSetup ea base where
  offset_cases :
    (ea - base).toNat = 0 ∨ (ea - base).toNat = 1 ∨
    (ea - base).toNat = 2 ∨ (ea - base).toNat = 3 ∨
    (ea - base).toNat = 4 ∨ (ea - base).toNat = 5 ∨
    (ea - base).toNat = 6 ∨ (ea - base).toNat = 7

/-- Halfword-store setup: the target offset is one of the four halfword lanes. -/
structure HalfwordStoreSetup (ea base : BitVec 64) : Prop extends DwordWindowSetup ea base where
  halfword_aligned : ea &&& 1 = 0
  offset_cases :
    (ea - base).toNat = 0 ∨ (ea - base).toNat = 2 ∨
    (ea - base).toNat = 4 ∨ (ea - base).toNat = 6

/-- Word-store setup expressed in the same vocabulary as byte/halfword stores. -/
structure WordStoreSetup (ea base : BitVec 64) : Prop extends DwordWindowSetup ea base where
  word_aligned : ea &&& 3 = 0
  offset_cases : (ea - base).toNat = 0 ∨ (ea - base).toNat = 4

/-- The byte-store XOR-mask-XOR expression.  `shift` is measured in bits. -/
def byteSplice (dword_orig : BitVec 64) (byte_val : BitVec 8) (shift : Nat) : BitVec 64 :=
  let b_ext : BitVec 64 := byte_val.zeroExtend 64 <<< shift
  let mask : BitVec 64 := (0x00000000000000FF : BitVec 64) <<< shift
  dword_orig ^^^ ((dword_orig ^^^ b_ext) &&& mask)

/-- The halfword-store XOR-mask-XOR expression.  `shift` is measured in bits. -/
def halfwordSplice (dword_orig : BitVec 64) (halfword_val : BitVec 16) (shift : Nat) :
    BitVec 64 :=
  let h_ext : BitVec 64 := halfword_val.zeroExtend 64 <<< shift
  let mask : BitVec 64 := (0x000000000000FFFF : BitVec 64) <<< shift
  dword_orig ^^^ ((dword_orig ^^^ h_ext) &&& mask)

/-- The word-store XOR-mask-XOR expression.  `shift` is measured in bits. -/
def wordSplice (dword_orig : BitVec 64) (word_val : BitVec 32) (shift : Nat) : BitVec 64 :=
  let w_ext : BitVec 64 := word_val.zeroExtend 64 <<< shift
  let mask : BitVec 64 := (0x00000000FFFFFFFF : BitVec 64) <<< shift
  dword_orig ^^^ ((dword_orig ^^^ w_ext) &&& mask)

/-- `spliced` is obtained from `original` by replacing one byte at `offset`. -/
def IsByteSplice (original spliced : BitVec 64) (byte_val : BitVec 8) (offset : Nat) :
    Prop :=
  (∀ j : Nat, j < 1 →
    dword_byte spliced (offset + j) = byte_byte byte_val j) ∧
  (∀ k : Nat, k < 8 →
    (k < offset ∨ k ≥ offset + 1) →
    dword_byte spliced k = dword_byte original k)

/-- `spliced` is obtained from `original` by replacing two bytes at `offset`. -/
def IsHalfwordSplice (original spliced : BitVec 64) (halfword_val : BitVec 16)
    (offset : Nat) : Prop :=
  (∀ j : Nat, j < 2 →
    dword_byte spliced (offset + j) = halfword_byte halfword_val j) ∧
  (∀ k : Nat, k < 8 →
    (k < offset ∨ k ≥ offset + 2) →
    dword_byte spliced k = dword_byte original k)

/-- `spliced` is obtained from `original` by replacing four bytes at `offset`. -/
def IsWordSplice (original spliced : BitVec 64) (word_val : BitVec 32) (offset : Nat) :
    Prop :=
  (∀ j : Nat, j < 4 →
    dword_byte spliced (offset + j) = word_byte word_val j) ∧
  (∀ k : Nat, k < 8 →
    (k < offset ∨ k ≥ offset + 4) →
    dword_byte spliced k = dword_byte original k)

/-- The byte splice writes the target byte. -/
theorem byteSplice_target_bytes (dword_orig : BitVec 64) (byte_val : BitVec 8)
    (off : Nat)
    (hoff :
      off = 0 ∨ off = 1 ∨ off = 2 ∨ off = 3 ∨
      off = 4 ∨ off = 5 ∨ off = 6 ∨ off = 7) :
    ∀ j : Nat, j < 1 →
      dword_byte (byteSplice dword_orig byte_val (8 * off)) (off + j) =
      byte_byte byte_val j := by
  intro j hj
  rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals interval_cases j <;> simp [byteSplice, dword_byte, byte_byte] <;> bv_decide

/-- The byte splice preserves every non-target byte. -/
theorem byteSplice_other_bytes (dword_orig : BitVec 64) (byte_val : BitVec 8)
    (off : Nat)
    (hoff :
      off = 0 ∨ off = 1 ∨ off = 2 ∨ off = 3 ∨
      off = 4 ∨ off = 5 ∨ off = 6 ∨ off = 7) :
    ∀ k : Nat, k < 8 →
      (k < off ∨ k ≥ off + 1) →
      dword_byte (byteSplice dword_orig byte_val (8 * off)) k =
      dword_byte dword_orig k := by
  intro k hk hout
  rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    interval_cases k <;>
      (first | omega | (simp [byteSplice, dword_byte] <;> bv_decide))

/-- The byte-store XOR-mask-XOR expression is a one-byte splice. -/
theorem byteSplice_spec (dword_orig : BitVec 64) (byte_val : BitVec 8)
    (off : Nat)
    (hoff :
      off = 0 ∨ off = 1 ∨ off = 2 ∨ off = 3 ∨
      off = 4 ∨ off = 5 ∨ off = 6 ∨ off = 7) :
    let spliced := byteSplice dword_orig byte_val (8 * off)
    IsByteSplice dword_orig spliced byte_val off := by
  dsimp [IsByteSplice]
  refine ⟨?_, ?_⟩
  · intro j hj
    simpa using byteSplice_target_bytes dword_orig byte_val off hoff j hj
  · intro k hk hout
    simpa using byteSplice_other_bytes dword_orig byte_val off hoff k hk hout

/-- The halfword splice writes the target two bytes. -/
theorem halfwordSplice_target_bytes (dword_orig : BitVec 64)
    (halfword_val : BitVec 16) (off : Nat)
    (hoff : off = 0 ∨ off = 2 ∨ off = 4 ∨ off = 6) :
    ∀ j : Nat, j < 2 →
      dword_byte (halfwordSplice dword_orig halfword_val (8 * off)) (off + j) =
      halfword_byte halfword_val j := by
  intro j hj
  rcases hoff with rfl | rfl | rfl | rfl
  all_goals interval_cases j <;> simp [halfwordSplice, dword_byte, halfword_byte] <;> bv_decide

/-- The halfword splice preserves every non-target byte. -/
theorem halfwordSplice_other_bytes (dword_orig : BitVec 64)
    (halfword_val : BitVec 16) (off : Nat)
    (hoff : off = 0 ∨ off = 2 ∨ off = 4 ∨ off = 6) :
    ∀ k : Nat, k < 8 →
      (k < off ∨ k ≥ off + 2) →
      dword_byte (halfwordSplice dword_orig halfword_val (8 * off)) k =
      dword_byte dword_orig k := by
  intro k hk hout
  rcases hoff with rfl | rfl | rfl | rfl
  all_goals
    interval_cases k <;>
      (first | omega | (simp [halfwordSplice, dword_byte] <;> bv_decide))

/-- The halfword-store XOR-mask-XOR expression is a two-byte splice. -/
theorem halfwordSplice_spec (dword_orig : BitVec 64) (halfword_val : BitVec 16)
    (off : Nat) (hoff : off = 0 ∨ off = 2 ∨ off = 4 ∨ off = 6) :
    let spliced := halfwordSplice dword_orig halfword_val (8 * off)
    IsHalfwordSplice dword_orig spliced halfword_val off := by
  dsimp [IsHalfwordSplice]
  refine ⟨?_, ?_⟩
  · intro j hj
    simpa using halfwordSplice_target_bytes dword_orig halfword_val off hoff j hj
  · intro k hk hout
    simpa using halfwordSplice_other_bytes dword_orig halfword_val off hoff k hk hout

/-- The word splice writes the target four bytes. -/
theorem wordSplice_target_bytes (dword_orig : BitVec 64) (word_val : BitVec 32)
    (off : Nat) (hoff : off = 0 ∨ off = 4) :
    ∀ j : Nat, j < 4 →
      dword_byte (wordSplice dword_orig word_val (8 * off)) (off + j) =
      word_byte word_val j := by
  intro j hj
  rcases hoff with rfl | rfl
  all_goals interval_cases j <;> simp [wordSplice, dword_byte, word_byte] <;> bv_decide

/-- The word splice preserves every non-target byte. -/
theorem wordSplice_other_bytes (dword_orig : BitVec 64) (word_val : BitVec 32)
    (off : Nat) (hoff : off = 0 ∨ off = 4) :
    ∀ k : Nat, k < 8 →
      (k < off ∨ k ≥ off + 4) →
      dword_byte (wordSplice dword_orig word_val (8 * off)) k =
      dword_byte dword_orig k := by
  intro k hk hout
  rcases hoff with rfl | rfl
  all_goals
    interval_cases k <;>
      (first | omega | (simp [wordSplice, dword_byte] <;> bv_decide))

/-- The word-store XOR-mask-XOR expression is a four-byte splice. -/
theorem wordSplice_spec (dword_orig : BitVec 64) (word_val : BitVec 32)
    (off : Nat) (hoff : off = 0 ∨ off = 4) :
    let spliced := wordSplice dword_orig word_val (8 * off)
    IsWordSplice dword_orig spliced word_val off := by
  dsimp [IsWordSplice]
  refine ⟨?_, ?_⟩
  · intro j hj
    simpa using wordSplice_target_bytes dword_orig word_val off hoff j hj
  · intro k hk hout
    simpa using wordSplice_other_bytes dword_orig word_val off hoff k hk hout

/-- A dword-window setup is enough to reuse the existing dword-store hashmap
facts, whose older statement packages a word-alignment field that is irrelevant
for an 8-byte write. -/
private theorem dwordStoreSetup_self_of_window {ea base : BitVec 64}
    (h : DwordWindowSetup ea base) :
    DwordStoreSetup base base := by
  have hbase8 : base &&& (7 : BitVec 64) = 0 := by
    rw [h.base_is_aligned]
    bv_decide
  have hbase4 : base &&& (3 : BitVec 64) = 0 := by
    have := hbase8
    bv_decide
  have hbase_self : base = base &&& (-8 : BitVec 64) := by
    have := hbase8
    bv_decide
  exact
    { word_aligned := hbase4
      base_is_aligned := hbase_self
      no_ovf := h.no_ovf }

/-- The absolute address for the `j`-th target byte can be written either from
the dword base plus the lane offset or from the native effective address. -/
private theorem target_addr_eq_of_window {ea base : BitVec 64}
    (h : DwordWindowSetup ea base) (j : Nat) :
    base.toNat + ((ea - base).toNat + j) = ea.toNat + j := by
  rw [h.ea_toNat]
  omega

/-- Every dword byte is either outside a target sub-window of width `width`, or
is the `j`-th byte inside that target window. -/
private theorem k_in_target_or_outside_width (off width k : Nat) :
    (k < off ∨ k ≥ off + width) ∨
    ∃ j : Nat, j < width ∧ k = off + j := by
  by_cases hlt : k < off
  · exact Or.inl (Or.inl hlt)
  · by_cases hge : k ≥ off + width
    · exact Or.inl (Or.inr hge)
    · right
      refine ⟨k - off, ?_, ?_⟩ <;> omega

/-- If an address is outside the enclosing dword window, it is outside the
native byte-store window as well. -/
private theorem outside_dword_window_implies_outside_byte_window
    {ea base : BitVec 64} (a : Nat) (h : ByteStoreSetup ea base)
    (hout : a < base.toNat ∨ a ≥ base.toNat + 8) :
    a < ea.toNat ∨ a ≥ ea.toNat + 1 := by
  rw [h.ea_toNat]
  have hoff_le : (ea - base).toNat + 1 ≤ 8 := by
    rcases h.offset_cases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 <;> omega
  rcases hout with hlt | hge
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- If an address is outside the enclosing dword window, it is outside the
native halfword-store window as well. -/
private theorem outside_dword_window_implies_outside_halfword_window
    {ea base : BitVec 64} (a : Nat) (h : HalfwordStoreSetup ea base)
    (hout : a < base.toNat ∨ a ≥ base.toNat + 8) :
    a < ea.toNat ∨ a ≥ ea.toNat + 2 := by
  rw [h.ea_toNat]
  have hoff_le : (ea - base).toNat + 2 ≤ 8 := by
    rcases h.offset_cases with h0 | h2 | h4 | h6 <;> omega
  rcases hout with hlt | hge
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- If an address is outside the enclosing dword window, it is outside the
native word-store window as well. -/
private theorem outside_dword_window_implies_outside_word_window
    {ea base : BitVec 64} (a : Nat) (h : WordStoreSetup ea base)
    (hout : a < base.toNat ∨ a ≥ base.toNat + 8) :
    a < ea.toNat ∨ a ≥ ea.toNat + 4 := by
  rw [h.ea_toNat]
  have hoff_le : (ea - base).toNat + 4 ≤ 8 := by
    rcases h.offset_cases with h0 | h4 <;> omega
  rcases hout with hlt | hge
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- If a dword byte index lies outside the byte target lane, then the absolute
address lies outside the native byte-store window. -/
private theorem outside_target_addr_outside_byte_window
    {ea base : BitVec 64} (k : Nat) (h : ByteStoreSetup ea base)
    (hout : k < (ea - base).toNat ∨ k ≥ (ea - base).toNat + 1) :
    base.toNat + k < ea.toNat ∨ base.toNat + k ≥ ea.toNat + 1 := by
  rw [h.ea_toNat]
  omega

/-- Halfword analogue of `outside_target_addr_outside_byte_window`. -/
private theorem outside_target_addr_outside_halfword_window
    {ea base : BitVec 64} (k : Nat) (h : HalfwordStoreSetup ea base)
    (hout : k < (ea - base).toNat ∨ k ≥ (ea - base).toNat + 2) :
    base.toNat + k < ea.toNat ∨ base.toNat + k ≥ ea.toNat + 2 := by
  rw [h.ea_toNat]
  omega

/-- Word analogue of `outside_target_addr_outside_byte_window`. -/
private theorem outside_target_addr_outside_word_window
    {ea base : BitVec 64} (k : Nat) (h : WordStoreSetup ea base)
    (hout : k < (ea - base).toNat ∨ k ≥ (ea - base).toNat + 4) :
    base.toNat + k < ea.toNat ∨ base.toNat + k ≥ ea.toNat + 4 := by
  rw [h.ea_toNat]
  omega

/-- Writing a spliced dword is the same hashmap update as a native byte store,
provided the spliced dword has the byte-store shape and the original dword was
loaded from the enclosing dword window. -/
theorem dword_store_splice_eq_byte_store_populated
    (s : SailState) (ea base : BitVec 64)
    (byte_val : BitVec 8) (dword_orig dword_new : BitVec 64)
    (hsetup : ByteStoreSetup ea base)
    (hpop : ∀ k : Nat, k < 8 -> s.mem.get? (base.toNat + k) ≠ none)
    (hload : ∀ k : Nat, k < 8 →
      dword_byte dword_orig k = loaded_byte_at s (base + BitVec.ofNat 64 k))
    (hsplice_target : ∀ j : Nat, j < 1 →
      dword_byte dword_new ((ea - base).toNat + j) = byte_byte byte_val j)
    (hsplice_other : ∀ k : Nat, k < 8 →
      (k < (ea - base).toNat ∨ k ≥ (ea - base).toNat + 1) →
      dword_byte dword_new k = dword_byte dword_orig k) :
    (state_after_dword_store s base dword_new).mem =
    (state_after_byte_store s ea byte_val).mem := by
  apply mem_eq_of_eq_on_dword_window base.toNat
      (state_after_dword_store s base dword_new).mem
      (state_after_byte_store s ea byte_val).mem
      s.mem
  · intro a ha
    simpa using stored_dword_untouched s base base dword_new
      (dwordStoreSetup_self_of_window hsetup.toDwordWindowSetup) a ha
  · intro a ha
    have ha_byte : a < ea.toNat ∨ a ≥ ea.toNat + 1 :=
      outside_dword_window_implies_outside_byte_window a hsetup ha
    simpa using stored_byte_untouched s ea byte_val a ha_byte
  · intro k hk
    rcases k_in_target_or_outside_width (ea - base).toNat 1 k with hout | htarget
    ·
        rw [stored_dword_get?_hit s base dword_new k hk]
        rw [hsplice_other k hk hout]
        have haddr : (base + BitVec.ofNat 64 k).toNat = base.toNat + k :=
          toNat_base_add_small base k hk hsetup.no_ovf
        have hpop' : s.mem.get? (base + BitVec.ofNat 64 k).toNat ≠ none := by
          simpa [haddr] using hpop k hk
        have hload' : loaded_byte_at s (base + BitVec.ofNat 64 k) =
            dword_byte dword_orig k := by
          simpa using (hload k hk).symm
        have hsome : s.mem.get? (base.toNat + k) = some (dword_byte dword_orig k) := by
          simpa [haddr] using get?_of_loaded_byte_at_eq s (base + BitVec.ofNat 64 k)
            (dword_byte dword_orig k) hpop' hload'
        rw [← hsome]
        have haddr_out : base.toNat + k < ea.toNat ∨ base.toNat + k ≥ ea.toNat + 1 :=
          outside_target_addr_outside_byte_window k hsetup hout
        symm
        simpa using stored_byte_untouched s ea byte_val (base.toNat + k) haddr_out
    ·
        obtain ⟨j, hj, hk_eq⟩ := htarget
        rw [hk_eq]
        rw [stored_dword_get?_hit s base dword_new ((ea - base).toNat + j) (by omega)]
        rw [hsplice_target j hj]
        rw [target_addr_eq_of_window hsetup.toDwordWindowSetup j]
        symm
        simpa using stored_byte_get?_hit s ea byte_val j hj

/-- Writing a spliced dword is the same hashmap update as a native halfword
store. -/
theorem dword_store_splice_eq_halfword_store_populated
    (s : SailState) (ea base : BitVec 64)
    (halfword_val : BitVec 16) (dword_orig dword_new : BitVec 64)
    (hsetup : HalfwordStoreSetup ea base)
    (hpop : ∀ k : Nat, k < 8 -> s.mem.get? (base.toNat + k) ≠ none)
    (hload : ∀ k : Nat, k < 8 →
      dword_byte dword_orig k = loaded_byte_at s (base + BitVec.ofNat 64 k))
    (hsplice_target : ∀ j : Nat, j < 2 →
      dword_byte dword_new ((ea - base).toNat + j) = halfword_byte halfword_val j)
    (hsplice_other : ∀ k : Nat, k < 8 →
      (k < (ea - base).toNat ∨ k ≥ (ea - base).toNat + 2) →
      dword_byte dword_new k = dword_byte dword_orig k) :
    (state_after_dword_store s base dword_new).mem =
    (state_after_halfword_store s ea halfword_val).mem := by
  apply mem_eq_of_eq_on_dword_window base.toNat
      (state_after_dword_store s base dword_new).mem
      (state_after_halfword_store s ea halfword_val).mem
      s.mem
  · intro a ha
    simpa using stored_dword_untouched s base base dword_new
      (dwordStoreSetup_self_of_window hsetup.toDwordWindowSetup) a ha
  · intro a ha
    have ha_half : a < ea.toNat ∨ a ≥ ea.toNat + 2 :=
      outside_dword_window_implies_outside_halfword_window a hsetup ha
    simpa using stored_halfword_untouched s ea halfword_val a ha_half
  · intro k hk
    rcases k_in_target_or_outside_width (ea - base).toNat 2 k with hout | htarget
    ·
        rw [stored_dword_get?_hit s base dword_new k hk]
        rw [hsplice_other k hk hout]
        have haddr : (base + BitVec.ofNat 64 k).toNat = base.toNat + k :=
          toNat_base_add_small base k hk hsetup.no_ovf
        have hpop' : s.mem.get? (base + BitVec.ofNat 64 k).toNat ≠ none := by
          simpa [haddr] using hpop k hk
        have hload' : loaded_byte_at s (base + BitVec.ofNat 64 k) =
            dword_byte dword_orig k := by
          simpa using (hload k hk).symm
        have hsome : s.mem.get? (base.toNat + k) = some (dword_byte dword_orig k) := by
          simpa [haddr] using get?_of_loaded_byte_at_eq s (base + BitVec.ofNat 64 k)
            (dword_byte dword_orig k) hpop' hload'
        rw [← hsome]
        have haddr_out : base.toNat + k < ea.toNat ∨ base.toNat + k ≥ ea.toNat + 2 :=
          outside_target_addr_outside_halfword_window k hsetup hout
        symm
        simpa using stored_halfword_untouched s ea halfword_val (base.toNat + k) haddr_out
    ·
        obtain ⟨j, hj, hk_eq⟩ := htarget
        rw [hk_eq]
        rw [stored_dword_get?_hit s base dword_new ((ea - base).toNat + j) (by omega)]
        rw [hsplice_target j hj]
        rw [target_addr_eq_of_window hsetup.toDwordWindowSetup j]
        symm
        simpa using stored_halfword_get?_hit s ea halfword_val j hj

/-- Writing a spliced dword is the same hashmap update as a native word store. -/
theorem dword_store_splice_eq_word_store_populated'
    (s : SailState) (ea base : BitVec 64)
    (word_val : BitVec 32) (dword_orig dword_new : BitVec 64)
    (hsetup : WordStoreSetup ea base)
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
    simpa using stored_dword_untouched s base base dword_new
      (dwordStoreSetup_self_of_window hsetup.toDwordWindowSetup) a ha
  · intro a ha
    have ha_word : a < ea.toNat ∨ a ≥ ea.toNat + 4 :=
      outside_dword_window_implies_outside_word_window a hsetup ha
    simpa using stored_word_untouched s ea word_val a ha_word
  · intro k hk
    rcases k_in_target_or_outside_width (ea - base).toNat 4 k with hout | htarget
    ·
        rw [stored_dword_get?_hit s base dword_new k hk]
        rw [hsplice_other k hk hout]
        have haddr : (base + BitVec.ofNat 64 k).toNat = base.toNat + k :=
          toNat_base_add_small base k hk hsetup.no_ovf
        have hpop' : s.mem.get? (base + BitVec.ofNat 64 k).toNat ≠ none := by
          simpa [haddr] using hpop k hk
        have hload' : loaded_byte_at s (base + BitVec.ofNat 64 k) =
            dword_byte dword_orig k := by
          simpa using (hload k hk).symm
        have hsome : s.mem.get? (base.toNat + k) = some (dword_byte dword_orig k) := by
          simpa [haddr] using get?_of_loaded_byte_at_eq s (base + BitVec.ofNat 64 k)
            (dword_byte dword_orig k) hpop' hload'
        rw [← hsome]
        have haddr_out : base.toNat + k < ea.toNat ∨ base.toNat + k ≥ ea.toNat + 4 :=
          outside_target_addr_outside_word_window k hsetup hout
        symm
        simpa using stored_word_untouched s ea word_val (base.toNat + k) haddr_out
    ·
        obtain ⟨j, hj, hk_eq⟩ := htarget
        rw [hk_eq]
        rw [stored_dword_get?_hit s base dword_new ((ea - base).toNat + j) (by omega)]
        rw [hsplice_target j hj]
        rw [target_addr_eq_of_window hsetup.toDwordWindowSetup j]
        symm
        simpa using stored_word_get?_hit s ea word_val j hj

end StoreSplice

end
