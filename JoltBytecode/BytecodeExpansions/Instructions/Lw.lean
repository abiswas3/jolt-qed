import JoltBytecode.BytecodeExpansions.Common.Cpu

/-!
# LW: RISC-V ≡ Jolt Decomposition

## Instruction (RV32I/RV64I)

`LW rd, offset(rs1)` loads a 32-bit word from memory at the word-aligned
address `(rs1 + offset) & ~3`, sign-extends it to 64 bits, and writes to rd.

## Jolt Decomposition

Jolt reads a 64-bit dword from the dword-aligned address, shifts to extract
the 32-bit word, then sign-extends.

## Proof Strategy

Define `read_word_val` and `read_dword_val` as Nat-valued little-endian
byte sums. The dword is just two words: `dword = lo_word + hi_word * 2^32`.
Extraction is then pure Nat arithmetic (mod/div by 2^32), handled by omega.
-/

-- Nat value of 4 little-endian bytes at addr.
def read_word_val (addr : BitVec 64) (s : State) : Nat :=
  (read_mem addr s).toNat +
  (read_mem (addr + 1) s).toNat * 2^8 +
  (read_mem (addr + 2) s).toNat * 2^16 +
  (read_mem (addr + 3) s).toNat * 2^24

-- Nat value of 8 little-endian bytes at addr = two consecutive words.
def read_dword_val (addr : BitVec 64) (s : State) : Nat :=
  read_word_val addr s + read_word_val (addr + 4) s * 2^32

-- BitVec wrappers.
def read_word (addr : BitVec 64) (s : State) : BitVec 32 :=
  BitVec.ofNat 32 (read_word_val addr s)

def read_dword (addr : BitVec 64) (s : State) : BitVec 64 :=
  BitVec.ofNat 64 (read_dword_val addr s)

-- RISC-V LW
def riscv_lw (rs1 rd : BitVec 5) (imm : BitVec 12) (s : State) : State :=
  let base := read rs1 s.reg
  let addr := (imm.setWidth 64 + base) &&& (-4#64)
  let word := read_word addr s
  let new_reg := write rd (word.signExtend 64) s.reg
  { s with reg := new_reg }

-- Jolt's LW: read dword, shift, truncate.
def jolt_lw (rs1 rd : BitVec 5) (imm : BitVec 12) (s : State) : State :=
  let base := read rs1 s.reg
  let addr := (imm.setWidth 64 + base) &&& (-4#64)
  let dword_addr := addr &&& (-8#64)
  let dword := read_dword dword_addr s
  let shift := (addr <<< 3).setWidth 6
  let word := (dword >>> shift.toNat).setWidth 32
  let new_reg := write rd (word.signExtend 64) s.reg
  { s with reg := new_reg }

-- ============================================================================
-- Nat-level bounds and extraction lemmas
-- ============================================================================

private lemma read_word_val_lt (addr : BitVec 64) (s : State) :
    read_word_val addr s < 2^32 := by
  unfold read_word_val
  have := (read_mem addr s).isLt
  have := (read_mem (addr + 1) s).isLt
  have := (read_mem (addr + 2) s).isLt
  have := (read_mem (addr + 3) s).isLt
  omega

private lemma read_dword_val_lt (addr : BitVec 64) (s : State) :
    read_dword_val addr s < 2^64 := by
  unfold read_dword_val
  have := read_word_val_lt addr s
  have := read_word_val_lt (addr + 4) s
  omega

-- Lower word of dword (shift = 0 case).
private lemma extract_lower_word (addr : BitVec 64) (s : State) :
    read_word_val addr s = read_dword_val addr s % 2^32 := by
  unfold read_dword_val
  have := read_word_val_lt addr s
  omega

-- Upper word of dword (shift = 32 case).
-- lo_addr + 4 = hi_addr (the word we want is the upper half of the dword).
private lemma extract_upper_word (lo hi : BitVec 64) (s : State)
    (h : lo + 4 = hi) :
    read_word_val hi s = read_dword_val lo s / 2^32 % 2^32 := by
  unfold read_dword_val; rw [h]
  have := read_word_val_lt lo s
  have := read_word_val_lt hi s
  omega

-- ============================================================================
-- Bridge lemmas: BitVec ↔ Nat
-- ============================================================================

private lemma read_word_toNat (addr : BitVec 64) (s : State) :
    (read_word addr s).toNat = read_word_val addr s := by
  unfold read_word; rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (read_word_val_lt addr s)

private lemma read_dword_toNat (addr : BitVec 64) (s : State) :
    (read_dword addr s).toNat = read_dword_val addr s := by
  unfold read_dword; rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (read_dword_val_lt addr s)

-- ============================================================================
-- Address arithmetic
-- ============================================================================

-- (x &&& -4) &&& 3 = 0
private lemma and_neg4_and_3_eq_0 (x : BitVec 64) :
    (x &&& (-4#64)) &&& 3#64 = 0#64 := by
  have : (-4#64) &&& 3#64 = 0#64 := by native_decide
  rw [BitVec.and_assoc]; simp [this]

-- Dword-aligned: addr &&& -8 = addr when addr &&& 7 = 0
private lemma dword_align_eq (addr : BitVec 64)
    (h : addr &&& 7#64 = 0#64) : addr &&& (-8#64) = addr := by
  bv_decide

-- Not dword-aligned: addr &&& -8 = addr - 4 when addr &&& 3 = 0 and addr &&& 7 ≠ 0
private lemma dword_align_sub4 (addr : BitVec 64)
    (h3 : addr &&& 3#64 = 0#64) (h7 : ¬(addr &&& 7#64 = 0#64)) :
    addr &&& (-8#64) = addr - 4 := by
  bv_decide

-- Shift = 0 when dword-aligned
private lemma shift_eq_zero (addr : BitVec 64)
    (h : addr &&& 7#64 = 0#64) :
    ((addr <<< 3).setWidth 6).toNat = 0 := by
  have : (addr <<< 3).setWidth 6 = 0#6 := by bv_decide
  simp [this]

-- Shift = 32 when word-aligned but not dword-aligned
private lemma shift_eq_32 (addr : BitVec 64)
    (h3 : addr &&& 3#64 = 0#64) (h7 : ¬(addr &&& 7#64 = 0#64)) :
    ((addr <<< 3).setWidth 6).toNat = 32 := by
  have : (addr <<< 3).setWidth 6 = 32#6 := by bv_decide
  simp [this]

-- ============================================================================
-- Key lemma: word read = extract from dword (via Nat bridge)
-- ============================================================================

lemma read_word_eq_dword_extract (addr : BitVec 64) (s : State)
    (h_aligned : addr &&& 3#64 = 0#64) :
    read_word addr s =
    (read_dword (addr &&& (-8#64)) s >>> ((addr <<< 3).setWidth 6).toNat).setWidth 32 := by
  -- Rewrite address/shift in BitVec land FIRST, then convert to Nat.
  by_cases h7 : addr &&& 7#64 = 0#64
  · -- Dword-aligned: dword_addr = addr, shift = 0
    rw [dword_align_eq addr h7, shift_eq_zero addr h7]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
               Nat.shiftRight_eq_div_pow, pow_zero, Nat.div_one,
               read_dword_toNat, read_word_toNat]
    exact extract_lower_word addr s
  · -- Word-aligned, not dword-aligned: dword_addr = addr - 4, shift = 32
    rw [dword_align_sub4 addr h_aligned h7, shift_eq_32 addr h_aligned h7]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
               Nat.shiftRight_eq_div_pow, read_dword_toNat, read_word_toNat]
    have h_addr : addr - 4 + 4 = addr := by bv_omega
    exact extract_upper_word (addr - 4) addr s h_addr

-- ============================================================================
-- Main theorem
-- ============================================================================

theorem lw_eq (rs1 rd : BitVec 5) (imm : BitVec 12) (s : State) :
    riscv_lw rs1 rd imm s = jolt_lw rs1 rd imm s := by
  simp only [riscv_lw, jolt_lw]
  congr 1
  funext x
  simp only [write]
  by_cases h : x = rd
  · simp only [h, ↓reduceIte]
    congr 1
    exact read_word_eq_dword_extract _ s (and_neg4_and_3_eq_0 _)
  · simp [h]
