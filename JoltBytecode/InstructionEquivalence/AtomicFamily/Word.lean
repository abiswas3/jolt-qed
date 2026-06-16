import JoltBytecode.InstructionEquivalence.AtomicFamily.Common
import JoltBytecode.InstructionEquivalence.AtomicFamily.Derived
import JoltBytecode.InstructionEquivalence.LoadDefUtils
import JoltBytecode.InstructionEquivalence.LoadFamily.DwordArithmetic
import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.InstructionEquivalence.StoreFamily.Splice
import JoltBytecode.JoltISA.Semantics.ExpansionBlocks.ALU
import JoltBytecode.JoltISA.Semantics.Instructions.Add
import JoltBytecode.JoltISA.Semantics.Instructions.ANDI
import JoltBytecode.JoltISA.Semantics.Instructions.LD
import JoltBytecode.JoltISA.Semantics.Instructions.Mul
import JoltBytecode.JoltISA.Semantics.Instructions.ORI
import JoltBytecode.JoltISA.Semantics.Instructions.SD
import JoltBytecode.JoltISA.Semantics.Instructions.Sub
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualAssertAlignment
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualMULI
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualPow2
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualShiftRightBitmask
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualSignExtendWord
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualSRL
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualSRLI
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualZeroExtendWord
import JoltBytecode.JoltISA.Semantics.Instructions.XOR
import JoltBytecode.JoltISA.Semantics.Instructions.AND

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace AtomicFamily

/-- The enclosing dword address used by every `.W` AMO expansion. -/
abbrev amoWordBase (addr : BitVec 64) : BitVec 64 :=
  addr &&& (-8 : BitVec 64)

/-- Canonical Sail state after an aligned 32-bit AMO has stored `result` and
written the sign-extended old word into `rd`. -/
abbrev amoWordFinalSailState
    (rd : regidx) (s : SailState) (addr : BitVec 64) (result : BitVec 32) :
    SailState :=
  stateAfterWrite
    (state_after_word_store s addr result)
    rd
    (sign_extend (m := 64) (loaded_word_at s addr))

/-- The dword written back by the `.W` AMO postlude after replacing the target
word lane with the low word of `newValue`. -/
def amoWordSplicedDword
    (s : SailState) (addr newValue : BitVec 64) : BitVec 64 :=
  StoreSplice.wordSplice
    (loaded_dword_at s (amoWordBase addr))
    (Sail.BitVec.extractLsb newValue 31 0)
    (8 * ((addr - amoWordBase addr).toNat))

/-- The shifted old word value produced by the common `.W` AMO prelude. -/
abbrev amoWordShiftedOld (s : SailState) (addr : BitVec 64) : BitVec 64 :=
  shift_bits_right (loaded_dword_at s (amoWordBase addr))
    (Sail.BitVec.extractLsb (shift_bits_left addr (3 : BitVec 6)) 5 0)

/-- The zero immediate used by word AMO expansion instructions leaves the
effective address unchanged. -/
theorem amo_word_zero_offset_addr (addr : BitVec 64) :
    addr + sign_extend (m := 64) (0 : BitVec 12) = addr := by
  have hsext0 :
      sign_extend (m := 64) (0 : BitVec 12) = (0 : BitVec 64) := by
    decide
  rw [hsext0]
  bv_decide

/-- `ANDI` with `-8` computes the enclosing dword base used by `.W` AMOs. -/
theorem amo_word_base_mask (addr : BitVec 64) :
    addr &&& sign_extend (m := 64) (-8 : BitVec 12) = amoWordBase addr := by
  unfold amoWordBase
  have hmask :
      sign_extend (m := 64) (-8 : BitVec 12) = (-8 : BitVec 64) := by
    decide
  rw [hmask]

/-- Alignment at the base address is preserved by the word AMO expansion's
zero offset. -/
theorem amo_word_zero_offset_aligned (addr : BitVec 64)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    (addr + sign_extend (m := 64) (0 : BitVec 12)) &&& (3 : BitVec 64) = 0 := by
  rw [amo_word_zero_offset_addr addr]
  exact h_align

/-- Misalignment at the base address is preserved by the word AMO expansion's
zero offset. -/
theorem amo_word_zero_offset_misaligned (addr : BitVec 64)
    (h_align : addr &&& (3 : BitVec 64) ≠ 0) :
    (addr + sign_extend (m := 64) (0 : BitVec 12)) &&& (3 : BitVec 64) ≠ 0 := by
  rw [amo_word_zero_offset_addr addr]
  exact h_align

/-- The enclosing dword base of a word AMO is always 8-byte aligned. -/
theorem amo_word_base_aligned (addr : BitVec 64) :
    amoWordBase addr &&& (7 : BitVec 64) = 0 := by
  unfold amoWordBase
  bv_decide

/-- The enclosing dword base of a word AMO has room for its full 8-byte
window. -/
theorem amo_word_base_no_ovf (addr : BitVec 64) :
    (amoWordBase addr).toNat + 7 < 2 ^ 64 := by
  exact aligned_addr_no_ovf_of_align (amoWordBase addr)
    (amo_word_base_aligned addr)

/-- The enclosing dword base packages the access facts expected by dword load
and dword store helpers. -/
theorem amo_word_base_aligned_access
    (addr : BitVec 64) (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64) :
    AlignedDwordAccess (amoWordBase addr) :=
  { misalign := access_misaligned_8_aligned_false
      (amoWordBase addr) (amo_word_base_aligned addr)
    split := split_misaligned_aligned_8
      (amoWordBase addr) (amo_word_base_aligned addr)
    align := amo_word_base_aligned addr
    no_ovf := h_no_ovf }

/-- A word-aligned AMO address gives the splice setup for the containing dword
window. -/
theorem amo_word_store_setup
    (addr : BitVec 64)
    (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    StoreSplice.WordStoreSetup addr (amoWordBase addr) := by
  let hsetup : DwordStoreSetup addr (amoWordBase addr) :=
    { word_aligned := h_align
      base_is_aligned := rfl
      no_ovf := h_no_ovf }
  exact
    { base_is_aligned := rfl
      no_ovf := h_no_ovf
      ea_toNat := ea_toNat_eq_base_plus_offset addr (amoWordBase addr) hsetup
      word_aligned := h_align
      offset_cases := store_offset_cases addr (amoWordBase addr) hsetup }

/-- The leading word alignment assertion retires on aligned `.W` AMO expansion
paths. -/
theorem amo_word_virtual_assert_aligned_run
    (rs1 : regidx) (js : SailJoltState) (addr : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    (JoltISA.execInstr
      (.VirtualAssertWordAlignment rs1 (0 : BitVec 12)
        (ExceptionType.E_SAMO_Addr_Align ()))).run js =
      .ok RETIRE_SUCCESS js := by
  exact
    JoltISA.virtual_assert_word_alignment_run_aligned
      rs1 (0 : BitVec 12) (ExceptionType.E_SAMO_Addr_Align ())
      js addr hrs1 (amo_word_zero_offset_aligned addr h_align)

/-- The leading word alignment assertion raises the AMO alignment exception on
misaligned `.W` AMO expansion paths. -/
theorem amo_word_virtual_assert_misaligned_run
    (rs1 : regidx) (js : SailJoltState) (addr : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (h_align : addr &&& (3 : BitVec 64) ≠ 0) :
    (JoltISA.execInstr
      (.VirtualAssertWordAlignment rs1 (0 : BitVec 12)
        (ExceptionType.E_SAMO_Addr_Align ()))).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr addr, ExceptionType.E_SAMO_Addr_Align ())) js := by
  have hrun :=
    JoltISA.virtual_assert_word_alignment_run_misaligned
      rs1 (0 : BitVec 12) (ExceptionType.E_SAMO_Addr_Align ())
      js addr hrs1 (amo_word_zero_offset_misaligned addr h_align)
  rw [amo_word_zero_offset_addr addr] at hrun
  exact hrun

/-- A failed leading word-alignment assertion stops a word-AMO program before
running the supplied tail. -/
theorem amo_word_assert_prefix_misaligned_run
    (rs1 : regidx) (tail : JoltISA.Program)
    (js : SailJoltState) (addr : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (h_align : addr &&& (3 : BitVec 64) ≠ 0) :
    (JoltISA.execProgram
      (.instr (.VirtualAssertWordAlignment rs1 (0 : BitVec 12)
        (ExceptionType.E_SAMO_Addr_Align ())) tail)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr addr, ExceptionType.E_SAMO_Addr_Align ())) js := by
  let e := (Virtaddr addr, ExceptionType.E_SAMO_Addr_Align ())
  have hassert :=
    amo_word_virtual_assert_misaligned_run rs1 js addr hrs1 h_align
  exact
    JoltISA.execProgram_instr_run_memory_exception
      (.VirtualAssertWordAlignment rs1 (0 : BitVec 12)
        (ExceptionType.E_SAMO_Addr_Align ()))
      tail js js e hassert

/-- Any `amoPre64Program` expansion stops at the leading word-alignment check
on a misaligned address. -/
theorem amo_word_pre64_misaligned_run
    (rs1 : regidx) (old dword shift : JoltISA.VReg) (tail : JoltISA.Program)
    (js : SailJoltState) (addr : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (h_align : addr &&& (3 : BitVec 64) ≠ 0) :
    (JoltISA.execProgram
      (JoltISA.amoPre64Program rs1 old dword shift tail)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr addr, ExceptionType.E_SAMO_Addr_Align ())) js := by
  unfold JoltISA.amoPre64Program JoltISA.amoPre64ProgramWithScratch
  exact amo_word_assert_prefix_misaligned_run rs1 _ js addr hrs1 h_align

private theorem setWidth6_eq_extractLsb_5_0 (v : BitVec 64) :
    v.setWidth 6 = Sail.BitVec.extractLsb v 5 0 := by
  unfold Sail.BitVec.extractLsb
  ext i
  simp

/-- The low six bits of the `.W` AMO shift value are exactly the byte-lane
offset in bits. -/
theorem amo_word_shift6_eq_offset
    (addr base : BitVec 64)
    (hsetup : StoreSplice.WordStoreSetup addr base) :
    Sail.BitVec.extractLsb (shift_bits_left addr (3 : BitVec 6)) 5 0 =
      BitVec.ofNat 6 (((addr - base).toNat) * 8) := by
  rw [← setWidth6_eq_extractLsb_5_0 (shift_bits_left addr (3 : BitVec 6))]
  apply BitVec.eq_of_toNat_eq
  simp only [shift_bits_left, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  change (BitVec.shiftLeft addr 3).toNat % 2 ^ 6 =
    (addr - base).toNat * 8 % 2 ^ 6
  rw [show (BitVec.shiftLeft addr 3).toNat = addr.toNat <<< 3 % 2 ^ 64 by
    exact BitVec.toNat_shiftLeft]
  simp only [Nat.shiftLeft_eq]
  norm_num
  conv_lhs => rw [hsetup.ea_toNat]
  have hbase8 : base &&& (7 : BitVec 64) = 0 := by
    rw [hsetup.base_is_aligned]
    exact align_down_8_and_7_eq_zero addr
  have hbase_low : (base &&& (7 : BitVec 64)).toNat = base.toNat % 8 := by
    rw [BitVec.toNat_and]
    have h7 : (7 : BitVec 64).toNat = 7 := by decide
    rw [h7, show (7 : Nat) = 2 ^ 3 - 1 by norm_num,
      Nat.and_two_pow_sub_one_eq_mod]
  have hbase_mod8 : base.toNat % 8 = 0 := by
    have hzero := congrArg BitVec.toNat hbase8
    rw [hbase_low] at hzero
    simpa using hzero
  have hmod :
      ((base.toNat + (addr - base).toNat) * 8) % 64 =
        ((addr - base).toNat * 8) % 64 := by
    have hb_dvd : 8 ∣ base.toNat := Nat.dvd_of_mod_eq_zero hbase_mod8
    rcases hb_dvd with ⟨q, hq⟩
    rw [hq]
    rw [show (8 * q + (addr - base).toNat) * 8 =
        (addr - base).toNat * 8 + 64 * q by ring]
    rw [Nat.add_mul_mod_self_left]
  rw [hmod]
  have hsub_toNat :
      (18446744073709551616 - base.toNat + addr.toNat) %
          18446744073709551616 =
        (addr - base).toNat := by
    rw [show 18446744073709551616 = 2 ^ 64 by norm_num]
    exact (BitVec.toNat_sub addr base).symm
  conv_rhs => rw [hsub_toNat]

private theorem shift_bits_left_eq_shiftLeft_nat (x : BitVec 64) (sh : BitVec 6) :
    shift_bits_left x sh = x <<< sh.toNat := by
  rfl

private theorem amoWordSequenceMask_getLsbD_true {i : Nat} (hi : i < 32) :
    (4294967295#64).getLsbD i = true := by
  have hi64 : i < 64 := by omega
  have hmaskNat : Nat.testBit 4294967295 i = true := by
    rw [show 4294967295 = 2 ^ 32 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
    simp [hi]
  rw [BitVec.getLsbD_ofNat]
  simp [hi64, hmaskNat]

private theorem amoWordSequenceMask_getLsbD_false_of_ge32 {i : Nat}
    (hge : 32 ≤ i) :
    (4294967295#64).getLsbD i = false := by
  have hmaskNat : Nat.testBit 4294967295 i = false := by
    rw [show 4294967295 = 2 ^ 32 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
    simp [not_lt.mpr hge]
  rw [BitVec.getLsbD_ofNat]
  simp [hmaskNat]

private theorem amo_word_splice_eq_sequence_of_bound
    (dword rs2Val : BitVec 64) (off : Nat) (hoff : off + 4 ≤ 8) :
    dword ^^^
        (((dword ^^^
          shift_bits_left rs2Val (BitVec.ofNat 6 (off * 8))) &&&
          shift_bits_left (0x00000000FFFFFFFF : BitVec 64)
            (BitVec.ofNat 6 (off * 8)))) =
      StoreSplice.wordSplice dword
        (Sail.BitVec.extractLsb rs2Val 31 0) (off * 8) := by
  rw [shift_bits_left_eq_shiftLeft_nat rs2Val (BitVec.ofNat 6 (off * 8))]
  rw [shift_bits_left_eq_shiftLeft_nat (0x00000000FFFFFFFF : BitVec 64)
    (BitVec.ofNat 6 (off * 8))]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hshift_lt64 : off * 8 < 64 := by omega
  have hshift_toNat : (BitVec.ofNat 6 (off * 8)).toNat = off * 8 := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hshift_lt64
  simp only [StoreSplice.wordSplice, Sail.BitVec.extractLsb,
    BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb, hshift_toNat]
  by_cases hbefore : i < off * 8
  · simp [hbefore]
  · by_cases hinside : i - off * 8 < 32
    · have hsub64 : i - off * 8 < 64 := by omega
      simp [hbefore, hinside, hsub64]
    · have hge : 32 ≤ i - off * 8 := by omega
      have hmask : (4294967295#64).getLsbD (i - off * 8) = false :=
        amoWordSequenceMask_getLsbD_false_of_ge32 hge
      simp [hbefore, hinside, hmask]

/-- The XOR-mask-XOR postlude expression is the same word splice used by the
store-family memory bridge. -/
theorem amo_word_splice_eq_sequence
    (dword rs2Val : BitVec 64) (off : Nat)
    (hoff : off = 0 ∨ off = 4) :
    dword ^^^
        (((dword ^^^
          shift_bits_left rs2Val (BitVec.ofNat 6 (off * 8))) &&&
          shift_bits_left (0x00000000FFFFFFFF : BitVec 64)
            (BitVec.ofNat 6 (off * 8)))) =
      StoreSplice.wordSplice dword
        (Sail.BitVec.extractLsb rs2Val 31 0) (8 * off) := by
  have hoff_bound : off + 4 ≤ 8 := by
    rcases hoff with h0 | h4 <;> omega
  rw [Nat.mul_comm 8 off]
  exact amo_word_splice_eq_sequence_of_bound dword rs2Val off hoff_bound

/-- The byte slices of `loaded_dword_at` agree with direct byte loads from the
same dword window. -/
theorem amo_word_loaded_dword_byte
    (s : SailState) (base : BitVec 64) (k : Nat) (hk : k < 8) :
    dword_byte (loaded_dword_at s base) k =
      loaded_byte_at s (base + BitVec.ofNat 64 k) := by
  interval_cases k
  all_goals
    unfold dword_byte loaded_dword_at loaded_byte_at
    bv_decide

/-- Writing the `.W` AMO spliced enclosing dword is the same memory update as
Sail's native word store at the AMO address. -/
theorem amo_word_spliced_dword_store_eq_word_store
    (s : SailState) (addr newValue : BitVec 64)
    (hsetup : StoreSplice.WordStoreSetup addr (amoWordBase addr))
    (hbytes : DwordBytesPresent (amoWordBase addr) s) :
    state_after_dword_store s (amoWordBase addr)
        (amoWordSplicedDword s addr newValue) =
      state_after_word_store s addr
        (Sail.BitVec.extractLsb newValue 31 0) := by
  let base := amoWordBase addr
  let dword_orig := loaded_dword_at s base
  let word_val := Sail.BitVec.extractLsb newValue 31 0
  let dword_new := amoWordSplicedDword s addr newValue
  let off := (addr - base).toNat
  have hoff : off = 0 ∨ off = 4 := by
    exact hsetup.offset_cases
  have hspec :
      StoreSplice.IsWordSplice dword_orig dword_new word_val off := by
    change
      StoreSplice.IsWordSplice
        (loaded_dword_at s base)
        (StoreSplice.wordSplice
          (loaded_dword_at s base)
          (Sail.BitVec.extractLsb newValue 31 0)
          (8 * ((addr - amoWordBase addr).toNat)))
        (Sail.BitVec.extractLsb newValue 31 0)
        ((addr - base).toNat)
    rw [show base = amoWordBase addr from rfl]
    exact StoreSplice.wordSplice_spec
      (loaded_dword_at s (amoWordBase addr))
      (Sail.BitVec.extractLsb newValue 31 0)
      ((addr - amoWordBase addr).toNat) hoff
  have hpop : ∀ k : Nat, k < 8 -> s.mem.get? (base.toNat + k) ≠ none := by
    intro k hk
    exact hbytes.present k hk
  have hload : ∀ k : Nat, k < 8 →
      dword_byte dword_orig k =
        loaded_byte_at s (base + BitVec.ofNat 64 k) := by
    intro k hk
    exact amo_word_loaded_dword_byte s base k hk
  have hmem_eq :
      (state_after_dword_store s base dword_new).mem =
      (state_after_word_store s addr word_val).mem := by
    change
      (state_after_dword_store s base dword_new).mem =
      (state_after_word_store s addr word_val).mem
    unfold StoreSplice.IsWordSplice at hspec
    exact StoreSplice.dword_store_splice_eq_word_store_populated'
      s addr base word_val dword_orig dword_new hsetup
      hpop hload hspec.1 hspec.2
  change
    state_after_dword_store s base dword_new =
      state_after_word_store s addr word_val
  cases s
  unfold state_after_dword_store state_after_word_store at hmem_eq ⊢
  congr

/-- A word-aligned AMO address has room for the native four-byte AMO access. -/
theorem amo_word_aligned_no_ovf
    (addr : BitVec 64)
    (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    addr.toNat + 3 < 2 ^ 64 := by
  have hsetup := amo_word_store_setup addr h_no_ovf h_align
  have hto := hsetup.ea_toNat
  rcases hsetup.offset_cases with h0 | h4
  · rw [hto, h0]
    omega
  · rw [hto, h4]
    omega

/-- A 4-byte aligned virtual address satisfies Sail's aligned-address test. -/
theorem amo_word_is_aligned_vaddr_true (addr : BitVec 64)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    is_aligned_vaddr (Virtaddr addr) 4 = true := by
  unfold is_aligned_vaddr Sail.BitVec.toNatInt
  have h_mod : addr.toNat % 4 = 0 := by
    have h := congrArg BitVec.toNat h_align
    rw [BitVec.toNat_and] at h
    have h3 : (3 : BitVec 64).toNat = 3 := by decide
    have h0 : (0 : BitVec 64).toNat = 0 := by decide
    rw [h3, h0,
      show (3 : Nat) = 2^2 - 1 from by norm_num,
      Nat.and_two_pow_sub_one_eq_mod] at h
    exact h
  simp only [Int.tmod]
  change ((Int.ofNat (addr.toNat % 4)) == (0 : Int)) = true
  have h_int : Int.ofNat (addr.toNat % 4) = 0 := by
    rw [h_mod]
    rfl
  rw [h_int]
  rfl

/-- A 4-byte aligned physical address satisfies Sail's aligned-address test. -/
theorem amo_word_is_aligned_paddr_true (addr : BitVec 64)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    is_aligned_paddr (physaddr.Physaddr addr) 4 = true := by
  unfold is_aligned_paddr Sail.BitVec.toNatInt
  have h_mod : addr.toNat % 4 = 0 := by
    have h := congrArg BitVec.toNat h_align
    rw [BitVec.toNat_and] at h
    have h3 : (3 : BitVec 64).toNat = 3 := by decide
    have h0 : (0 : BitVec 64).toNat = 0 := by decide
    rw [h3, h0,
      show (3 : Nat) = 2^2 - 1 from by norm_num,
      Nat.and_two_pow_sub_one_eq_mod] at h
    exact h
  simp only [Int.tmod]
  change ((Int.ofNat (addr.toNat % 4)) == (0 : Int)) = true
  have h_int : Int.ofNat (addr.toNat % 4) = 0 := by
    rw [h_mod]
    rfl
  rw [h_int]
  rfl

/-- Sail RAM reads for AMO reserved word reads return the canonical hashmap
word value. -/
theorem amo_word_read_ram_reserved_eq_loaded_word
    (addr : BitVec 64) (s : SailState)
    (hbytes : MemBytesPresent addr 4 s)
    (h_no_ovf : addr.toNat + 3 < 2 ^ 64) :
    LeanRV64D.Functions.read_ram read_kind.Read_RISCV_reserved
      (physaddr.Physaddr addr) 4 false s =
    .ok (loaded_word_at s addr, default_meta) s := by
  change
    LeanRV64D.Functions.read_ram read_kind.Read_plain
      (physaddr.Physaddr addr) 4 false s =
    .ok (loaded_word_at s addr, default_meta) s
  exact read_ram_4_eq_loaded_word addr s hbytes h_no_ovf

/-- The checked AMO word read reduces to the canonical loaded word when PMP
and readable-MMIO checks say the access is ordinary RAM. -/
theorem amo_word_checked_mem_read_eq_loaded_word
    (op : amoop) (addr : BitVec 64) (s : SailState)
    (hbytes : MemBytesPresent addr 4 s)
    (h_no_ovf : addr.toNat + 3 < 2 ^ 64)
    (hfm : FlatAtomicMem op addr 4 s) :
    checked_mem_read (Atomic (op, Data, Data)) Privilege.Machine
      (physaddr.Physaddr addr) 4 false false true false s =
    .ok (Ok (loaded_word_at s addr, default_meta)) s := by
  unfold checked_mem_read
  simp only [bind, EStateM.bind, pure, EStateM.pure, hfm.pmp, hfm.readable,
    Bool.false_eq_true, if_false]
  unfold read_kind_of_flags
  simp only [pure, EStateM.pure]
  rw [amo_word_read_ram_reserved_eq_loaded_word addr s hbytes h_no_ovf]

/-- A full AMO word memory read reduces through privilege, alignment, PMP, and
RAM checks to the canonical loaded word. -/
theorem amo_word_mem_read_eq_loaded_word
    (op : amoop) (addr : BitVec 64) (s : SailState)
    (hcfg : JoltConfig s)
    (h_no_ovf : addr.toNat + 3 < 2 ^ 64)
    (h_align : addr &&& (3 : BitVec 64) = 0)
    (hfm : FlatAtomicMem op addr 4 s) :
    mem_read (Atomic (op, Data, Data))
      (physaddr.Physaddr addr) 4 false false true s =
    .ok (Ok (loaded_word_at s addr)) s := by
  obtain ⟨mval, h_ms_regs, h_mprv⟩ := hcfg.mstatus_mprv.value
  have h_ms_read := readReg_eq Register.mstatus s mval h_ms_regs
  have h_priv := readReg_eq Register.cur_privilege s Privilege.Machine hcfg.cur_privilege.value
  have h_paddr_aligned := amo_word_is_aligned_paddr_true addr h_align
  have h_mpp_check : decide (0#1 = 1#1) = false := by decide
  unfold mem_read mem_read_priv
  simp only [bind, EStateM.bind, pure, EStateM.pure, h_ms_read, h_priv]
  unfold effectivePrivilege
  simp only [h_mprv, bne, BEq.beq, instBEqMemoryAccessType.beq,
    Bool.not_false, h_mpp_check, Bool.and_false, Bool.false_eq_true, if_false]
  unfold mem_read_priv_meta
  simp only [bind, EStateM.bind, pure, EStateM.pure,
    Bool.false_or, Bool.true_and, h_paddr_aligned]
  unfold LeanRV64D.Functions.not
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  rw [amo_word_checked_mem_read_eq_loaded_word
    op addr s hfm.bytes h_no_ovf hfm]
  rfl

/-- The AMO word write effective-address check succeeds for aligned physical
addresses. -/
theorem amo_word_mem_write_ea_ok
    (addr : BitVec 64) (s : SailState)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    mem_write_ea (physaddr.Physaddr addr) 4 false false true s =
      .ok (Ok ()) s := by
  have h_paddr_aligned := amo_word_is_aligned_paddr_true addr h_align
  unfold mem_write_ea
  simp only [Bool.false_or, Bool.true_and, h_paddr_aligned]
  unfold LeanRV64D.Functions.not
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  unfold write_kind_of_flags
  unfold write_ram_ea
  change
    (EStateM.bind (EStateM.pure write_kind.Write_RISCV_conditional)
      (fun _ => EStateM.pure (Ok ()))) s =
      .ok (Ok ()) s
  rfl

/-- Sail's conditional AMO word RAM write is the canonical direct hashmap word
store. -/
theorem amo_word_write_ram_conditional_eq_state_after_word_store
    (addr : BitVec 64) (data : BitVec 32) (s : SailState) :
    LeanRV64D.Functions.write_ram write_kind.Write_RISCV_conditional
      (physaddr.Physaddr addr) 4 data default_meta s =
    .ok true (state_after_word_store s addr data) := by
  simp only [LeanRV64D.Functions.write_ram,
    Sail.ConcurrencyInterfaceV1.sail_mem_write,
    PreSail.ConcurrencyInterfaceV1.sail_mem_write,
    PreSail.writeBytes,
    PreSail.writeByte,
    state_after_word_store,
    word_byte]
  rfl

/-- A full AMO word memory-value write reduces through privilege, alignment,
PMP, and RAM checks to the canonical word store. -/
theorem amo_word_mem_write_value_eq_state_after_word_store
    (op : amoop) (addr : BitVec 64) (data : BitVec 32) (s : SailState)
    (hcfg : JoltConfig s)
    (h_align : addr &&& (3 : BitVec 64) = 0)
    (hfm : FlatAtomicMem op addr 4 s) :
    mem_write_value (physaddr.Physaddr addr) 4 data
      (Atomic (op, Data, Data)) false false true s =
    .ok (Ok true) (state_after_word_store s addr data) := by
  obtain ⟨mval, h_ms_regs, h_mprv⟩ := hcfg.mstatus_mprv.value
  have h_ms_read := readReg_eq Register.mstatus s mval h_ms_regs
  have h_priv := readReg_eq Register.cur_privilege s Privilege.Machine hcfg.cur_privilege.value
  have h_paddr_aligned := amo_word_is_aligned_paddr_true addr h_align
  have h_mpp_check : decide (0#1 = 1#1) = false := by decide
  unfold mem_write_value mem_write_value_meta mem_write_value_priv_meta
    checked_mem_write
  simp only [bind, EStateM.bind, pure, h_ms_read, h_priv]
  unfold effectivePrivilege
  simp only [h_mprv, bne, BEq.beq, instBEqMemoryAccessType.beq,
    Bool.not_false, h_mpp_check, Bool.and_false, Bool.false_eq_true, if_false]
  simp only [Bool.false_or, Bool.true_and, h_paddr_aligned]
  unfold LeanRV64D.Functions.not
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  change
    (EStateM.bind
      (EStateM.bind
        (phys_access_check (Atomic (op, Data, Data)) Privilege.Machine
          (physaddr.Physaddr addr) 4 true)
        (fun result =>
          match result with
          | some e => EStateM.pure (Err e)
          | none =>
              EStateM.bind
                (within_mmio_writable (physaddr.Physaddr addr) 4)
                (fun isMmio =>
                  if isMmio = true then
                    mmio_write (physaddr.Physaddr addr) 4 data
                  else
                    EStateM.bind
                      (write_kind_of_flags false false true)
                      (fun wk =>
                        EStateM.bind
                          (LeanRV64D.Functions.write_ram wk
                            (physaddr.Physaddr addr) 4 data default_meta)
                          (fun ok => EStateM.pure (Ok ok))))))
      (fun result => EStateM.pure result)) s =
    .ok (Ok true) (state_after_word_store s addr data)
  simp only [EStateM.bind, hfm.pmp]
  simp only [hfm.writable]
  simp only [Bool.false_eq_true, if_false]
  unfold write_kind_of_flags
  simp only [EStateM.bind, pure, EStateM.pure]
  rw [amo_word_write_ram_conditional_eq_state_after_word_store addr data s]

/-- Sail's generated width assertion succeeds for a 4-byte non-CAS word AMO. -/
theorem amo_word_width_assert_true :
    (4 ≤b (((4 : Nat) : Int) * (2 : Int)).toNat) = true := by
  decide

/-- Sail's generated top-level width assertion succeeds for a 4-byte AMO on
RV64. -/
theorem amo_word_execute_width_assert_true :
    (4 ≤b (((8 : Nat) : Int) * (2 : Int)).toNat) = true := by
  decide

/-- Sail's generated register-width branch selects the ordinary x-register
path for a 4-byte word AMO. -/
theorem amo_word_width4_true : (4 ≤b (8 : Nat)) = true := by
  decide

/-- A non-4-aligned address is not aligned according to Sail's virtual-address
alignment predicate. -/
theorem amo_word_is_aligned_vaddr_false
    (addr : BitVec 64) (h_align : addr &&& (3 : BitVec 64) ≠ 0) :
    is_aligned_vaddr (Virtaddr addr) 4 = false := by
  have haccess := access_misaligned_4_unaligned_true addr h_align
  unfold access_causes_misaligned_exception at haccess
  unfold LeanRV64D.Functions.not at haccess
  simp only [plat_enable_misaligned_access, Bool.not_false, Bool.true_or,
    Bool.and_true] at haccess
  cases hval : is_aligned_vaddr (Virtaddr addr) 4
  · rfl
  · rw [hval] at haccess
    simp only [Bool.not_true, Bool.false_eq_true] at haccess

/-- Native Sail word AMOs stop at the alignment check on non-4-aligned
addresses. -/
theorem execute_AMO_word_misaligned
    (op : amoop) (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_align : addr &&& (3 : BitVec 64) ≠ 0) :
    (execute_AMO op false false rs2 rs1 4 rd).run js.sail =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr addr, ExceptionType.E_SAMO_Addr_Align ())) js.sail := by
  unfold execute_AMO
  simp only [bind, pure]
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  simp only [amo_word_execute_width_assert_true, PreSail.assert, pure,
    EStateM.run, if_true]
  unfold SailME.run PreSail.PreSailME.run
  have haddr0 : addr + zeros (n := 64) = addr := by
    unfold zeros
    exact BitVec.add_zero addr
  have hnot_aligned :
      is_aligned_vaddr (Virtaddr addr) 4 = false :=
    amo_word_is_aligned_vaddr_false addr h_align
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    ExceptT.pure, ExceptT.lift, MonadLift.monadLift, liftM, monadLift,
    Functor.map, ext_data_get_addr, hrs1, haddr0, hnot_aligned,
    LeanRV64D.Functions.not, Bool.not_false, if_true]

/-- The generated word-width cast leaves an already-32-bit value unchanged. -/
theorem amo_word_setWidth_4x8_eq_self (value : BitVec 32) :
    BitVec.setWidth (4 * 8) value = value := by
  rfl

/-- A 32-bit value is unchanged by Sail sign-extension at the generated
`4 * 8` width. -/
theorem amo_word_sign_extend_4x8_eq_self (value : BitVec 32) :
    sign_extend (m := 4 * 8) value = value := by
  unfold sign_extend Sail.BitVec.signExtend
  bv_decide

/-- The generated word-width writeback cast leaves the old word writeback
unchanged. -/
theorem amo_word_writeback_loaded_direct
    (rd : regidx) (s writebackState : SailState)
    (addr : BitVec 64) (result : BitVec 32)
    (hwriteback :
      wX_bits rd (sign_extend (m := 64) (loaded_word_at s addr))
        (state_after_word_store s addr result) =
        .ok () writebackState) :
    wX_bits rd
      (sign_extend (m := 64)
        (BitVec.setWidth (4 * 8) (loaded_word_at s addr)))
      (state_after_word_store s addr result) =
      .ok () writebackState := by
  rw [amo_word_setWidth_4x8_eq_self]
  exact hwriteback

/-- Sail's generated 32-bit truncation of `rs2` is the low word. -/
theorem amo_word_trunc_4x8_eq_extract (value : BitVec 64) :
    (show BitVec (4 * 8) from
      trunc (m := (((4 : Nat) : Int) * (8 : Int)).toNat) value) =
    (Sail.BitVec.extractLsb value 31 0 : BitVec 32) := by
  unfold trunc Sail.BitVec.truncate Sail.BitVec.extractLsb
  rfl

/-- The result expression generated by Sail's 32-bit non-CAS AMO executor after
the word load and `rs2` read have reduced. -/
abbrev amoWordSailResult
    (op : amoop) (rs2Val loaded : BitVec 32) : BitVec 32 :=
  match op with
  | amoop.AMOSWAP => rs2Val
  | amoop.AMOADD => rs2Val + loaded
  | amoop.AMOXOR => rs2Val ^^^ loaded
  | amoop.AMOAND => rs2Val &&& loaded
  | amoop.AMOOR => rs2Val ||| loaded
  | amoop.AMOMIN =>
      if (zopz0zI_s rs2Val loaded : Bool) then rs2Val else loaded
  | amoop.AMOMAX =>
      if (zopz0zK_s rs2Val loaded : Bool) then rs2Val else loaded
  | amoop.AMOMINU =>
      if (zopz0zI_u rs2Val loaded : Bool) then rs2Val else loaded
  | amoop.AMOMAXU =>
      if (zopz0zK_u rs2Val loaded : Bool) then rs2Val else loaded
  | amoop.AMOCAS => rs2Val

/-- The Sail AMO write of the computed word result reduces to the canonical
hashmap word store. -/
theorem amo_word_mem_write_value_sail_result
    (op : amoop) (addr rs2Val : BitVec 64) (result : BitVec 32)
    (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (h_mem : AmoMemoryContext op 4 (amoWordBase addr) addr js.sail)
    (h_align : addr &&& (3 : BitVec 64) = 0)
    (hresult :
      amoWordSailResult op
        (show BitVec (4 * 8) from
          trunc (m := (((4 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
        (BitVec.setWidth (4 * 8) (loaded_word_at js.sail addr)) =
      result) :
    mem_write_value (physaddr.Physaddr addr) 4
      (sign_extend (m := ((8 : Int) * ((4 : Nat) : Int)).toNat)
        (amoWordSailResult op
          (show BitVec (4 * 8) from
            trunc (m := (((4 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
          (BitVec.setWidth (4 * 8) (loaded_word_at js.sail addr))))
      (Atomic (op, Data, Data)) false false true js.sail =
    .ok (Ok true) (state_after_word_store js.sail addr result) := by
  rw [hresult]
  change
    mem_write_value (physaddr.Physaddr addr) 4
      (sign_extend (m := 4 * 8) result)
      (Atomic (op, Data, Data)) false false true js.sail =
    .ok (Ok true) (state_after_word_store js.sail addr result)
  rw [amo_word_sign_extend_4x8_eq_self result]
  exact
    amo_word_mem_write_value_eq_state_after_word_store
      op addr result js.sail hcfg h_align h_mem.sail_atomic_mem

/-- The final word AMO writeback state exists and is exactly the canonical
word AMO final state. -/
theorem amo_word_writeback_old_shape
    (rd : regidx) (s : SailState) (addr : BitVec 64) (result : BitVec 32) :
    ∃ writebackState : SailState,
      wX_bits rd (sign_extend (m := 64) (loaded_word_at s addr))
        (state_after_word_store s addr result) =
        .ok () writebackState ∧
      writebackState = amoWordFinalSailState rd s addr result := by
  obtain ⟨writebackState, hwriteback⟩ :=
    wX_shape rd (sign_extend (m := 64) (loaded_word_at s addr))
      (state_after_word_store s addr result)
  refine ⟨writebackState, hwriteback, ?_⟩
  exact
    wX_bits_eq_stateAfterWrite rd
      (sign_extend (m := 64) (loaded_word_at s addr))
      (state_after_word_store s addr result) writebackState hwriteback

/-- Sign-extending the shifted old word produced by `amoPre64Program` recovers
the native word load at the AMO address. -/
theorem amo_word_shifted_old_sign_extend_eq_loaded_word
    (s : SailState) (addr : BitVec 64)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    (let shifted :=
      shift_bits_right (loaded_dword_at s (amoWordBase addr))
        (Sail.BitVec.extractLsb (shift_bits_left addr (3 : BitVec 6)) 5 0)
     sign_extend (m := 64)
        ((Sail.BitVec.extractLsb shifted 31 0) : BitVec 32)) =
    sign_extend (m := 64) (loaded_word_at s addr) := by
  simp only [srl_sign_extend_word_extracts_word _ _ h_align,
    ← loaded_word_in_dword _ _ h_align]

private theorem sign_extend_64_setWidth_32 (x : BitVec 32) :
    (sign_extend (m := 64) x).setWidth 32 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth]
  change ((i<b32) && (BitVec.signExtend 64 x).getLsbD i) = x.getLsbD i
  rw [BitVec.getLsbD_signExtend]
  have hi64 : i < 64 := by omega
  simp [hi, hi64]

/-- Sign-extension from 32 to 64 bits is injective. -/
theorem amo_word_sign_extend_64_injective
    {lhs rhs : BitVec 32}
    (h : sign_extend (m := 64) lhs = sign_extend (m := 64) rhs) :
    lhs = rhs := by
  have h' := congrArg (fun x : BitVec 64 => x.setWidth 32) h
  change (sign_extend (m := 64) lhs).setWidth 32 =
    (sign_extend (m := 64) rhs).setWidth 32 at h'
  rw [sign_extend_64_setWidth_32 lhs, sign_extend_64_setWidth_32 rhs] at h'
  exact h'

/-- The shifted old dword produced by the word-AMO prelude has the native old
word in its low 32 bits. -/
theorem amo_word_shifted_old_extract_eq_loaded_word
    (s : SailState) (addr : BitVec 64)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    (let shifted :=
      shift_bits_right (loaded_dword_at s (amoWordBase addr))
        (Sail.BitVec.extractLsb (shift_bits_left addr (3 : BitVec 6)) 5 0)
     (Sail.BitVec.extractLsb shifted 31 0 : BitVec 32)) =
    loaded_word_at s addr := by
  exact
    amo_word_sign_extend_64_injective
      (amo_word_shifted_old_sign_extend_eq_loaded_word s addr h_align)

/-- The named shifted-old prelude value has the native old word in its low
32 bits. -/
theorem amo_word_shifted_old_abbrev_extract_eq_loaded_word
    (s : SailState) (addr : BitVec 64)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    (Sail.BitVec.extractLsb (amoWordShiftedOld s addr) 31 0 :
      BitVec 32) =
    loaded_word_at s addr := by
  exact amo_word_shifted_old_extract_eq_loaded_word s addr h_align

/-- Extracting the low word of a 64-bit addition is the same as adding the low
words. -/
theorem amo_word_extract_add_low
    (lhs rhs : BitVec 64) :
    (Sail.BitVec.extractLsb (lhs + rhs) 31 0 : BitVec 32) =
      (Sail.BitVec.extractLsb lhs 31 0 : BitVec 32) +
        (Sail.BitVec.extractLsb rhs 31 0 : BitVec 32) := by
  unfold Sail.BitVec.extractLsb
  bv_decide

/-- Extracting the low word of a 64-bit bitwise-and is the same as anding the
low words. -/
theorem amo_word_extract_and_low
    (lhs rhs : BitVec 64) :
    (Sail.BitVec.extractLsb (lhs &&& rhs) 31 0 : BitVec 32) =
      (Sail.BitVec.extractLsb lhs 31 0 : BitVec 32) &&&
        (Sail.BitVec.extractLsb rhs 31 0 : BitVec 32) := by
  unfold Sail.BitVec.extractLsb
  bv_decide

/-- Extracting the low word of a 64-bit bitwise-or is the same as oring the
low words. -/
theorem amo_word_extract_or_low
    (lhs rhs : BitVec 64) :
    (Sail.BitVec.extractLsb (lhs ||| rhs) 31 0 : BitVec 32) =
      (Sail.BitVec.extractLsb lhs 31 0 : BitVec 32) |||
        (Sail.BitVec.extractLsb rhs 31 0 : BitVec 32) := by
  unfold Sail.BitVec.extractLsb
  bv_decide

/-- Extracting the low word of a 64-bit bitwise-xor is the same as xoring the
low words. -/
theorem amo_word_extract_xor_low
    (lhs rhs : BitVec 64) :
    (Sail.BitVec.extractLsb (lhs ^^^ rhs) 31 0 : BitVec 32) =
      (Sail.BitVec.extractLsb lhs 31 0 : BitVec 32) ^^^
        (Sail.BitVec.extractLsb rhs 31 0 : BitVec 32) := by
  unfold Sail.BitVec.extractLsb
  bv_decide

/-- The Jolt `AMOADD.W` middle result has the same low word as Sail's native
word addition result. -/
theorem amo_word_add_result_extract_eq
    (s : SailState) (addr rs2Val : BitVec 64)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    (let old :=
      shift_bits_right (loaded_dword_at s (amoWordBase addr))
        (Sail.BitVec.extractLsb (shift_bits_left addr (3 : BitVec 6)) 5 0)
     (Sail.BitVec.extractLsb (rs2Val + old) 31 0 : BitVec 32)) =
    (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32) +
      loaded_word_at s addr := by
  rw [amo_word_extract_add_low]
  rw [amo_word_shifted_old_extract_eq_loaded_word s addr h_align]

/-- The Jolt `AMOAND.W` middle result has the same low word as Sail's native
word bitwise-and result. -/
theorem amo_word_and_result_extract_eq
    (s : SailState) (addr rs2Val : BitVec 64)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    (let old :=
      shift_bits_right (loaded_dword_at s (amoWordBase addr))
        (Sail.BitVec.extractLsb (shift_bits_left addr (3 : BitVec 6)) 5 0)
     (Sail.BitVec.extractLsb (rs2Val &&& old) 31 0 : BitVec 32)) =
    (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32) &&&
      loaded_word_at s addr := by
  rw [amo_word_extract_and_low]
  rw [amo_word_shifted_old_extract_eq_loaded_word s addr h_align]

/-- The Jolt `AMOOR.W` middle result has the same low word as Sail's native
word bitwise-or result. -/
theorem amo_word_or_result_extract_eq
    (s : SailState) (addr rs2Val : BitVec 64)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    (let old :=
      shift_bits_right (loaded_dword_at s (amoWordBase addr))
        (Sail.BitVec.extractLsb (shift_bits_left addr (3 : BitVec 6)) 5 0)
     (Sail.BitVec.extractLsb (rs2Val ||| old) 31 0 : BitVec 32)) =
    (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32) |||
      loaded_word_at s addr := by
  rw [amo_word_extract_or_low]
  rw [amo_word_shifted_old_extract_eq_loaded_word s addr h_align]

/-- The Jolt `AMOXOR.W` middle result has the same low word as Sail's native
word bitwise-xor result. -/
theorem amo_word_xor_result_extract_eq
    (s : SailState) (addr rs2Val : BitVec 64)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    (let old :=
      shift_bits_right (loaded_dword_at s (amoWordBase addr))
        (Sail.BitVec.extractLsb (shift_bits_left addr (3 : BitVec 6)) 5 0)
     (Sail.BitVec.extractLsb (rs2Val ^^^ old) 31 0 : BitVec 32)) =
    (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32) ^^^
      loaded_word_at s addr := by
  rw [amo_word_extract_xor_low]
  rw [amo_word_shifted_old_extract_eq_loaded_word s addr h_align]

/-- Once the aligned AMO setup facts have been reduced, the generated Sail
word executor follows the concrete non-CAS write path and retires
successfully. -/
theorem execute_AMO_word_non_cas_aligned_core
    (op : amoop) (rs2 rs1 rd : regidx) (js : SailJoltState)
    (addr rs2Val rdVal : BitVec 64) (result : BitVec 32)
    (writebackState : SailState)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd_read : rX_bits rd js.sail = .ok rdVal js.sail)
    (hnot_cas : (op == amoop.AMOCAS) = false)
    (h_vaddr_aligned : is_aligned_vaddr (Virtaddr addr) 4 = true)
    (htranslate :
      translateAddr (Virtaddr addr) (Atomic (op, Data, Data)) js.sail =
        .ok (Ok (physaddr.Physaddr addr, init_ext_ptw)) js.sail)
    (hea :
      mem_write_ea (physaddr.Physaddr addr) 4 false false true js.sail =
        .ok (Ok ()) js.sail)
    (hread :
      mem_read (Atomic (op, Data, Data))
        (physaddr.Physaddr addr) 4 false false true js.sail =
        .ok (Ok (loaded_word_at js.sail addr)) js.sail)
    (hwrite_value :
      mem_write_value (physaddr.Physaddr addr) 4
        (sign_extend (m := ((8 : Int) * ((4 : Nat) : Int)).toNat)
          (amoWordSailResult op
            (show BitVec (4 * 8) from
              trunc (m := (((4 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
            (BitVec.setWidth (4 * 8) (loaded_word_at js.sail addr))))
        (Atomic (op, Data, Data)) false false true js.sail =
        .ok (Ok true) (state_after_word_store js.sail addr result))
    (hwriteback_loaded_direct :
      wX_bits rd
        (sign_extend (m := 64)
          (BitVec.setWidth (4 * 8) (loaded_word_at js.sail addr)))
        (state_after_word_store js.sail addr result) =
        .ok () writebackState)
    (hwriteback_state :
      writebackState = amoWordFinalSailState rd js.sail addr result) :
    (execute_AMO op false false rs2 rs1 4 rd).run js.sail =
      .ok RETIRE_SUCCESS (amoWordFinalSailState rd js.sail addr result) := by
  have haddr0 : addr + zeros (n := 64) = addr := by
    unfold zeros
    exact BitVec.add_zero addr
  cases hop : op
  case AMOCAS =>
    rw [hop] at hnot_cas
    cases hnot_cas
  all_goals
    have hcas_check : decide (op.ctorIdx = amoop.AMOCAS.ctorIdx) = false := by
      rw [hop]
      decide
    rw [hop] at htranslate hread hcas_check hwrite_value
    simp only [amoWordSailResult] at hwrite_value
    unfold execute_AMO
    simp only [bind, pure]
    unfold Sail.assert LeanRV64D.Functions.xlen_bytes
    simp only [amo_word_execute_width_assert_true, PreSail.assert, pure,
      EStateM.run, if_true]
    unfold SailME.run PreSail.PreSailME.run
    simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
      ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
      ExceptT.pure, ExceptT.lift, MonadLift.monadLift, liftM, monadLift,
      Functor.map, SailME.throw, PreSail.PreSailME.throw,
      MonadExceptOf.throw, ext_data_get_addr, hrs1, haddr0,
      h_vaddr_aligned, LeanRV64D.Functions.not, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, htranslate,
      amo_word_width4_true, hrs2, hea, hread, hrd_read, hcas_check,
      Bool.false_and, instBEqAmoop.beq, BEq.beq]
    rw [hwrite_value]
    simp only [EStateM.bind, EStateM.map, ExceptT.bindCont,
      hwriteback_loaded_direct, hwriteback_state, EStateM.pure]

/-- Shared Sail-side aligned reduction for 32-bit non-CAS AMOs.

The generated Sail code reads `rd` while evaluating the AMOCAS guard, even when
`op` is later shown not to be AMOCAS. Callers therefore supply `hrd`. -/
theorem execute_AMO_word_non_cas_aligned
    (op : amoop) (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64) (result : BitVec 32)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryContext op 4 (amoWordBase addr) addr js.sail)
    (h_align : addr &&& (3 : BitVec 64) = 0)
    (hnot_cas : (op == amoop.AMOCAS) = false)
    (hresult :
      amoWordSailResult op
        (show BitVec (4 * 8) from
          trunc (m := (((4 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
        (BitVec.setWidth (4 * 8) (loaded_word_at js.sail addr)) =
      result) :
    (execute_AMO op false false rs2 rs1 4 rd).run js.sail =
      .ok RETIRE_SUCCESS (amoWordFinalSailState rd js.sail addr result) := by
  have h_no_ovf := amo_word_base_no_ovf addr
  obtain ⟨rdVal, hrd_read⟩ := hrd
  obtain ⟨writebackState, hwriteback, hwriteback_state⟩ :=
    amo_word_writeback_old_shape rd js.sail addr result
  exact
    execute_AMO_word_non_cas_aligned_core
      op rs2 rs1 rd js addr rs2Val rdVal result writebackState
      hrs1 hrs2 hrd_read hnot_cas
      (amo_word_is_aligned_vaddr_true addr h_align)
      (translateAddr_atomic_data_of_joltConfig op addr js.sail hcfg)
      (amo_word_mem_write_ea_ok addr js.sail h_align)
      (amo_word_mem_read_eq_loaded_word op addr js.sail hcfg
        (amo_word_aligned_no_ovf addr h_no_ovf h_align)
        h_align h_mem.sail_atomic_mem)
      (amo_word_mem_write_value_sail_result
        op addr rs2Val result js hcfg h_mem h_align hresult)
      (amo_word_writeback_loaded_direct
        rd js.sail writebackState addr result hwriteback)
      hwriteback_state

/-- `VirtualMULI` from an architectural source to a virtual destination writes
the wrapped product and leaves the Sail state unchanged. -/
theorem amo_word_virtual_muli_run_vreg_xreg
    (vd : JoltISA.VReg) (rs : regidx) (imm : BitVec 64)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail)
    (hvd : WritableVReg vd) :
    (JoltISA.execInstr (.VirtualMULI (.vreg vd) (.xreg rs) imm)).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then jolt_virtual_muli_value x imm else js.vregs r } := by
  unfold JoltISA.execInstr JoltISA.readSrc JoltISA.writeDst liftSail
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
  exact JoltISA.writeVReg_retire_run_of_writable vd
    (jolt_virtual_muli_value x imm) js hvd

/-- The aligned `.W` AMO prelude reaches the tail with the containing dword,
lane shift, and shifted old word in the standard AMO scratch registers. -/
theorem amo_word_pre64_aligned_run
    {op : amoop} (tail : JoltISA.Program)
    (rs1 : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (h_mem : AmoMemoryContext op 4 (amoWordBase addr) addr js.sail)
    (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    ∃ js_pre : SailJoltState,
      (JoltISA.execProgram
        (JoltISA.amoPre64Program rs1 JoltISA.amoOldVReg
          JoltISA.amoDwordVReg JoltISA.amoShiftVReg tail)).run js =
        (JoltISA.execProgram tail).run js_pre ∧
      js_pre.sail = js.sail ∧
      js_pre.vregs JoltISA.amoDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr) ∧
      js_pre.vregs JoltISA.amoShiftVReg =
        shift_bits_left addr (3 : BitVec 6) ∧
      js_pre.vregs JoltISA.amoOldVReg =
        shift_bits_right
          (loaded_dword_at js.sail (amoWordBase addr))
          (Sail.BitVec.extractLsb
            (shift_bits_left addr (3 : BitVec 6)) 5 0) := by
  have hassert :=
    amo_word_virtual_assert_aligned_run rs1 js addr hrs1 h_align
  obtain ⟨js_base, _hrs1_base, hbase_sail, hbase_shift_raw,
      _hbase_preserves, hbase_run⟩ :=
    JoltISA.exists_state_after_andi_run_vreg_xreg_of_sail_eq
      JoltISA.amoShiftVReg rs1 (-8 : BitVec 12) js js.sail addr rfl hrs1 (by unfold WritableVReg; decide)
  have hbase_shift :
      js_base.vregs JoltISA.amoShiftVReg = amoWordBase addr := by
    rw [hbase_shift_raw]
    exact amo_word_base_mask addr
  have hcfg_base : JoltConfig js_base.sail := by
    rw [hbase_sail]
    exact hcfg
  have hload_evidence :
      DwordLoadEvidence (amoWordBase addr) js_base.sail := by
    rw [hbase_sail]
    exact
      dwordLoadEvidence_of_aligned_phys (amoWordBase addr) js.sail
        (amo_word_base_aligned_access addr h_no_ovf)
        (AmoMemoryContext.jolt_load_mem h_mem)
  have hld :
      (JoltISA.execInstr
        (.LD (.vreg JoltISA.amoDwordVReg)
          (.vreg JoltISA.amoShiftVReg) (0 : BitVec 12))).run js_base =
        .ok RETIRE_SUCCESS
          { sail := js_base.sail
            vregs := fun r =>
              if r = JoltISA.amoDwordVReg then
                loaded_dword_at js_base.sail (amoWordBase addr)
              else js_base.vregs r } := by
    exact
      vreg_LD_run_of_dword_evidence
        JoltISA.amoDwordVReg JoltISA.amoShiftVReg js_base
        (amoWordBase addr) hbase_shift hcfg_base hload_evidence
        (by unfold WritableVReg; decide)
  let js_load : SailJoltState :=
    { sail := js_base.sail
      vregs := fun r =>
        if r = JoltISA.amoDwordVReg then
          loaded_dword_at js_base.sail (amoWordBase addr)
        else js_base.vregs r }
  have hld_named :
      (JoltISA.execInstr
        (.LD (.vreg JoltISA.amoDwordVReg)
          (.vreg JoltISA.amoShiftVReg) (0 : BitVec 12))).run js_base =
        .ok RETIRE_SUCCESS js_load := by
    exact hld
  have hload_sail : js_load.sail = js.sail := by
    exact hbase_sail
  have hload_dword :
      js_load.vregs JoltISA.amoDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr) := by
    change
      (if JoltISA.amoDwordVReg = JoltISA.amoDwordVReg then
          loaded_dword_at js_base.sail (amoWordBase addr)
        else js_base.vregs JoltISA.amoDwordVReg) =
        loaded_dword_at js.sail (amoWordBase addr)
    rw [if_pos rfl, hbase_sail]
  have hload_shift :
      js_load.vregs JoltISA.amoShiftVReg = amoWordBase addr := by
    change
      (if JoltISA.amoShiftVReg = JoltISA.amoDwordVReg then
          loaded_dword_at js_base.sail (amoWordBase addr)
        else js_base.vregs JoltISA.amoShiftVReg) =
        amoWordBase addr
    rw [if_neg (by decide)]
    exact hbase_shift
  have hrs1_load :
      rX_bits rs1 js_load.sail = .ok addr js_load.sail := by
    rw [hload_sail]
    exact hrs1
  have hmuli :
      (JoltISA.execInstr
        (.VirtualMULI (.vreg JoltISA.amoShiftVReg)
          (.xreg rs1) (8 : BitVec 64))).run js_load =
      .ok RETIRE_SUCCESS
        { sail := js_load.sail
          vregs := fun r =>
            if r = JoltISA.amoShiftVReg then
              jolt_virtual_muli_value addr (8 : BitVec 64)
            else js_load.vregs r } :=
    amo_word_virtual_muli_run_vreg_xreg
      JoltISA.amoShiftVReg rs1 (8 : BitVec 64) js_load addr hrs1_load
      (by unfold WritableVReg; decide)
  let js_shift : SailJoltState :=
    { sail := js_load.sail
      vregs := fun r =>
        if r = JoltISA.amoShiftVReg then
          jolt_virtual_muli_value addr (8 : BitVec 64)
        else js_load.vregs r }
  have hmuli_named :
      (JoltISA.execInstr
        (.VirtualMULI (.vreg JoltISA.amoShiftVReg)
          (.xreg rs1) (8 : BitVec 64))).run js_load =
      .ok RETIRE_SUCCESS js_shift := by
    exact hmuli
  have hshift_sail : js_shift.sail = js.sail := by
    exact hload_sail
  have hshift_dword :
      js_shift.vregs JoltISA.amoDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr) := by
    change
      (if JoltISA.amoDwordVReg = JoltISA.amoShiftVReg then
          jolt_virtual_muli_value addr (8 : BitVec 64)
        else js_load.vregs JoltISA.amoDwordVReg) =
        loaded_dword_at js.sail (amoWordBase addr)
    rw [if_neg (by decide)]
    exact hload_dword
  have hshift_shift :
      js_shift.vregs JoltISA.amoShiftVReg =
        shift_bits_left addr (3 : BitVec 6) := by
    change
      (if JoltISA.amoShiftVReg = JoltISA.amoShiftVReg then
          jolt_virtual_muli_value addr (8 : BitVec 64)
        else js_load.vregs JoltISA.amoShiftVReg) =
        shift_bits_left addr (3 : BitVec 6)
    rw [if_pos rfl]
    exact JoltISA.virtual_muli_eight_eq_shift_left_three addr
  have hbitmask :
      (JoltISA.execInstr
        (.VirtualShiftRightBitmask (.vreg JoltISA.amoInlineTmpVReg)
          (.vreg JoltISA.amoShiftVReg))).run js_shift =
      .ok RETIRE_SUCCESS
        { sail := js_shift.sail
          vregs := fun r =>
            if r = JoltISA.amoInlineTmpVReg then
              jolt_virtual_shift_right_bitmask_value
                (js_shift.vregs JoltISA.amoShiftVReg)
            else js_shift.vregs r } :=
    JoltISA.virtual_shift_right_bitmask_run_vreg_vreg
      JoltISA.amoInlineTmpVReg JoltISA.amoShiftVReg js_shift
      (by unfold WritableVReg; decide)
  let js_bitmask : SailJoltState :=
    { sail := js_shift.sail
      vregs := fun r =>
        if r = JoltISA.amoInlineTmpVReg then
          jolt_virtual_shift_right_bitmask_value
            (js_shift.vregs JoltISA.amoShiftVReg)
        else js_shift.vregs r }
  have hbitmask_named :
      (JoltISA.execInstr
        (.VirtualShiftRightBitmask (.vreg JoltISA.amoInlineTmpVReg)
          (.vreg JoltISA.amoShiftVReg))).run js_shift =
      .ok RETIRE_SUCCESS js_bitmask := by
    exact hbitmask
  have hbitmask_sail : js_bitmask.sail = js.sail := by
    exact hshift_sail
  have hbitmask_dword :
      js_bitmask.vregs JoltISA.amoDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr) := by
    change
      (if JoltISA.amoDwordVReg = JoltISA.amoInlineTmpVReg then
          jolt_virtual_shift_right_bitmask_value
            (js_shift.vregs JoltISA.amoShiftVReg)
        else js_shift.vregs JoltISA.amoDwordVReg) =
        loaded_dword_at js.sail (amoWordBase addr)
    rw [if_neg (by decide)]
    exact hshift_dword
  have hbitmask_shift :
      js_bitmask.vregs JoltISA.amoShiftVReg =
        shift_bits_left addr (3 : BitVec 6) := by
    change
      (if JoltISA.amoShiftVReg = JoltISA.amoInlineTmpVReg then
          jolt_virtual_shift_right_bitmask_value
            (js_shift.vregs JoltISA.amoShiftVReg)
        else js_shift.vregs JoltISA.amoShiftVReg) =
        shift_bits_left addr (3 : BitVec 6)
    rw [if_neg (by decide)]
    exact hshift_shift
  have hbitmask_tmp :
      js_bitmask.vregs JoltISA.amoInlineTmpVReg =
        jolt_virtual_shift_right_bitmask_value
          (shift_bits_left addr (3 : BitVec 6)) := by
    change
      (if JoltISA.amoInlineTmpVReg = JoltISA.amoInlineTmpVReg then
          jolt_virtual_shift_right_bitmask_value
            (js_shift.vregs JoltISA.amoShiftVReg)
        else js_shift.vregs JoltISA.amoInlineTmpVReg) =
        jolt_virtual_shift_right_bitmask_value
          (shift_bits_left addr (3 : BitVec 6))
    rw [if_pos rfl, hshift_shift]
  have hsrl :
      (JoltISA.execInstr
        (.VirtualSRL (.vreg JoltISA.amoOldVReg)
          (.vreg JoltISA.amoDwordVReg)
          (.vreg JoltISA.amoInlineTmpVReg))).run js_bitmask =
      .ok RETIRE_SUCCESS
        { sail := js_bitmask.sail
          vregs := fun r =>
            if r = JoltISA.amoOldVReg then
              jolt_virtual_srl_value
                (js_bitmask.vregs JoltISA.amoDwordVReg)
                (js_bitmask.vregs JoltISA.amoInlineTmpVReg)
            else js_bitmask.vregs r } :=
    JoltISA.virtual_srl_run_vreg_vreg_vreg
      JoltISA.amoOldVReg JoltISA.amoDwordVReg
      JoltISA.amoInlineTmpVReg js_bitmask
      (by unfold WritableVReg; decide)
  let js_pre : SailJoltState :=
    { sail := js_bitmask.sail
      vregs := fun r =>
        if r = JoltISA.amoOldVReg then
          jolt_virtual_srl_value
            (js_bitmask.vregs JoltISA.amoDwordVReg)
            (js_bitmask.vregs JoltISA.amoInlineTmpVReg)
        else js_bitmask.vregs r }
  have hsrl_named :
      (JoltISA.execInstr
        (.VirtualSRL (.vreg JoltISA.amoOldVReg)
          (.vreg JoltISA.amoDwordVReg)
          (.vreg JoltISA.amoInlineTmpVReg))).run js_bitmask =
      .ok RETIRE_SUCCESS js_pre := by
    exact hsrl
  refine ⟨js_pre, ?_, ?_, ?_, ?_, ?_⟩
  · unfold JoltISA.amoPre64Program JoltISA.amoPre64ProgramWithScratch
    rw [JoltISA.execProgram_instr_run_retire _ _ js js hassert]
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_base hbase_run]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_base js_load hld_named]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_load js_shift hmuli_named]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_shift js_bitmask hbitmask_named]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_bitmask js_pre hsrl_named]
  · exact hbitmask_sail
  · change
      (if JoltISA.amoDwordVReg = JoltISA.amoOldVReg then
          jolt_virtual_srl_value
            (js_bitmask.vregs JoltISA.amoDwordVReg)
            (js_bitmask.vregs JoltISA.amoInlineTmpVReg)
        else js_bitmask.vregs JoltISA.amoDwordVReg) =
        loaded_dword_at js.sail (amoWordBase addr)
    rw [if_neg (by decide)]
    exact hbitmask_dword
  · change
      (if JoltISA.amoShiftVReg = JoltISA.amoOldVReg then
          jolt_virtual_srl_value
            (js_bitmask.vregs JoltISA.amoDwordVReg)
            (js_bitmask.vregs JoltISA.amoInlineTmpVReg)
        else js_bitmask.vregs JoltISA.amoShiftVReg) =
        shift_bits_left addr (3 : BitVec 6)
    rw [if_neg (by decide)]
    exact hbitmask_shift
  · change
      (if JoltISA.amoOldVReg = JoltISA.amoOldVReg then
          jolt_virtual_srl_value
            (js_bitmask.vregs JoltISA.amoDwordVReg)
            (js_bitmask.vregs JoltISA.amoInlineTmpVReg)
        else js_bitmask.vregs JoltISA.amoOldVReg) =
        shift_bits_right
          (loaded_dword_at js.sail (amoWordBase addr))
          (Sail.BitVec.extractLsb
            (shift_bits_left addr (3 : BitVec 6)) 5 0)
    rw [if_pos rfl, hbitmask_dword, hbitmask_tmp]
    exact
      JoltISA.virtual_srl_shift_right_bitmask_value_eq
        (loaded_dword_at js.sail (amoWordBase addr))
        (shift_bits_left addr (3 : BitVec 6))

/-- Shape produced by the pure middle instruction in a word AMO binop
expansion.

The middle instruction computes the new candidate word value into
`amoNewVReg`, leaves the Sail state unchanged, and preserves the prelude state
needed by the postlude. -/
structure AmoWordMiddleStep
    (middle : JoltISA.Instr)
    (old dword shift result : BitVec 64)
    (js_before js_after : SailJoltState) : Prop where
  run :
    (JoltISA.execInstr middle).run js_before =
      .ok RETIRE_SUCCESS js_after
  sail : js_after.sail = js_before.sail
  result_vreg : js_after.vregs JoltISA.amoNewVReg = result
  old_vreg : js_after.vregs JoltISA.amoOldVReg = old
  dword_vreg : js_after.vregs JoltISA.amoDwordVReg = dword
  shift_vreg : js_after.vregs JoltISA.amoShiftVReg = shift

/-- Word AMO addition is commutative at the 64-bit scratch-register level. -/
theorem amo_word_add_comm (lhs rhs : BitVec 64) :
    lhs + rhs = rhs + lhs := by
  exact BitVec.add_comm lhs rhs

/-- Word AMO bitwise-and is commutative at the 64-bit scratch-register level. -/
theorem amo_word_and_comm (lhs rhs : BitVec 64) :
    lhs &&& rhs = rhs &&& lhs := by
  exact BitVec.and_comm lhs rhs

/-- Word AMO bitwise-or is commutative at the 64-bit scratch-register level. -/
theorem amo_word_or_comm (lhs rhs : BitVec 64) :
    lhs ||| rhs = rhs ||| lhs := by
  exact BitVec.or_comm lhs rhs

/-- Word AMO bitwise-xor is commutative at the 64-bit scratch-register level. -/
theorem amo_word_xor_comm (lhs rhs : BitVec 64) :
    lhs ^^^ rhs = rhs ^^^ lhs := by
  exact BitVec.xor_comm lhs rhs

/-- The `AMOADD.W` middle instruction writes `rs2 + old` to `amoNewVReg` and
preserves the word-AMO prelude registers. -/
theorem amo_word_add_middle_run
    (rs2 : regidx) (js_pre : SailJoltState)
    (rs2Val old dword shift : BitVec 64)
    (hrs2 : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail)
    (h_old : js_pre.vregs JoltISA.amoOldVReg = old)
    (h_dword : js_pre.vregs JoltISA.amoDwordVReg = dword)
    (h_shift : js_pre.vregs JoltISA.amoShiftVReg = shift) :
    ∃ js_afterMiddle : SailJoltState,
      AmoWordMiddleStep
        (.ADD (.vreg JoltISA.amoNewVReg)
          (.vreg JoltISA.amoOldVReg) (.xreg rs2))
        old dword shift (rs2Val + old) js_pre js_afterMiddle := by
  let js_afterMiddle : SailJoltState :=
    { sail := js_pre.sail
      vregs := fun r =>
        if r = JoltISA.amoNewVReg then old + rs2Val else js_pre.vregs r }
  refine ⟨js_afterMiddle, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold JoltISA.execInstr JoltISA.readSrc JoltISA.writeDst readVReg
      writeVReg liftSail
    simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
      get, getThe, MonadStateOf.get, EStateM.get,
      modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
      h_old, hrs2]
    rfl
  · rfl
  · change
      (if JoltISA.amoNewVReg = JoltISA.amoNewVReg then old + rs2Val
        else js_pre.vregs JoltISA.amoNewVReg) = rs2Val + old
    rw [if_pos rfl]
    exact amo_word_add_comm old rs2Val
  · change
      (if JoltISA.amoOldVReg = JoltISA.amoNewVReg then old + rs2Val
        else js_pre.vregs JoltISA.amoOldVReg) = old
    rw [if_neg (by decide)]
    exact h_old
  · change
      (if JoltISA.amoDwordVReg = JoltISA.amoNewVReg then old + rs2Val
        else js_pre.vregs JoltISA.amoDwordVReg) = dword
    rw [if_neg (by decide)]
    exact h_dword
  · change
      (if JoltISA.amoShiftVReg = JoltISA.amoNewVReg then old + rs2Val
        else js_pre.vregs JoltISA.amoShiftVReg) = shift
    rw [if_neg (by decide)]
    exact h_shift

/-- The `AMOAND.W` middle instruction writes `rs2 & old` to `amoNewVReg` and
preserves the word-AMO prelude registers. -/
theorem amo_word_and_middle_run
    (rs2 : regidx) (js_pre : SailJoltState)
    (rs2Val old dword shift : BitVec 64)
    (hrs2 : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail)
    (h_old : js_pre.vregs JoltISA.amoOldVReg = old)
    (h_dword : js_pre.vregs JoltISA.amoDwordVReg = dword)
    (h_shift : js_pre.vregs JoltISA.amoShiftVReg = shift) :
    ∃ js_afterMiddle : SailJoltState,
      AmoWordMiddleStep
        (.AND (.vreg JoltISA.amoNewVReg)
          (.vreg JoltISA.amoOldVReg) (.xreg rs2))
        old dword shift (rs2Val &&& old) js_pre js_afterMiddle := by
  let js_afterMiddle : SailJoltState :=
    { sail := js_pre.sail
      vregs := fun r =>
        if r = JoltISA.amoNewVReg then old &&& rs2Val else js_pre.vregs r }
  refine ⟨js_afterMiddle, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold JoltISA.execInstr JoltISA.readSrc JoltISA.writeDst readVReg
      writeVReg liftSail
    simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
      get, getThe, MonadStateOf.get, EStateM.get,
      modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
      h_old, hrs2]
    rfl
  · rfl
  · change
      (if JoltISA.amoNewVReg = JoltISA.amoNewVReg then old &&& rs2Val
        else js_pre.vregs JoltISA.amoNewVReg) = rs2Val &&& old
    rw [if_pos rfl]
    exact amo_word_and_comm old rs2Val
  · change
      (if JoltISA.amoOldVReg = JoltISA.amoNewVReg then old &&& rs2Val
        else js_pre.vregs JoltISA.amoOldVReg) = old
    rw [if_neg (by decide)]
    exact h_old
  · change
      (if JoltISA.amoDwordVReg = JoltISA.amoNewVReg then old &&& rs2Val
        else js_pre.vregs JoltISA.amoDwordVReg) = dword
    rw [if_neg (by decide)]
    exact h_dword
  · change
      (if JoltISA.amoShiftVReg = JoltISA.amoNewVReg then old &&& rs2Val
        else js_pre.vregs JoltISA.amoShiftVReg) = shift
    rw [if_neg (by decide)]
    exact h_shift

/-- The `AMOOR.W` middle instruction writes `rs2 | old` to `amoNewVReg` and
preserves the word-AMO prelude registers. -/
theorem amo_word_or_middle_run
    (rs2 : regidx) (js_pre : SailJoltState)
    (rs2Val old dword shift : BitVec 64)
    (hrs2 : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail)
    (h_old : js_pre.vregs JoltISA.amoOldVReg = old)
    (h_dword : js_pre.vregs JoltISA.amoDwordVReg = dword)
    (h_shift : js_pre.vregs JoltISA.amoShiftVReg = shift) :
    ∃ js_afterMiddle : SailJoltState,
      AmoWordMiddleStep
        (.OR (.vreg JoltISA.amoNewVReg)
          (.vreg JoltISA.amoOldVReg) (.xreg rs2))
        old dword shift (rs2Val ||| old) js_pre js_afterMiddle := by
  let js_afterMiddle : SailJoltState :=
    { sail := js_pre.sail
      vregs := fun r =>
        if r = JoltISA.amoNewVReg then old ||| rs2Val else js_pre.vregs r }
  refine ⟨js_afterMiddle, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold JoltISA.execInstr JoltISA.readSrc JoltISA.writeDst readVReg
      writeVReg liftSail
    simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
      get, getThe, MonadStateOf.get, EStateM.get,
      modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
      h_old, hrs2]
    rfl
  · rfl
  · change
      (if JoltISA.amoNewVReg = JoltISA.amoNewVReg then old ||| rs2Val
        else js_pre.vregs JoltISA.amoNewVReg) = rs2Val ||| old
    rw [if_pos rfl]
    exact amo_word_or_comm old rs2Val
  · change
      (if JoltISA.amoOldVReg = JoltISA.amoNewVReg then old ||| rs2Val
        else js_pre.vregs JoltISA.amoOldVReg) = old
    rw [if_neg (by decide)]
    exact h_old
  · change
      (if JoltISA.amoDwordVReg = JoltISA.amoNewVReg then old ||| rs2Val
        else js_pre.vregs JoltISA.amoDwordVReg) = dword
    rw [if_neg (by decide)]
    exact h_dword
  · change
      (if JoltISA.amoShiftVReg = JoltISA.amoNewVReg then old ||| rs2Val
        else js_pre.vregs JoltISA.amoShiftVReg) = shift
    rw [if_neg (by decide)]
    exact h_shift

/-- The `AMOXOR.W` middle instruction writes `rs2 ^ old` to `amoNewVReg` and
preserves the word-AMO prelude registers. -/
theorem amo_word_xor_middle_run
    (rs2 : regidx) (js_pre : SailJoltState)
    (rs2Val old dword shift : BitVec 64)
    (hrs2 : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail)
    (h_old : js_pre.vregs JoltISA.amoOldVReg = old)
    (h_dword : js_pre.vregs JoltISA.amoDwordVReg = dword)
    (h_shift : js_pre.vregs JoltISA.amoShiftVReg = shift) :
    ∃ js_afterMiddle : SailJoltState,
      AmoWordMiddleStep
        (.XOR (.vreg JoltISA.amoNewVReg)
          (.vreg JoltISA.amoOldVReg) (.xreg rs2))
        old dword shift (rs2Val ^^^ old) js_pre js_afterMiddle := by
  let js_afterMiddle : SailJoltState :=
    { sail := js_pre.sail
      vregs := fun r =>
        if r = JoltISA.amoNewVReg then old ^^^ rs2Val else js_pre.vregs r }
  refine ⟨js_afterMiddle, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold JoltISA.execInstr JoltISA.readSrc JoltISA.writeDst readVReg
      writeVReg liftSail
    simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
      get, getThe, MonadStateOf.get, EStateM.get,
      modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
      h_old, hrs2]
    rfl
  · rfl
  · change
      (if JoltISA.amoNewVReg = JoltISA.amoNewVReg then old ^^^ rs2Val
        else js_pre.vregs JoltISA.amoNewVReg) = rs2Val ^^^ old
    rw [if_pos rfl]
    exact amo_word_xor_comm old rs2Val
  · change
      (if JoltISA.amoOldVReg = JoltISA.amoNewVReg then old ^^^ rs2Val
        else js_pre.vregs JoltISA.amoOldVReg) = old
    rw [if_neg (by decide)]
    exact h_old
  · change
      (if JoltISA.amoDwordVReg = JoltISA.amoNewVReg then old ^^^ rs2Val
        else js_pre.vregs JoltISA.amoDwordVReg) = dword
    rw [if_neg (by decide)]
    exact h_dword
  · change
      (if JoltISA.amoShiftVReg = JoltISA.amoNewVReg then old ^^^ rs2Val
        else js_pre.vregs JoltISA.amoShiftVReg) = shift
    rw [if_neg (by decide)]
    exact h_shift

/-- After the common word prelude, the `AMOADD.W` middle instruction is ready
for the shared word-binop program helper. -/
theorem amo_word_add_middle_after_pre
    (rs2 : regidx) (js : SailJoltState) (addr rs2Val : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail) :
    ∀ js_pre : SailJoltState,
      js_pre.sail = js.sail →
      js_pre.vregs JoltISA.amoDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr) →
      js_pre.vregs JoltISA.amoShiftVReg =
        shift_bits_left addr (3 : BitVec 6) →
      js_pre.vregs JoltISA.amoOldVReg =
        shift_bits_right
          (loaded_dword_at js.sail (amoWordBase addr))
          (Sail.BitVec.extractLsb
            (shift_bits_left addr (3 : BitVec 6)) 5 0) →
      ∃ js_afterMiddle : SailJoltState,
        AmoWordMiddleStep
          (.ADD (.vreg JoltISA.amoNewVReg)
            (.vreg JoltISA.amoOldVReg) (.xreg rs2))
          (shift_bits_right
            (loaded_dword_at js.sail (amoWordBase addr))
            (Sail.BitVec.extractLsb
              (shift_bits_left addr (3 : BitVec 6)) 5 0))
          (loaded_dword_at js.sail (amoWordBase addr))
          (shift_bits_left addr (3 : BitVec 6))
          (rs2Val +
            shift_bits_right
              (loaded_dword_at js.sail (amoWordBase addr))
              (Sail.BitVec.extractLsb
                (shift_bits_left addr (3 : BitVec 6)) 5 0))
          js_pre js_afterMiddle := by
  intro js_pre hpre_sail hpre_dword hpre_shift hpre_old
  have hrs2_pre : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail := by
    rw [hpre_sail]
    exact hrs2
  exact
    amo_word_add_middle_run rs2 js_pre rs2Val
      (shift_bits_right
        (loaded_dword_at js.sail (amoWordBase addr))
        (Sail.BitVec.extractLsb
          (shift_bits_left addr (3 : BitVec 6)) 5 0))
      (loaded_dword_at js.sail (amoWordBase addr))
      (shift_bits_left addr (3 : BitVec 6))
      hrs2_pre hpre_old hpre_dword hpre_shift

/-- After the common word prelude, the `AMOAND.W` middle instruction is ready
for the shared word-binop program helper. -/
theorem amo_word_and_middle_after_pre
    (rs2 : regidx) (js : SailJoltState) (addr rs2Val : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail) :
    ∀ js_pre : SailJoltState,
      js_pre.sail = js.sail →
      js_pre.vregs JoltISA.amoDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr) →
      js_pre.vregs JoltISA.amoShiftVReg =
        shift_bits_left addr (3 : BitVec 6) →
      js_pre.vregs JoltISA.amoOldVReg =
        shift_bits_right
          (loaded_dword_at js.sail (amoWordBase addr))
          (Sail.BitVec.extractLsb
            (shift_bits_left addr (3 : BitVec 6)) 5 0) →
      ∃ js_afterMiddle : SailJoltState,
        AmoWordMiddleStep
          (.AND (.vreg JoltISA.amoNewVReg)
            (.vreg JoltISA.amoOldVReg) (.xreg rs2))
          (shift_bits_right
            (loaded_dword_at js.sail (amoWordBase addr))
            (Sail.BitVec.extractLsb
              (shift_bits_left addr (3 : BitVec 6)) 5 0))
          (loaded_dword_at js.sail (amoWordBase addr))
          (shift_bits_left addr (3 : BitVec 6))
          (rs2Val &&&
            shift_bits_right
              (loaded_dword_at js.sail (amoWordBase addr))
              (Sail.BitVec.extractLsb
                (shift_bits_left addr (3 : BitVec 6)) 5 0))
          js_pre js_afterMiddle := by
  intro js_pre hpre_sail hpre_dword hpre_shift hpre_old
  have hrs2_pre : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail := by
    rw [hpre_sail]
    exact hrs2
  exact
    amo_word_and_middle_run rs2 js_pre rs2Val
      (shift_bits_right
        (loaded_dword_at js.sail (amoWordBase addr))
        (Sail.BitVec.extractLsb
          (shift_bits_left addr (3 : BitVec 6)) 5 0))
      (loaded_dword_at js.sail (amoWordBase addr))
      (shift_bits_left addr (3 : BitVec 6))
      hrs2_pre hpre_old hpre_dword hpre_shift

/-- After the common word prelude, the `AMOOR.W` middle instruction is ready
for the shared word-binop program helper. -/
theorem amo_word_or_middle_after_pre
    (rs2 : regidx) (js : SailJoltState) (addr rs2Val : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail) :
    ∀ js_pre : SailJoltState,
      js_pre.sail = js.sail →
      js_pre.vregs JoltISA.amoDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr) →
      js_pre.vregs JoltISA.amoShiftVReg =
        shift_bits_left addr (3 : BitVec 6) →
      js_pre.vregs JoltISA.amoOldVReg =
        shift_bits_right
          (loaded_dword_at js.sail (amoWordBase addr))
          (Sail.BitVec.extractLsb
            (shift_bits_left addr (3 : BitVec 6)) 5 0) →
      ∃ js_afterMiddle : SailJoltState,
        AmoWordMiddleStep
          (.OR (.vreg JoltISA.amoNewVReg)
            (.vreg JoltISA.amoOldVReg) (.xreg rs2))
          (shift_bits_right
            (loaded_dword_at js.sail (amoWordBase addr))
            (Sail.BitVec.extractLsb
              (shift_bits_left addr (3 : BitVec 6)) 5 0))
          (loaded_dword_at js.sail (amoWordBase addr))
          (shift_bits_left addr (3 : BitVec 6))
          (rs2Val |||
            shift_bits_right
              (loaded_dword_at js.sail (amoWordBase addr))
              (Sail.BitVec.extractLsb
                (shift_bits_left addr (3 : BitVec 6)) 5 0))
          js_pre js_afterMiddle := by
  intro js_pre hpre_sail hpre_dword hpre_shift hpre_old
  have hrs2_pre : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail := by
    rw [hpre_sail]
    exact hrs2
  exact
    amo_word_or_middle_run rs2 js_pre rs2Val
      (shift_bits_right
        (loaded_dword_at js.sail (amoWordBase addr))
        (Sail.BitVec.extractLsb
          (shift_bits_left addr (3 : BitVec 6)) 5 0))
      (loaded_dword_at js.sail (amoWordBase addr))
      (shift_bits_left addr (3 : BitVec 6))
      hrs2_pre hpre_old hpre_dword hpre_shift

/-- After the common word prelude, the `AMOXOR.W` middle instruction is ready
for the shared word-binop program helper. -/
theorem amo_word_xor_middle_after_pre
    (rs2 : regidx) (js : SailJoltState) (addr rs2Val : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail) :
    ∀ js_pre : SailJoltState,
      js_pre.sail = js.sail →
      js_pre.vregs JoltISA.amoDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr) →
      js_pre.vregs JoltISA.amoShiftVReg =
        shift_bits_left addr (3 : BitVec 6) →
      js_pre.vregs JoltISA.amoOldVReg =
        shift_bits_right
          (loaded_dword_at js.sail (amoWordBase addr))
          (Sail.BitVec.extractLsb
            (shift_bits_left addr (3 : BitVec 6)) 5 0) →
      ∃ js_afterMiddle : SailJoltState,
        AmoWordMiddleStep
          (.XOR (.vreg JoltISA.amoNewVReg)
            (.vreg JoltISA.amoOldVReg) (.xreg rs2))
          (shift_bits_right
            (loaded_dword_at js.sail (amoWordBase addr))
            (Sail.BitVec.extractLsb
              (shift_bits_left addr (3 : BitVec 6)) 5 0))
          (loaded_dword_at js.sail (amoWordBase addr))
          (shift_bits_left addr (3 : BitVec 6))
          (rs2Val ^^^
            shift_bits_right
              (loaded_dword_at js.sail (amoWordBase addr))
              (Sail.BitVec.extractLsb
                (shift_bits_left addr (3 : BitVec 6)) 5 0))
          js_pre js_afterMiddle := by
  intro js_pre hpre_sail hpre_dword hpre_shift hpre_old
  have hrs2_pre : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail := by
    rw [hpre_sail]
    exact hrs2
  exact
    amo_word_xor_middle_run rs2 js_pre rs2Val
      (shift_bits_right
        (loaded_dword_at js.sail (amoWordBase addr))
        (Sail.BitVec.extractLsb
          (shift_bits_left addr (3 : BitVec 6)) 5 0))
      (loaded_dword_at js.sail (amoWordBase addr))
      (shift_bits_left addr (3 : BitVec 6))
      hrs2_pre hpre_old hpre_dword hpre_shift

/-- Reading architectural register `x0` is the pure zero read used by the word
AMO postlude's mask construction. -/
theorem amo_word_read_x0_eq_zero (s : SailState) :
    rX_bits (regidx.Regidx 0) s = .ok 0#64 s := by
  exact rX_bits_regidx_zero s

/-- The ORI seed used by the postlude is the all-ones dword. -/
theorem amo_word_seed_mask_value :
    (0#64) ||| sign_extend (m := 64) (-1 : BitVec 12) =
      (-1 : BitVec 64) := by
  decide

/-- Shifting the all-ones dword right by 32 creates the low-word mask. -/
theorem amo_word_low_word_mask_value :
    shift_bits_right (-1 : BitVec 64) (32 : BitVec 6) =
      (0x00000000FFFFFFFF : BitVec 64) := by
  unfold shift_bits_right
  bv_decide

/-- `AND` on virtual registers packaged with source values and preservation. -/
theorem amo_word_exists_state_after_and_run_vreg_vreg_vreg
    (vd lhs rhs : JoltISA.VReg) (js : SailJoltState) (x y : BitVec 64)
    (h_lhs : js.vregs lhs = x) (h_rhs : js.vregs rhs = y)
    (hvd : WritableVReg vd) :
    ∃ js',
      js'.sail = js.sail ∧
      js'.vregs vd = x &&& y ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      (JoltISA.execInstr (.AND (.vreg vd) (.vreg lhs) (.vreg rhs))).run js =
        .ok RETIRE_SUCCESS js' := by
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then js.vregs lhs &&& js.vregs rhs else js.vregs r }
  refine ⟨js', rfl, ?_, ?_, ?_⟩
  · change
      (if vd = vd then js.vregs lhs &&& js.vregs rhs else js.vregs vd) =
        x &&& y
    rw [if_pos rfl, h_lhs, h_rhs]
  · intro r hne
    change
      (if r = vd then js.vregs lhs &&& js.vregs rhs else js.vregs r) =
        js.vregs r
    rw [if_neg hne]
  · exact JoltISA.execInstr_and_vreg_vreg_vreg_run vd lhs rhs js hvd

/-- The shifted new word and shifted mask implement the store-family word
splice formula. -/
theorem amo_word_splice_shifted_eq
    (s : SailState) (addr newValue : BitVec 64)
    (hsetup : StoreSplice.WordStoreSetup addr (amoWordBase addr)) :
    let shift6 :=
      Sail.BitVec.extractLsb (shift_bits_left addr (3 : BitVec 6)) 5 0
    loaded_dword_at s (amoWordBase addr) ^^^
        (((loaded_dword_at s (amoWordBase addr) ^^^
          shift_bits_left newValue shift6) &&&
          shift_bits_left (0x00000000FFFFFFFF : BitVec 64) shift6)) =
      amoWordSplicedDword s addr newValue := by
  let base := amoWordBase addr
  let shift6 :=
    Sail.BitVec.extractLsb (shift_bits_left addr (3 : BitVec 6)) 5 0
  have hshift6 : shift6 = BitVec.ofNat 6 (((addr - base).toNat) * 8) :=
    amo_word_shift6_eq_offset addr base hsetup
  change
    loaded_dword_at s base ^^^
        (((loaded_dword_at s base ^^^ shift_bits_left newValue shift6) &&&
          shift_bits_left (0x00000000FFFFFFFF : BitVec 64) shift6)) =
      StoreSplice.wordSplice (loaded_dword_at s base)
        (Sail.BitVec.extractLsb newValue 31 0) (8 * ((addr - base).toNat))
  rw [hshift6]
  exact amo_word_splice_eq_sequence
    (loaded_dword_at s base) newValue ((addr - base).toNat) hsetup.offset_cases

/-- The first two postlude instructions seed the low-word mask and preserve the
loaded dword, lane shift, and old word. -/
theorem amo_word_mask32_prefix_run
    (js : SailJoltState) (s : SailState) (shift64 dword old : BitVec 64)
    (h_sail : js.sail = s)
    (h_shift : js.vregs JoltISA.amoShiftVReg = shift64)
    (h_dword : js.vregs JoltISA.amoDwordVReg = dword)
    (h_old : js.vregs JoltISA.amoOldVReg = old) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs JoltISA.amoMaskVReg =
        (0x00000000FFFFFFFF : BitVec 64) ∧
      js'.vregs JoltISA.amoShiftVReg = shift64 ∧
      js'.vregs JoltISA.amoDwordVReg = dword ∧
      js'.vregs JoltISA.amoOldVReg = old ∧
      js'.vregs JoltISA.amoNewVReg = js.vregs JoltISA.amoNewVReg ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.ORI (.vreg JoltISA.amoMaskVReg)
            (.xreg (regidx.Regidx 0)) (-1 : BitVec 12)) <|
           .instr (.VirtualSRLI (.vreg JoltISA.amoMaskVReg)
            (.vreg JoltISA.amoMaskVReg)
            (JoltISA.srliBitmask (32 : BitVec 6))) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  obtain ⟨js_ones, _hx0, hones_sail_raw, hones_mask_raw,
      hones_preserves, hones_run⟩ :=
    JoltISA.exists_state_after_ori_run_vreg_xreg_of_sail_eq
      JoltISA.amoMaskVReg (regidx.Regidx 0) (-1 : BitVec 12)
      js s (0#64) h_sail (amo_word_read_x0_eq_zero s) (by unfold WritableVReg; decide)
  have hones_sail : js_ones.sail = s := by
    rw [hones_sail_raw, h_sail]
  have hones_mask : js_ones.vregs JoltISA.amoMaskVReg = (-1 : BitVec 64) := by
    rw [hones_mask_raw]
    exact amo_word_seed_mask_value
  have hones_shift : js_ones.vregs JoltISA.amoShiftVReg = shift64 := by
    rw [hones_preserves JoltISA.amoShiftVReg (by decide)]
    exact h_shift
  have hones_dword : js_ones.vregs JoltISA.amoDwordVReg = dword := by
    rw [hones_preserves JoltISA.amoDwordVReg (by decide)]
    exact h_dword
  have hones_old : js_ones.vregs JoltISA.amoOldVReg = old := by
    rw [hones_preserves JoltISA.amoOldVReg (by decide)]
    exact h_old
  have hones_new :
      js_ones.vregs JoltISA.amoNewVReg = js.vregs JoltISA.amoNewVReg := by
    rw [hones_preserves JoltISA.amoNewVReg (by decide)]
  obtain ⟨js_mask, hmask_sail_raw, hmask_raw, hmask_preserves,
      hmask_tail⟩ :=
    JoltISA.exists_state_after_srli_block_run_vreg_vreg
      JoltISA.amoMaskVReg JoltISA.amoMaskVReg (32 : BitVec 6) js_ones
      (by unfold WritableVReg; decide)
  refine ⟨js_mask, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmask_sail_raw, hones_sail]
  · rw [hmask_raw, hones_mask]
    exact amo_word_low_word_mask_value
  · rw [hmask_preserves JoltISA.amoShiftVReg (by decide)]
    exact hones_shift
  · rw [hmask_preserves JoltISA.amoDwordVReg (by decide)]
    exact hones_dword
  · rw [hmask_preserves JoltISA.amoOldVReg (by decide)]
    exact hones_old
  · rw [hmask_preserves JoltISA.amoNewVReg (by decide)]
    exact hones_new
  · intro tail
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_ones hones_run]
    have htail := hmask_tail tail
    unfold JoltISA.srliBlock at htail
    exact htail

/-- The postlude's mask-shift block turns the low-word mask into the selected
word-lane mask. -/
theorem amo_word_shift_mask_prefix_run
    (js : SailJoltState) (s : SailState) (shift64 dword old : BitVec 64)
    (h_sail : js.sail = s)
    (h_mask : js.vregs JoltISA.amoMaskVReg =
      (0x00000000FFFFFFFF : BitVec 64))
    (h_shift : js.vregs JoltISA.amoShiftVReg = shift64)
    (h_dword : js.vregs JoltISA.amoDwordVReg = dword)
    (h_old : js.vregs JoltISA.amoOldVReg = old) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs JoltISA.amoMaskVReg =
        shift_bits_left (0x00000000FFFFFFFF : BitVec 64)
          (Sail.BitVec.extractLsb shift64 5 0) ∧
      js'.vregs JoltISA.amoShiftVReg = shift64 ∧
      js'.vregs JoltISA.amoDwordVReg = dword ∧
      js'.vregs JoltISA.amoOldVReg = old ∧
      js'.vregs JoltISA.amoNewVReg = js.vregs JoltISA.amoNewVReg ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.VirtualPow2 (.vreg JoltISA.amoInlineTmpVReg)
            (.vreg JoltISA.amoShiftVReg)) <|
           .instr (.MUL (.vreg JoltISA.amoMaskVReg)
            (.vreg JoltISA.amoMaskVReg)
            (.vreg JoltISA.amoInlineTmpVReg)) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  obtain ⟨js', h_sail_raw, h_mask_raw, h_preserves, htail⟩ :=
    JoltISA.exists_state_after_sll_block_run_vreg_vreg_vreg
      JoltISA.amoMaskVReg JoltISA.amoMaskVReg
      JoltISA.amoShiftVReg JoltISA.amoInlineTmpVReg js (by decide)
      (by unfold WritableVReg; decide) (by unfold WritableVReg; decide)
  refine ⟨js', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_sail_raw, h_sail]
  · rw [h_mask_raw, h_mask, h_shift]
  · rw [h_preserves JoltISA.amoShiftVReg (by decide) (by decide)]
    exact h_shift
  · rw [h_preserves JoltISA.amoDwordVReg (by decide) (by decide)]
    exact h_dword
  · rw [h_preserves JoltISA.amoOldVReg (by decide) (by decide)]
    exact h_old
  · rw [h_preserves JoltISA.amoNewVReg (by decide) (by decide)]
  · intro tail
    have h := htail tail
    unfold JoltISA.sllBlock at h
    exact h

/-- The postlude shifts the new word value from `rs2` into the selected dword
lane while preserving the prepared mask and old word. -/
theorem amo_word_shift_new_prefix_run
    (rs2 : regidx) (js : SailJoltState) (s : SailState)
    (rs2Val shift64 shiftedMask dword old : BitVec 64)
    (h_sail : js.sail = s)
    (hrs2 : rX_bits rs2 s = .ok rs2Val s)
    (h_mask : js.vregs JoltISA.amoMaskVReg = shiftedMask)
    (h_shift : js.vregs JoltISA.amoShiftVReg = shift64)
    (h_dword : js.vregs JoltISA.amoDwordVReg = dword)
    (h_old : js.vregs JoltISA.amoOldVReg = old) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs JoltISA.amoShiftVReg =
        shift_bits_left rs2Val (Sail.BitVec.extractLsb shift64 5 0) ∧
      js'.vregs JoltISA.amoMaskVReg = shiftedMask ∧
      js'.vregs JoltISA.amoDwordVReg = dword ∧
      js'.vregs JoltISA.amoOldVReg = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.VirtualPow2 (.vreg JoltISA.amoInlineTmpVReg)
            (.vreg JoltISA.amoShiftVReg)) <|
           .instr (.MUL (.vreg JoltISA.amoShiftVReg)
            (.xreg rs2) (.vreg JoltISA.amoInlineTmpVReg)) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  have hrs2_current : rX_bits rs2 js.sail = .ok rs2Val js.sail := by
    rw [h_sail]
    exact hrs2
  obtain ⟨js', _hrs2, h_sail_raw, h_shift_raw, h_preserves, htail⟩ :=
    JoltISA.exists_state_after_sll_block_run_vreg_xreg_vreg
      JoltISA.amoShiftVReg rs2 JoltISA.amoShiftVReg
      JoltISA.amoInlineTmpVReg js rs2Val hrs2_current
      (by unfold WritableVReg; decide) (by unfold WritableVReg; decide)
  refine ⟨js', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_sail_raw, h_sail]
  · rw [h_shift_raw, h_shift]
  · rw [h_preserves JoltISA.amoMaskVReg (by decide) (by decide)]
    exact h_mask
  · rw [h_preserves JoltISA.amoDwordVReg (by decide) (by decide)]
    exact h_dword
  · rw [h_preserves JoltISA.amoOldVReg (by decide) (by decide)]
    exact h_old
  · intro tail
    have h := htail tail
    unfold JoltISA.sllBlock at h
    exact h

/-- The postlude shifts a virtual-register new word value into the selected
dword lane while preserving the prepared mask and old word. -/
theorem amo_word_shift_new_vreg_prefix_run
    (new : JoltISA.VReg) (js : SailJoltState) (s : SailState)
    (newValue shift64 shiftedMask dword old : BitVec 64)
    (h_sail : js.sail = s)
    (h_new : js.vregs new = newValue)
    (h_mask : js.vregs JoltISA.amoMaskVReg = shiftedMask)
    (h_shift : js.vregs JoltISA.amoShiftVReg = shift64)
    (h_dword : js.vregs JoltISA.amoDwordVReg = dword)
    (h_old : js.vregs JoltISA.amoOldVReg = old)
    (hnew_ne_tmp : new ≠ JoltISA.amoInlineTmpVReg) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs JoltISA.amoShiftVReg =
        shift_bits_left newValue (Sail.BitVec.extractLsb shift64 5 0) ∧
      js'.vregs JoltISA.amoMaskVReg = shiftedMask ∧
      js'.vregs JoltISA.amoDwordVReg = dword ∧
      js'.vregs JoltISA.amoOldVReg = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.VirtualPow2 (.vreg JoltISA.amoInlineTmpVReg)
            (.vreg JoltISA.amoShiftVReg)) <|
           .instr (.MUL (.vreg JoltISA.amoShiftVReg)
            (.vreg new) (.vreg JoltISA.amoInlineTmpVReg)) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  obtain ⟨js', h_sail_raw, h_shift_raw, h_preserves, htail⟩ :=
    JoltISA.exists_state_after_sll_block_run_vreg_vreg_vreg
      JoltISA.amoShiftVReg new JoltISA.amoShiftVReg
      JoltISA.amoInlineTmpVReg js hnew_ne_tmp
      (by unfold WritableVReg; decide) (by unfold WritableVReg; decide)
  refine ⟨js', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_sail_raw, h_sail]
  · rw [h_shift_raw, h_new, h_shift]
  · rw [h_preserves JoltISA.amoMaskVReg (by decide) (by decide)]
    exact h_mask
  · rw [h_preserves JoltISA.amoDwordVReg (by decide) (by decide)]
    exact h_dword
  · rw [h_preserves JoltISA.amoOldVReg (by decide) (by decide)]
    exact h_old
  · intro tail
    have h := htail tail
    unfold JoltISA.sllBlock at h
    exact h

/-- The XOR/AND/XOR postlude block splices the shifted new word into the loaded
dword and preserves the shifted old word. -/
theorem amo_word_splice_block_run
    (js : SailJoltState) (s : SailState) (addr newValue old : BitVec 64)
    (hsetup : StoreSplice.WordStoreSetup addr (amoWordBase addr))
    (h_sail : js.sail = s)
    (h_dword :
      js.vregs JoltISA.amoDwordVReg =
        loaded_dword_at s (amoWordBase addr))
    (h_shift :
      js.vregs JoltISA.amoShiftVReg =
        shift_bits_left newValue
          (Sail.BitVec.extractLsb
            (shift_bits_left addr (3 : BitVec 6)) 5 0))
    (h_mask :
      js.vregs JoltISA.amoMaskVReg =
        shift_bits_left (0x00000000FFFFFFFF : BitVec 64)
          (Sail.BitVec.extractLsb
            (shift_bits_left addr (3 : BitVec 6)) 5 0))
    (h_old : js.vregs JoltISA.amoOldVReg = old) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs JoltISA.amoDwordVReg =
        amoWordSplicedDword s addr newValue ∧
      js'.vregs JoltISA.amoOldVReg = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.XOR (.vreg JoltISA.amoShiftVReg)
            (.vreg JoltISA.amoDwordVReg)
            (.vreg JoltISA.amoShiftVReg)) <|
           .instr (.AND (.vreg JoltISA.amoShiftVReg)
            (.vreg JoltISA.amoShiftVReg)
            (.vreg JoltISA.amoMaskVReg)) <|
           .instr (.XOR (.vreg JoltISA.amoDwordVReg)
            (.vreg JoltISA.amoDwordVReg)
            (.vreg JoltISA.amoShiftVReg)) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  let shiftedNew :=
    shift_bits_left newValue
      (Sail.BitVec.extractLsb (shift_bits_left addr (3 : BitVec 6)) 5 0)
  let shiftedMask :=
    shift_bits_left (0x00000000FFFFFFFF : BitVec 64)
      (Sail.BitVec.extractLsb (shift_bits_left addr (3 : BitVec 6)) 5 0)
  let dword := loaded_dword_at s (amoWordBase addr)
  obtain ⟨js_xor, hxor_sail_raw, hxor_shift_raw, hxor_preserves,
      hxor_run⟩ :=
    JoltISA.exists_state_after_xor_run_vreg_vreg_vreg
      JoltISA.amoShiftVReg JoltISA.amoDwordVReg
      JoltISA.amoShiftVReg js dword shiftedNew h_dword h_shift (by unfold WritableVReg; decide)
  have hxor_sail : js_xor.sail = s := by
    rw [hxor_sail_raw, h_sail]
  have hxor_shift : js_xor.vregs JoltISA.amoShiftVReg = dword ^^^ shiftedNew := by
    exact hxor_shift_raw
  have hxor_mask : js_xor.vregs JoltISA.amoMaskVReg = shiftedMask := by
    rw [hxor_preserves JoltISA.amoMaskVReg (by decide)]
    exact h_mask
  have hxor_dword : js_xor.vregs JoltISA.amoDwordVReg = dword := by
    rw [hxor_preserves JoltISA.amoDwordVReg (by decide)]
    exact h_dword
  have hxor_old : js_xor.vregs JoltISA.amoOldVReg = old := by
    rw [hxor_preserves JoltISA.amoOldVReg (by decide)]
    exact h_old
  obtain ⟨js_and, hand_sail_raw, hand_shift_raw, hand_preserves,
      hand_run⟩ :=
    amo_word_exists_state_after_and_run_vreg_vreg_vreg
      JoltISA.amoShiftVReg JoltISA.amoShiftVReg JoltISA.amoMaskVReg
      js_xor (dword ^^^ shiftedNew) shiftedMask hxor_shift hxor_mask
      (by unfold WritableVReg; decide)
  have hand_sail : js_and.sail = s := by
    rw [hand_sail_raw, hxor_sail]
  have hand_shift : js_and.vregs JoltISA.amoShiftVReg =
      (dword ^^^ shiftedNew) &&& shiftedMask := by
    exact hand_shift_raw
  have hand_dword : js_and.vregs JoltISA.amoDwordVReg = dword := by
    rw [hand_preserves JoltISA.amoDwordVReg (by decide)]
    exact hxor_dword
  have hand_old : js_and.vregs JoltISA.amoOldVReg = old := by
    rw [hand_preserves JoltISA.amoOldVReg (by decide)]
    exact hxor_old
  obtain ⟨js_splice, hsplice_sail_raw, hsplice_dword_raw,
      hsplice_preserves, hxor2_run⟩ :=
    JoltISA.exists_state_after_xor_run_vreg_vreg_vreg
      JoltISA.amoDwordVReg JoltISA.amoDwordVReg
      JoltISA.amoShiftVReg js_and dword
      ((dword ^^^ shiftedNew) &&& shiftedMask) hand_dword hand_shift (by unfold WritableVReg; decide)
  have hspliced_value := amo_word_splice_shifted_eq s addr newValue hsetup
  refine ⟨js_splice, ?_, ?_, ?_, ?_⟩
  · rw [hsplice_sail_raw, hand_sail]
  · rw [hsplice_dword_raw]
    exact hspliced_value
  · rw [hsplice_preserves JoltISA.amoOldVReg (by decide)]
    exact hand_old
  · intro tail
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_xor hxor_run]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_xor js_and hand_run]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_and js_splice hxor2_run]

/-- The postlude recomputes the enclosing dword base before storing it. -/
theorem amo_word_store_base_prefix_run
    (rs1 : regidx) (js : SailJoltState) (s : SailState)
    (addr dwordNew old : BitVec 64)
    (h_sail : js.sail = s)
    (hrs1 : rX_bits rs1 s = .ok addr s)
    (h_dword : js.vregs JoltISA.amoDwordVReg = dwordNew)
    (h_old : js.vregs JoltISA.amoOldVReg = old) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs JoltISA.amoMaskVReg = amoWordBase addr ∧
      js'.vregs JoltISA.amoDwordVReg = dwordNew ∧
      js'.vregs JoltISA.amoOldVReg = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.ANDI (.vreg JoltISA.amoMaskVReg)
            (.xreg rs1) (-8 : BitVec 12)) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  obtain ⟨js', _hrs1, h_sail_raw, h_base_raw, h_preserves, hrun⟩ :=
    JoltISA.exists_state_after_andi_run_vreg_xreg_of_sail_eq
      JoltISA.amoMaskVReg rs1 (-8 : BitVec 12) js s addr h_sail hrs1 (by unfold WritableVReg; decide)
  refine ⟨js', ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_sail_raw, h_sail]
  · rw [h_base_raw]
    exact amo_word_base_mask addr
  · rw [h_preserves JoltISA.amoDwordVReg (by decide)]
    exact h_dword
  · rw [h_preserves JoltISA.amoOldVReg (by decide)]
    exact h_old
  · intro tail
    rw [JoltISA.execProgram_instr_run_retire _ _ js js' hrun]

/-- The dword store instruction writes the spliced dword and preserves the
virtual-register file for the final writeback. -/
theorem amo_word_sd_spliced_dword_run
    {op : amoop}
    (js : SailJoltState) (s : SailState) (addr dwordNew old : BitVec 64)
    (hcfg : JoltConfig s)
    (h_mem : AmoMemoryContext op 4 (amoWordBase addr) addr s)
    (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
    (h_sail : js.sail = s)
    (h_base : js.vregs JoltISA.amoMaskVReg = amoWordBase addr)
    (h_dword : js.vregs JoltISA.amoDwordVReg = dwordNew)
    (h_old : js.vregs JoltISA.amoOldVReg = old) :
    ∃ js',
      js'.sail = state_after_dword_store s (amoWordBase addr) dwordNew ∧
      js'.vregs JoltISA.amoOldVReg = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.SD (.vreg JoltISA.amoMaskVReg)
            (.vreg JoltISA.amoDwordVReg) (0 : BitVec 12)) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  have hwrite_dword :
      vmem_write_addr (Virtaddr (amoWordBase addr)) 8 dwordNew
        (Store Data) false false false s =
      .ok (Ok true) (state_after_dword_store s (amoWordBase addr) dwordNew) :=
    vmem_write_addr_dword_store_reduces (amoWordBase addr) dwordNew s hcfg
      (amo_word_base_aligned_access addr h_no_ovf).toAlignedAccess
      (AmoMemoryContext.jolt_store_mem h_mem).pmp
      (AmoMemoryContext.jolt_store_mem h_mem).mmio
  have hwrite_current :
      vmem_write_addr (Virtaddr (js.vregs JoltISA.amoMaskVReg +
          sign_extend (m := 64) (0 : BitVec 12))) 8
        (js.vregs JoltISA.amoDwordVReg)
        (Store Data) false false false js.sail =
      .ok (Ok true) (state_after_dword_store s (amoWordBase addr) dwordNew) := by
    rw [h_sail, h_base, h_dword, amo_word_zero_offset_addr (amoWordBase addr)]
    exact hwrite_dword
  let js' : SailJoltState :=
    { sail := state_after_dword_store s (amoWordBase addr) dwordNew
      vregs := js.vregs }
  have hsd_align :
      (js.vregs JoltISA.amoMaskVReg + sign_extend (m := 64) (0 : BitVec 12)) &&&
          (7 : BitVec 64) =
        0 := by
    rw [h_base, amo_word_zero_offset_addr (amoWordBase addr)]
    exact amo_word_base_aligned addr
  have hsd :
      (JoltISA.execInstr
        (.SD (.vreg JoltISA.amoMaskVReg)
          (.vreg JoltISA.amoDwordVReg) (0 : BitVec 12))).run js =
        .ok RETIRE_SUCCESS js' :=
    JoltISA.execInstr_sd_vreg_run_of_write
      JoltISA.amoMaskVReg JoltISA.amoDwordVReg (0 : BitVec 12)
      js (state_after_dword_store s (amoWordBase addr) dwordNew) hsd_align hwrite_current
  refine ⟨js', rfl, ?_, ?_⟩
  · exact h_old
  · intro tail
    rw [JoltISA.execProgram_instr_run_retire _ _ js js' hsd]

/-- The final postlude instruction writes the sign-extended old word to `rd`. -/
theorem amo_word_writeback_old_run
    (rd : regidx) (js : SailJoltState) (s : SailState)
    (addr : BitVec 64) (result : BitVec 32) (old : BitVec 64)
    (h_sail : js.sail = state_after_word_store s addr result)
    (h_old : js.vregs JoltISA.amoOldVReg = old)
    (h_old_word :
      sign_extend (m := 64)
        ((Sail.BitVec.extractLsb old 31 0) : BitVec 32) =
      sign_extend (m := 64) (loaded_word_at s addr)) :
    ∃ js',
      js'.sail = amoWordFinalSailState rd s addr result ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.VirtualSignExtendWord (.xreg rd)
            (.vreg JoltISA.amoOldVReg)) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  obtain ⟨writebackState, hwriteback, hwriteback_state⟩ :=
    amo_word_writeback_old_shape rd s addr result
  have hwriteback_current :
      wX_bits rd
        (sign_extend (m := 64)
          ((Sail.BitVec.extractLsb
            (js.vregs JoltISA.amoOldVReg) 31 0) : BitVec 32))
        js.sail =
      .ok () writebackState := by
    rw [h_sail, h_old, h_old_word]
    exact hwriteback
  let js' : SailJoltState := { sail := writebackState, vregs := js.vregs }
  have hsext :
      (JoltISA.execInstr
        (.VirtualSignExtendWord (.xreg rd)
          (.vreg JoltISA.amoOldVReg))).run js =
        .ok RETIRE_SUCCESS js' :=
    JoltISA.virtual_sign_extend_word_run_xreg_vreg
      rd JoltISA.amoOldVReg js writebackState hwriteback_current
  refine ⟨js', ?_, ?_⟩
  · exact hwriteback_state
  · intro tail
    rw [JoltISA.execProgram_instr_run_retire _ _ js js' hsext]

/-- The aligned word-AMO postlude stores the low 32 bits of a virtual-register
new value into the selected word lane and writes the sign-extended old word
into `rd`. -/
theorem amo_word_post64_vreg_aligned_run
    {op : amoop} (rs1 rd : regidx)
    (js js_pre : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr newValue : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (h_mem : AmoMemoryContext op 4 (amoWordBase addr) addr js.sail)
    (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (3 : BitVec 64) = 0)
    (hpre_sail : js_pre.sail = js.sail)
    (hpre_new : js_pre.vregs JoltISA.amoNewVReg = newValue)
    (hpre_dword :
      js_pre.vregs JoltISA.amoDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr))
    (hpre_shift :
      js_pre.vregs JoltISA.amoShiftVReg =
        shift_bits_left addr (3 : BitVec 6))
    (hpre_old :
      js_pre.vregs JoltISA.amoOldVReg =
        shift_bits_right
          (loaded_dword_at js.sail (amoWordBase addr))
          (Sail.BitVec.extractLsb
            (shift_bits_left addr (3 : BitVec 6)) 5 0)) :
    ∃ jsf : SailJoltState,
      (JoltISA.execProgram
        (JoltISA.amoPost64Program rs1 rd (.vreg JoltISA.amoNewVReg)
          JoltISA.amoDwordVReg JoltISA.amoShiftVReg
          JoltISA.amoMaskVReg JoltISA.amoOldVReg)).run js_pre =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail =
        amoWordFinalSailState rd js.sail addr
          (Sail.BitVec.extractLsb newValue 31 0) := by
  let shift64 := shift_bits_left addr (3 : BitVec 6)
  let shift6 := Sail.BitVec.extractLsb shift64 5 0
  let dword := loaded_dword_at js.sail (amoWordBase addr)
  let old := shift_bits_right dword shift6
  let mask32 := (0x00000000FFFFFFFF : BitVec 64)
  let shiftedMask := shift_bits_left mask32 shift6
  let dwordNew := amoWordSplicedDword js.sail addr newValue
  let wordResult : BitVec 32 := Sail.BitVec.extractLsb newValue 31 0
  have hsetup := amo_word_store_setup addr h_no_ovf h_align
  obtain ⟨js_mask32, hmask_sail, hmask_mask, hmask_shift, hmask_dword,
      hmask_old, hmask_new_preserve, hmask_tail⟩ :=
    amo_word_mask32_prefix_run js_pre js.sail shift64 dword old
      hpre_sail hpre_shift hpre_dword hpre_old
  have hmask_new : js_mask32.vregs JoltISA.amoNewVReg = newValue := by
    rw [hmask_new_preserve]
    exact hpre_new
  obtain ⟨js_shifted_mask, hshift_mask_sail, hshift_mask_mask,
      hshift_mask_shift, hshift_mask_dword, hshift_mask_old,
      hshift_mask_new_preserve, hshift_mask_tail⟩ :=
    amo_word_shift_mask_prefix_run js_mask32 js.sail shift64 dword old
      hmask_sail hmask_mask hmask_shift hmask_dword hmask_old
  have hshift_mask_new :
      js_shifted_mask.vregs JoltISA.amoNewVReg = newValue := by
    rw [hshift_mask_new_preserve]
    exact hmask_new
  obtain ⟨js_shifted_new, hshift_new_sail, hshift_new_shift,
      hshift_new_mask, hshift_new_dword, hshift_new_old,
      hshift_new_tail⟩ :=
    amo_word_shift_new_vreg_prefix_run JoltISA.amoNewVReg
      js_shifted_mask js.sail
      newValue shift64 shiftedMask dword old hshift_mask_sail
      hshift_mask_new hshift_mask_mask hshift_mask_shift
      hshift_mask_dword hshift_mask_old (by decide)
  obtain ⟨js_splice, hsplice_sail, hsplice_dword, hsplice_old,
      hsplice_tail⟩ :=
    amo_word_splice_block_run js_shifted_new js.sail addr newValue old hsetup
      hshift_new_sail hshift_new_dword hshift_new_shift hshift_new_mask
      hshift_new_old
  obtain ⟨js_store_base, hstore_base_sail, hstore_base, hstore_base_dword,
      hstore_base_old, hstore_base_tail⟩ :=
    amo_word_store_base_prefix_run rs1 js_splice js.sail addr dwordNew old
      hsplice_sail hrs1 hsplice_dword hsplice_old
  obtain ⟨js_store, hstore_sail, hstore_old, hstore_tail⟩ :=
    amo_word_sd_spliced_dword_run js_store_base js.sail addr dwordNew old
      hcfg h_mem h_no_ovf hstore_base_sail hstore_base hstore_base_dword
      hstore_base_old
  have hword_store :
      state_after_dword_store js.sail (amoWordBase addr) dwordNew =
        state_after_word_store js.sail addr wordResult :=
    amo_word_spliced_dword_store_eq_word_store
      js.sail addr newValue hsetup h_mem.jolt_bytes
  have hstore_sail_word :
      js_store.sail = state_after_word_store js.sail addr wordResult := by
    rw [hstore_sail, hword_store]
  have hold_writeback :
      sign_extend (m := 64)
        ((Sail.BitVec.extractLsb old 31 0) : BitVec 32) =
      sign_extend (m := 64) (loaded_word_at js.sail addr) :=
    amo_word_shifted_old_sign_extend_eq_loaded_word js.sail addr h_align
  obtain ⟨jsf, hwriteback_sail, hwriteback_tail⟩ :=
    amo_word_writeback_old_run rd js_store js.sail addr wordResult old
      hstore_sail_word hstore_old hold_writeback
  refine ⟨jsf, ?_, ?_⟩
  · unfold JoltISA.amoPost64Program JoltISA.amoPost64ProgramWithScratch
    rw [hmask_tail]
    rw [hshift_mask_tail]
    rw [hshift_new_tail]
    rw [hsplice_tail]
    rw [hstore_base_tail]
    rw [hstore_tail]
    rw [hwriteback_tail]
    rfl
  · exact hwriteback_sail

/-- Shared aligned concrete execution for word AMO binop expansions.

The common prelude extracts the old word, the caller supplies the single pure
middle instruction, and the shared postlude splices the low word of the middle
result back to memory. -/
theorem amo_word_binop_program_concrete_aligned
    (op : amoop)
    (binop : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr result64 : BitVec 64) (result : BitVec 32)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (h_mem : AmoMemoryContext op 4 (amoWordBase addr) addr js.sail)
    (h_align : addr &&& (3 : BitVec 64) = 0)
    (hresult : (Sail.BitVec.extractLsb result64 31 0 : BitVec 32) = result)
    (hmiddle :
      ∀ js_pre : SailJoltState,
        js_pre.sail = js.sail →
        js_pre.vregs JoltISA.amoDwordVReg =
          loaded_dword_at js.sail (amoWordBase addr) →
        js_pre.vregs JoltISA.amoShiftVReg =
          shift_bits_left addr (3 : BitVec 6) →
        js_pre.vregs JoltISA.amoOldVReg =
          shift_bits_right
            (loaded_dword_at js.sail (amoWordBase addr))
            (Sail.BitVec.extractLsb
              (shift_bits_left addr (3 : BitVec 6)) 5 0) →
        ∃ js_afterMiddle : SailJoltState,
          AmoWordMiddleStep
            (binop (.vreg JoltISA.amoNewVReg)
              (.vreg JoltISA.amoOldVReg) (.xreg rs2))
            (shift_bits_right
              (loaded_dword_at js.sail (amoWordBase addr))
              (Sail.BitVec.extractLsb
                (shift_bits_left addr (3 : BitVec 6)) 5 0))
            (loaded_dword_at js.sail (amoWordBase addr))
            (shift_bits_left addr (3 : BitVec 6))
            result64 js_pre js_afterMiddle) :
    ∃ jsf : SailJoltState,
      (JoltISA.execProgram
        (JoltISA.amoWordBinopProgram binop rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail = amoWordFinalSailState rd js.sail addr result := by
  let post : JoltISA.Program :=
    .instr (binop (.vreg JoltISA.amoNewVReg)
      (.vreg JoltISA.amoOldVReg) (.xreg rs2)) <|
    JoltISA.amoPost64Program rs1 rd (.vreg JoltISA.amoNewVReg)
      JoltISA.amoDwordVReg JoltISA.amoShiftVReg
      JoltISA.amoMaskVReg JoltISA.amoOldVReg
  have h_no_ovf := amo_word_base_no_ovf addr
  obtain ⟨js_pre, hpre_run, hpre_sail, hpre_dword, hpre_shift, hpre_old⟩ :=
    amo_word_pre64_aligned_run post rs1 js hcfg addr hrs1 h_mem
      h_no_ovf h_align
  obtain ⟨js_afterMiddle, hmiddle_step⟩ :=
    hmiddle js_pre hpre_sail hpre_dword hpre_shift hpre_old
  have hmiddle_sail : js_afterMiddle.sail = js.sail := by
    rw [hmiddle_step.sail, hpre_sail]
  obtain ⟨jsf, hpost_run, hpost_sail⟩ :=
    amo_word_post64_vreg_aligned_run rs1 rd
      js js_afterMiddle hcfg addr result64 hrs1 h_mem h_no_ovf h_align
      hmiddle_sail hmiddle_step.result_vreg
      hmiddle_step.dword_vreg hmiddle_step.shift_vreg hmiddle_step.old_vreg
  refine ⟨jsf, ?_, ?_⟩
  · unfold JoltISA.amoWordBinopProgram
    rw [hpre_run]
    rw [JoltISA.execProgram_instr_run_retire
      _ _ js_pre js_afterMiddle hmiddle_step.run]
    exact hpost_run
  · rw [hpost_sail, hresult]

/-- The word-select middle starts by extending `rs2` and the extracted old word
into the two comparison scratch registers. -/
def amoWordSelectExtendProgram
    (extend : JoltISA.Dst → JoltISA.Src → JoltISA.Instr)
    (rs2 : regidx) (tail : JoltISA.Program) : JoltISA.Program :=
  .instr (extend (.vreg JoltISA.amoNewVReg) (.xreg rs2)) <|
  .instr (extend (.vreg JoltISA.amoMaskVReg) (.vreg JoltISA.amoOldVReg)) <|
  tail

/-- The word-select comparison overwrites `amoMaskVReg` with the selected
comparison flag. -/
def amoWordSelectCompareProgram
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src) (tail : JoltISA.Program) :
    JoltISA.Program :=
  .instr (cmpInstr (.vreg JoltISA.amoMaskVReg) cmpLhs cmpRhs) tail

/-- The word-select tail computes `(rs2 - old) * flag + old` into
`amoNewVReg`. -/
def amoWordSelectTailProgram
    (rs2 : regidx) (tail : JoltISA.Program) : JoltISA.Program :=
  .instr (.SUB (.vreg JoltISA.amoNewVReg)
    (.xreg rs2) (.vreg JoltISA.amoOldVReg)) <|
  .instr (.MUL (.vreg JoltISA.amoNewVReg)
    (.vreg JoltISA.amoNewVReg) (.vreg JoltISA.amoMaskVReg)) <|
  .instr (.ADD (.vreg JoltISA.amoNewVReg)
    (.vreg JoltISA.amoNewVReg) (.vreg JoltISA.amoOldVReg)) <|
  tail

/-- The word-select middle is the extension phase, comparison phase, and
select-tail phase composed around an arbitrary continuation. -/
def amoWordSelectMiddleProgram
    (extend : JoltISA.Dst → JoltISA.Src → JoltISA.Instr)
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src) (rs2 : regidx)
    (tail : JoltISA.Program) : JoltISA.Program :=
  amoWordSelectExtendProgram extend rs2 <|
  amoWordSelectCompareProgram cmpInstr cmpLhs cmpRhs <|
  amoWordSelectTailProgram rs2 tail

/-- Shape produced by the extension phase of a word select AMO.

The phase writes the extended `rs2` word into `amoNewVReg`, the extended old
word into `amoMaskVReg`, and preserves the prelude values needed later. -/
structure AmoWordSelectExtendStep
    (extend : JoltISA.Dst → JoltISA.Src → JoltISA.Instr)
    (rs2 : regidx)
    (old dword shift rs2Ext oldExt : BitVec 64)
    (js_before js_after : SailJoltState) : Prop where
  run :
    ∀ tail,
      (JoltISA.execProgram
        (amoWordSelectExtendProgram extend rs2 tail)).run js_before =
        (JoltISA.execProgram tail).run js_after
  sail : js_after.sail = js_before.sail
  rs2_ext_vreg : js_after.vregs JoltISA.amoNewVReg = rs2Ext
  old_ext_vreg : js_after.vregs JoltISA.amoMaskVReg = oldExt
  old_vreg : js_after.vregs JoltISA.amoOldVReg = old
  dword_vreg : js_after.vregs JoltISA.amoDwordVReg = dword
  shift_vreg : js_after.vregs JoltISA.amoShiftVReg = shift

/-- Shape produced by the comparison phase of a word select AMO.

The phase overwrites `amoMaskVReg` with the comparison flag and preserves the
prelude values needed by the select tail and postlude. -/
structure AmoWordSelectCompareStep
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src)
    (old dword shift flag : BitVec 64)
    (js_before js_after : SailJoltState) : Prop where
  run :
    ∀ tail,
      (JoltISA.execProgram
        (amoWordSelectCompareProgram cmpInstr cmpLhs cmpRhs tail)).run
          js_before =
        (JoltISA.execProgram tail).run js_after
  sail : js_after.sail = js_before.sail
  flag_vreg : js_after.vregs JoltISA.amoMaskVReg = flag
  old_vreg : js_after.vregs JoltISA.amoOldVReg = old
  dword_vreg : js_after.vregs JoltISA.amoDwordVReg = dword
  shift_vreg : js_after.vregs JoltISA.amoShiftVReg = shift

/-- Shape produced by the select-tail phase of a word select AMO. -/
structure AmoWordSelectTailStep
    (rs2 : regidx) (old dword shift result : BitVec 64)
    (js_before js_after : SailJoltState) : Prop where
  run :
    ∀ tail,
      (JoltISA.execProgram
        (amoWordSelectTailProgram rs2 tail)).run js_before =
        (JoltISA.execProgram tail).run js_after
  sail : js_after.sail = js_before.sail
  result_vreg : js_after.vregs JoltISA.amoNewVReg = result
  old_vreg : js_after.vregs JoltISA.amoOldVReg = old
  dword_vreg : js_after.vregs JoltISA.amoDwordVReg = dword
  shift_vreg : js_after.vregs JoltISA.amoShiftVReg = shift

/-- Shape produced by the full word-select middle block. -/
structure AmoWordSelectMiddleStep
    (extend : JoltISA.Dst → JoltISA.Src → JoltISA.Instr)
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src) (rs2 : regidx)
    (old dword shift result : BitVec 64)
    (js_before js_after : SailJoltState) : Prop where
  run :
    ∀ tail,
      (JoltISA.execProgram
        (amoWordSelectMiddleProgram extend cmpInstr cmpLhs cmpRhs rs2
          tail)).run js_before =
        (JoltISA.execProgram tail).run js_after
  sail : js_after.sail = js_before.sail
  result_vreg : js_after.vregs JoltISA.amoNewVReg = result
  old_vreg : js_after.vregs JoltISA.amoOldVReg = old
  dword_vreg : js_after.vregs JoltISA.amoDwordVReg = dword
  shift_vreg : js_after.vregs JoltISA.amoShiftVReg = shift

/-- `VirtualZeroExtendWord` from a virtual source to a virtual destination. -/
theorem amo_word_virtual_zero_extend_word_run_vreg_vreg
    (vd vs : JoltISA.VReg) (js : SailJoltState)
    (hvd : WritableVReg vd) :
    (JoltISA.execInstr (.VirtualZeroExtendWord (.vreg vd) (.vreg vs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then
              zero_extend (m := 64)
                (Sail.BitVec.extractLsb (js.vregs vs) 31 0)
            else js.vregs r } := by
  unfold WritableVReg at hvd
  unfold JoltISA.execInstr JoltISA.readSrc JoltISA.writeDst
    readVReg writeVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    hvd, ↓reduceIte, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `SLT` on two virtual sources writes the signed less-than flag to a virtual
destination. -/
theorem amo_word_slt_run_vreg_vreg_vreg
    (vd lhs rhs : JoltISA.VReg) (js : SailJoltState)
    (hvd : WritableVReg vd) :
    (JoltISA.execInstr (.SLT (.vreg vd) (.vreg lhs) (.vreg rhs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then
              zero_extend (m := 64)
                (bool_to_bit (zopz0zI_s (js.vregs lhs) (js.vregs rhs)))
            else js.vregs r } := by
  unfold WritableVReg at hvd
  unfold JoltISA.execInstr JoltISA.readSrc JoltISA.writeDst
    readVReg writeVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    hvd, ↓reduceIte, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `SLTU` on two virtual sources writes the unsigned less-than flag to a
virtual destination. -/
theorem amo_word_sltu_run_vreg_vreg_vreg
    (vd lhs rhs : JoltISA.VReg) (js : SailJoltState)
    (hvd : WritableVReg vd) :
    (JoltISA.execInstr (.SLTU (.vreg vd) (.vreg lhs) (.vreg rhs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then jolt_sltu_value (js.vregs lhs) (js.vregs rhs)
            else js.vregs r } := by
  unfold WritableVReg at hvd
  unfold JoltISA.execInstr JoltISA.readSrc JoltISA.writeDst
    readVReg writeVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    hvd, ↓reduceIte, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- The signed word-select extension phase prepares signed comparison
operands for `AMOMIN.W` and `AMOMAX.W`. -/
theorem amo_word_signed_select_extend_phase_run
    (rs2 : regidx) (js : SailJoltState)
    (rs2Val old dword shift : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hold : js.vregs JoltISA.amoOldVReg = old)
    (hdword : js.vregs JoltISA.amoDwordVReg = dword)
    (hshift : js.vregs JoltISA.amoShiftVReg = shift) :
    ∃ js_afterExt : SailJoltState,
      AmoWordSelectExtendStep
        (fun dst src => .VirtualSignExtendWord dst src) rs2
        old dword shift
        (sign_extend (m := 64)
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
        (sign_extend (m := 64)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
        js js_afterExt := by
  let rs2Ext : BitVec 64 :=
    sign_extend (m := 64)
      (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
  let oldExt : BitVec 64 :=
    sign_extend (m := 64)
      (Sail.BitVec.extractLsb old 31 0 : BitVec 32)
  let js_afterRs2 : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.amoNewVReg then rs2Ext else js.vregs r }
  let js_afterExt : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.amoMaskVReg then oldExt else js_afterRs2.vregs r }
  have hrs2_run :
      (JoltISA.execInstr
        (.VirtualSignExtendWord (.vreg JoltISA.amoNewVReg)
          (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js_afterRs2 := by
    exact
      JoltISA.virtual_sign_extend_word_run_vreg_xreg
        JoltISA.amoNewVReg rs2 js rs2Val hrs2
        (by unfold WritableVReg; decide)
  have hold_afterRs2 :
      js_afterRs2.vregs JoltISA.amoOldVReg = old := by
    change
      (if JoltISA.amoOldVReg = JoltISA.amoNewVReg then rs2Ext
        else js.vregs JoltISA.amoOldVReg) = old
    rw [if_neg (by decide), hold]
  have hold_run :
      (JoltISA.execInstr
        (.VirtualSignExtendWord (.vreg JoltISA.amoMaskVReg)
          (.vreg JoltISA.amoOldVReg))).run js_afterRs2 =
        .ok RETIRE_SUCCESS js_afterExt := by
    rw [JoltISA.virtual_sign_extend_word_run_vreg_vreg
      JoltISA.amoMaskVReg JoltISA.amoOldVReg js_afterRs2
      (by unfold WritableVReg; decide)]
    unfold js_afterExt oldExt
    rw [hold_afterRs2]
  refine ⟨js_afterExt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tail
    unfold amoWordSelectExtendProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterRs2 hrs2_run]
    rw [JoltISA.execProgram_instr_run_retire
      _ _ js_afterRs2 js_afterExt hold_run]
  · rfl
  · change
      (if JoltISA.amoNewVReg = JoltISA.amoMaskVReg then oldExt
        else js_afterRs2.vregs JoltISA.amoNewVReg) = rs2Ext
    rw [if_neg (by decide)]
    change
      (if JoltISA.amoNewVReg = JoltISA.amoNewVReg then rs2Ext
        else js.vregs JoltISA.amoNewVReg) = rs2Ext
    rw [if_pos rfl]
  · change
      (if JoltISA.amoMaskVReg = JoltISA.amoMaskVReg then oldExt
        else js_afterRs2.vregs JoltISA.amoMaskVReg) = oldExt
    rw [if_pos rfl]
  · change
      (if JoltISA.amoOldVReg = JoltISA.amoMaskVReg then oldExt
        else js_afterRs2.vregs JoltISA.amoOldVReg) = old
    rw [if_neg (by decide), hold_afterRs2]
  · change
      (if JoltISA.amoDwordVReg = JoltISA.amoMaskVReg then oldExt
        else js_afterRs2.vregs JoltISA.amoDwordVReg) = dword
    rw [if_neg (by decide)]
    change
      (if JoltISA.amoDwordVReg = JoltISA.amoNewVReg then rs2Ext
        else js.vregs JoltISA.amoDwordVReg) = dword
    rw [if_neg (by decide), hdword]
  · change
      (if JoltISA.amoShiftVReg = JoltISA.amoMaskVReg then oldExt
        else js_afterRs2.vregs JoltISA.amoShiftVReg) = shift
    rw [if_neg (by decide)]
    change
      (if JoltISA.amoShiftVReg = JoltISA.amoNewVReg then rs2Ext
        else js.vregs JoltISA.amoShiftVReg) = shift
    rw [if_neg (by decide), hshift]

/-- The unsigned word-select extension phase prepares unsigned comparison
operands for `AMOMINU.W` and `AMOMAXU.W`. -/
theorem amo_word_unsigned_select_extend_phase_run
    (rs2 : regidx) (js : SailJoltState)
    (rs2Val old dword shift : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hold : js.vregs JoltISA.amoOldVReg = old)
    (hdword : js.vregs JoltISA.amoDwordVReg = dword)
    (hshift : js.vregs JoltISA.amoShiftVReg = shift) :
    ∃ js_afterExt : SailJoltState,
      AmoWordSelectExtendStep
        (fun dst src => .VirtualZeroExtendWord dst src) rs2
        old dword shift
        (zero_extend (m := 64)
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
        (zero_extend (m := 64)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
        js js_afterExt := by
  let rs2Ext : BitVec 64 :=
    zero_extend (m := 64)
      (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
  let oldExt : BitVec 64 :=
    zero_extend (m := 64)
      (Sail.BitVec.extractLsb old 31 0 : BitVec 32)
  let js_afterRs2 : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.amoNewVReg then rs2Ext else js.vregs r }
  let js_afterExt : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.amoMaskVReg then oldExt else js_afterRs2.vregs r }
  have hrs2_run :
      (JoltISA.execInstr
        (.VirtualZeroExtendWord (.vreg JoltISA.amoNewVReg)
          (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js_afterRs2 := by
    exact
      JoltISA.virtual_zero_extend_word_run_vreg_xreg
        JoltISA.amoNewVReg rs2 js rs2Val hrs2
        (by unfold WritableVReg; decide)
  have hold_afterRs2 :
      js_afterRs2.vregs JoltISA.amoOldVReg = old := by
    change
      (if JoltISA.amoOldVReg = JoltISA.amoNewVReg then rs2Ext
        else js.vregs JoltISA.amoOldVReg) = old
    rw [if_neg (by decide), hold]
  have hold_run :
      (JoltISA.execInstr
        (.VirtualZeroExtendWord (.vreg JoltISA.amoMaskVReg)
          (.vreg JoltISA.amoOldVReg))).run js_afterRs2 =
        .ok RETIRE_SUCCESS js_afterExt := by
    rw [amo_word_virtual_zero_extend_word_run_vreg_vreg
      JoltISA.amoMaskVReg JoltISA.amoOldVReg js_afterRs2
      (by unfold WritableVReg; decide)]
    unfold js_afterExt oldExt
    rw [hold_afterRs2]
  refine ⟨js_afterExt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tail
    unfold amoWordSelectExtendProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterRs2 hrs2_run]
    rw [JoltISA.execProgram_instr_run_retire
      _ _ js_afterRs2 js_afterExt hold_run]
  · rfl
  · change
      (if JoltISA.amoNewVReg = JoltISA.amoMaskVReg then oldExt
        else js_afterRs2.vregs JoltISA.amoNewVReg) = rs2Ext
    rw [if_neg (by decide)]
    change
      (if JoltISA.amoNewVReg = JoltISA.amoNewVReg then rs2Ext
        else js.vregs JoltISA.amoNewVReg) = rs2Ext
    rw [if_pos rfl]
  · change
      (if JoltISA.amoMaskVReg = JoltISA.amoMaskVReg then oldExt
        else js_afterRs2.vregs JoltISA.amoMaskVReg) = oldExt
    rw [if_pos rfl]
  · change
      (if JoltISA.amoOldVReg = JoltISA.amoMaskVReg then oldExt
        else js_afterRs2.vregs JoltISA.amoOldVReg) = old
    rw [if_neg (by decide), hold_afterRs2]
  · change
      (if JoltISA.amoDwordVReg = JoltISA.amoMaskVReg then oldExt
        else js_afterRs2.vregs JoltISA.amoDwordVReg) = dword
    rw [if_neg (by decide)]
    change
      (if JoltISA.amoDwordVReg = JoltISA.amoNewVReg then rs2Ext
        else js.vregs JoltISA.amoDwordVReg) = dword
    rw [if_neg (by decide), hdword]
  · change
      (if JoltISA.amoShiftVReg = JoltISA.amoMaskVReg then oldExt
        else js_afterRs2.vregs JoltISA.amoShiftVReg) = shift
    rw [if_neg (by decide)]
    change
      (if JoltISA.amoShiftVReg = JoltISA.amoNewVReg then rs2Ext
        else js.vregs JoltISA.amoShiftVReg) = shift
    rw [if_neg (by decide), hshift]

/-- A signed word-select comparison phase writes the signed less-than flag
between two prepared virtual operands. -/
theorem amo_word_slt_compare_phase_run_vreg_vreg
    (lhs rhs : JoltISA.VReg) (js : SailJoltState)
    (x y old dword shift : BitVec 64)
    (hlhs : js.vregs lhs = x)
    (hrhs : js.vregs rhs = y)
    (hold : js.vregs JoltISA.amoOldVReg = old)
    (hdword : js.vregs JoltISA.amoDwordVReg = dword)
    (hshift : js.vregs JoltISA.amoShiftVReg = shift) :
    ∃ js_afterCmp : SailJoltState,
      AmoWordSelectCompareStep
        (fun dst lhs rhs => .SLT dst lhs rhs) (.vreg lhs) (.vreg rhs)
        old dword shift
        (zero_extend (m := 64) (bool_to_bit (zopz0zI_s x y)))
        js js_afterCmp := by
  let flag : BitVec 64 :=
    zero_extend (m := 64) (bool_to_bit (zopz0zI_s x y))
  let js_afterCmp : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.amoMaskVReg then flag else js.vregs r }
  have hcmp_run :
      (JoltISA.execInstr
        (.SLT (.vreg JoltISA.amoMaskVReg) (.vreg lhs) (.vreg rhs))).run
          js =
        .ok RETIRE_SUCCESS js_afterCmp := by
    rw [amo_word_slt_run_vreg_vreg_vreg JoltISA.amoMaskVReg lhs rhs js
      (by unfold WritableVReg; decide)]
    unfold js_afterCmp flag
    rw [hlhs, hrhs]
  refine ⟨js_afterCmp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tail
    unfold amoWordSelectCompareProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterCmp hcmp_run]
  · rfl
  · change
      (if JoltISA.amoMaskVReg = JoltISA.amoMaskVReg then flag
        else js.vregs JoltISA.amoMaskVReg) =
      zero_extend (m := 64) (bool_to_bit (zopz0zI_s x y))
    rw [if_pos rfl]
  · change
      (if JoltISA.amoOldVReg = JoltISA.amoMaskVReg then flag
        else js.vregs JoltISA.amoOldVReg) = old
    rw [if_neg (by decide), hold]
  · change
      (if JoltISA.amoDwordVReg = JoltISA.amoMaskVReg then flag
        else js.vregs JoltISA.amoDwordVReg) = dword
    rw [if_neg (by decide), hdword]
  · change
      (if JoltISA.amoShiftVReg = JoltISA.amoMaskVReg then flag
        else js.vregs JoltISA.amoShiftVReg) = shift
    rw [if_neg (by decide), hshift]

/-- An unsigned word-select comparison phase writes the unsigned less-than flag
between two prepared virtual operands. -/
theorem amo_word_sltu_compare_phase_run_vreg_vreg
    (lhs rhs : JoltISA.VReg) (js : SailJoltState)
    (x y old dword shift : BitVec 64)
    (hlhs : js.vregs lhs = x)
    (hrhs : js.vregs rhs = y)
    (hold : js.vregs JoltISA.amoOldVReg = old)
    (hdword : js.vregs JoltISA.amoDwordVReg = dword)
    (hshift : js.vregs JoltISA.amoShiftVReg = shift) :
    ∃ js_afterCmp : SailJoltState,
      AmoWordSelectCompareStep
        (fun dst lhs rhs => .SLTU dst lhs rhs) (.vreg lhs) (.vreg rhs)
        old dword shift (jolt_sltu_value x y) js js_afterCmp := by
  let flag : BitVec 64 := jolt_sltu_value x y
  let js_afterCmp : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.amoMaskVReg then flag else js.vregs r }
  have hcmp_run :
      (JoltISA.execInstr
        (.SLTU (.vreg JoltISA.amoMaskVReg) (.vreg lhs) (.vreg rhs))).run
          js =
        .ok RETIRE_SUCCESS js_afterCmp := by
    rw [amo_word_sltu_run_vreg_vreg_vreg JoltISA.amoMaskVReg lhs rhs js
      (by unfold WritableVReg; decide)]
    unfold js_afterCmp flag
    rw [hlhs, hrhs]
  refine ⟨js_afterCmp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tail
    unfold amoWordSelectCompareProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterCmp hcmp_run]
  · rfl
  · change
      (if JoltISA.amoMaskVReg = JoltISA.amoMaskVReg then flag
        else js.vregs JoltISA.amoMaskVReg) = jolt_sltu_value x y
    rw [if_pos rfl]
  · change
      (if JoltISA.amoOldVReg = JoltISA.amoMaskVReg then flag
        else js.vregs JoltISA.amoOldVReg) = old
    rw [if_neg (by decide), hold]
  · change
      (if JoltISA.amoDwordVReg = JoltISA.amoMaskVReg then flag
        else js.vregs JoltISA.amoDwordVReg) = dword
    rw [if_neg (by decide), hdword]
  · change
      (if JoltISA.amoShiftVReg = JoltISA.amoMaskVReg then flag
        else js.vregs JoltISA.amoShiftVReg) = shift
    rw [if_neg (by decide), hshift]

/-- The word-select tail turns the comparison flag into the selected new value
while preserving the prelude registers needed by the postlude. -/
theorem amo_word_select_tail_phase_run
    (rs2 : regidx) (js : SailJoltState)
    (rs2Val old flag dword shift : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hold : js.vregs JoltISA.amoOldVReg = old)
    (hflag : js.vregs JoltISA.amoMaskVReg = flag)
    (hdword : js.vregs JoltISA.amoDwordVReg = dword)
    (hshift : js.vregs JoltISA.amoShiftVReg = shift) :
    ∃ js_afterTail : SailJoltState,
      AmoWordSelectTailStep rs2 old dword shift
        ((rs2Val - old) * flag + old) js js_afterTail := by
  let delta : BitVec 64 := rs2Val - old
  let scaled : BitVec 64 := delta * flag
  let js_afterSub : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.amoNewVReg then delta else js.vregs r }
  let js_afterMul : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.amoNewVReg then scaled else js_afterSub.vregs r }
  let js_afterAdd : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.amoNewVReg then scaled + old else js_afterMul.vregs r }
  have hsub_new : js_afterSub.vregs JoltISA.amoNewVReg = delta := by
    change
      (if JoltISA.amoNewVReg = JoltISA.amoNewVReg then delta
        else js.vregs JoltISA.amoNewVReg) = delta
    rw [if_pos rfl]
  have hsub_flag : js_afterSub.vregs JoltISA.amoMaskVReg = flag := by
    change
      (if JoltISA.amoMaskVReg = JoltISA.amoNewVReg then delta
        else js.vregs JoltISA.amoMaskVReg) = flag
    rw [if_neg (by decide), hflag]
  have hsub_old : js_afterSub.vregs JoltISA.amoOldVReg = old := by
    change
      (if JoltISA.amoOldVReg = JoltISA.amoNewVReg then delta
        else js.vregs JoltISA.amoOldVReg) = old
    rw [if_neg (by decide), hold]
  have hsub_dword : js_afterSub.vregs JoltISA.amoDwordVReg = dword := by
    change
      (if JoltISA.amoDwordVReg = JoltISA.amoNewVReg then delta
        else js.vregs JoltISA.amoDwordVReg) = dword
    rw [if_neg (by decide), hdword]
  have hsub_shift : js_afterSub.vregs JoltISA.amoShiftVReg = shift := by
    change
      (if JoltISA.amoShiftVReg = JoltISA.amoNewVReg then delta
        else js.vregs JoltISA.amoShiftVReg) = shift
    rw [if_neg (by decide), hshift]
  have hsub_run :
      (JoltISA.execInstr
        (.SUB (.vreg JoltISA.amoNewVReg)
          (.xreg rs2) (.vreg JoltISA.amoOldVReg))).run js =
        .ok RETIRE_SUCCESS js_afterSub := by
    rw [JoltISA.sub_run_vreg_xreg_vreg
      JoltISA.amoNewVReg rs2 JoltISA.amoOldVReg js rs2Val hrs2
      (by unfold WritableVReg; decide)]
    unfold js_afterSub delta
    rw [hold]
  have hmul_new : js_afterMul.vregs JoltISA.amoNewVReg = scaled := by
    change
      (if JoltISA.amoNewVReg = JoltISA.amoNewVReg then scaled
        else js_afterSub.vregs JoltISA.amoNewVReg) = scaled
    rw [if_pos rfl]
  have hmul_old : js_afterMul.vregs JoltISA.amoOldVReg = old := by
    change
      (if JoltISA.amoOldVReg = JoltISA.amoNewVReg then scaled
        else js_afterSub.vregs JoltISA.amoOldVReg) = old
    rw [if_neg (by decide), hsub_old]
  have hmul_dword : js_afterMul.vregs JoltISA.amoDwordVReg = dword := by
    change
      (if JoltISA.amoDwordVReg = JoltISA.amoNewVReg then scaled
        else js_afterSub.vregs JoltISA.amoDwordVReg) = dword
    rw [if_neg (by decide), hsub_dword]
  have hmul_shift : js_afterMul.vregs JoltISA.amoShiftVReg = shift := by
    change
      (if JoltISA.amoShiftVReg = JoltISA.amoNewVReg then scaled
        else js_afterSub.vregs JoltISA.amoShiftVReg) = shift
    rw [if_neg (by decide), hsub_shift]
  have hmul_run :
      (JoltISA.execInstr
        (.MUL (.vreg JoltISA.amoNewVReg)
          (.vreg JoltISA.amoNewVReg)
          (.vreg JoltISA.amoMaskVReg))).run js_afterSub =
        .ok RETIRE_SUCCESS js_afterMul := by
    rw [JoltISA.mul_run_vreg_vreg_vreg
      JoltISA.amoNewVReg JoltISA.amoNewVReg JoltISA.amoMaskVReg
      js_afterSub (by unfold WritableVReg; decide)]
    unfold js_afterMul scaled
    rw [hsub_new, hsub_flag]
  have hadd_result :
      js_afterAdd.vregs JoltISA.amoNewVReg =
        (rs2Val - old) * flag + old := by
    change
      (if JoltISA.amoNewVReg = JoltISA.amoNewVReg then scaled + old
        else js_afterMul.vregs JoltISA.amoNewVReg) =
      (rs2Val - old) * flag + old
    rw [if_pos rfl]
  have hadd_old : js_afterAdd.vregs JoltISA.amoOldVReg = old := by
    change
      (if JoltISA.amoOldVReg = JoltISA.amoNewVReg then scaled + old
        else js_afterMul.vregs JoltISA.amoOldVReg) = old
    rw [if_neg (by decide), hmul_old]
  have hadd_dword : js_afterAdd.vregs JoltISA.amoDwordVReg = dword := by
    change
      (if JoltISA.amoDwordVReg = JoltISA.amoNewVReg then scaled + old
        else js_afterMul.vregs JoltISA.amoDwordVReg) = dword
    rw [if_neg (by decide), hmul_dword]
  have hadd_shift : js_afterAdd.vregs JoltISA.amoShiftVReg = shift := by
    change
      (if JoltISA.amoShiftVReg = JoltISA.amoNewVReg then scaled + old
        else js_afterMul.vregs JoltISA.amoShiftVReg) = shift
    rw [if_neg (by decide), hmul_shift]
  have hadd_run :
      (JoltISA.execInstr
        (.ADD (.vreg JoltISA.amoNewVReg)
          (.vreg JoltISA.amoNewVReg)
          (.vreg JoltISA.amoOldVReg))).run js_afterMul =
        .ok RETIRE_SUCCESS js_afterAdd := by
    rw [JoltISA.add_run_vreg_vreg_vreg
      JoltISA.amoNewVReg JoltISA.amoNewVReg JoltISA.amoOldVReg
      js_afterMul (by unfold WritableVReg; decide)]
    unfold js_afterAdd
    rw [hmul_new, hmul_old]
  refine ⟨js_afterAdd, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tail
    unfold amoWordSelectTailProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterSub hsub_run]
    rw [JoltISA.execProgram_instr_run_retire
      _ _ js_afterSub js_afterMul hmul_run]
    rw [JoltISA.execProgram_instr_run_retire
      _ _ js_afterMul js_afterAdd hadd_run]
  · rfl
  · exact hadd_result
  · exact hadd_old
  · exact hadd_dword
  · exact hadd_shift

/-- Sign-extending a 32-bit word to an RV64 scratch value preserves its signed
integer interpretation. -/
theorem amo_word_toInt_signExtend32_64 (x : BitVec 32) :
    (sign_extend (m := 64) x).toInt = x.toInt := by
  unfold sign_extend Sail.BitVec.signExtend
  rw [BitVec.toInt_signExtend]
  have hlo : -(2^31 : Int) ≤ x.toInt := by
    have h := @BitVec.le_toInt 32 x
    exact h
  have hhi : x.toInt < 2^31 := by
    have h := @BitVec.toInt_lt 32 x
    exact h
  apply Int.bmod_eq_of_le
  · show -(((2^32 : Nat) : Int) / 2) ≤ x.toInt
    have h : (((2^32 : Nat) : Int) / 2) = (2^31 : Int) := by decide
    rw [h]
    exact hlo
  · show x.toInt < ((((2^32 : Nat) : Int) + 1) / 2)
    have h : ((((2^32 : Nat) : Int) + 1) / 2) = (2^31 : Int) := by decide
    rw [h]
    exact hhi

/-- Zero-extending a 32-bit word to an RV64 scratch value preserves its natural
bitvector value. -/
theorem amo_word_toNat_zeroExtend32_64 (x : BitVec 32) :
    (zero_extend (m := 64) x).toNat = x.toNat := by
  unfold zero_extend Sail.BitVec.zeroExtend
  rw [BitVec.toNat_setWidth]
  apply Nat.mod_eq_of_lt
  have hx := x.isLt
  omega

/-- Zero-extending a 32-bit word to an RV64 scratch value preserves Sail's
unsigned integer interpretation. -/
theorem amo_word_toNatInt_zeroExtend32_64 (x : BitVec 32) :
    BitVec.toNatInt (zero_extend (m := 64) x) = BitVec.toNatInt x := by
  unfold BitVec.toNatInt
  rw [amo_word_toNat_zeroExtend32_64 x]

/-- Signed comparison is unchanged by sign-extending both low words to RV64
scratch values. -/
theorem amo_word_slt_sext_extract_eq (lhs rhs : BitVec 64) :
    (zopz0zI_s
      (sign_extend (m := 64)
        (Sail.BitVec.extractLsb lhs 31 0 : BitVec 32))
      (sign_extend (m := 64)
        (Sail.BitVec.extractLsb rhs 31 0 : BitVec 32)) : Bool) =
    (zopz0zI_s
      (Sail.BitVec.extractLsb lhs 31 0 : BitVec 32)
      (Sail.BitVec.extractLsb rhs 31 0 : BitVec 32) : Bool) := by
  unfold zopz0zI_s
  rw [amo_word_toInt_signExtend32_64,
    amo_word_toInt_signExtend32_64]

/-- Unsigned comparison is unchanged by zero-extending both low words to RV64
scratch values. -/
theorem amo_word_sltu_zext_extract_eq (lhs rhs : BitVec 64) :
    (zopz0zI_u
      (zero_extend (m := 64)
        (Sail.BitVec.extractLsb lhs 31 0 : BitVec 32))
      (zero_extend (m := 64)
        (Sail.BitVec.extractLsb rhs 31 0 : BitVec 32)) : Bool) =
    (zopz0zI_u
      (Sail.BitVec.extractLsb lhs 31 0 : BitVec 32)
      (Sail.BitVec.extractLsb rhs 31 0 : BitVec 32) : Bool) := by
  unfold zopz0zI_u
  rw [amo_word_toNatInt_zeroExtend32_64,
    amo_word_toNatInt_zeroExtend32_64]

/-- Reversed signed word comparison is Sail's signed word greater-than test. -/
theorem amo_word_slt_sext_reverse_eq_sgt (old new : BitVec 64) :
    (zopz0zI_s
      (sign_extend (m := 64)
        (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
      (sign_extend (m := 64)
        (Sail.BitVec.extractLsb new 31 0 : BitVec 32)) : Bool) =
    (zopz0zK_s
      (Sail.BitVec.extractLsb new 31 0 : BitVec 32)
      (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) := by
  rw [amo_word_slt_sext_extract_eq old new]
  unfold zopz0zI_s zopz0zK_s
  rfl

/-- Reversed unsigned word comparison is Sail's unsigned word greater-than
test. -/
theorem amo_word_sltu_zext_reverse_eq_sgtu (old new : BitVec 64) :
    (zopz0zI_u
      (zero_extend (m := 64)
        (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
      (zero_extend (m := 64)
        (Sail.BitVec.extractLsb new 31 0 : BitVec 32)) : Bool) =
    (zopz0zK_u
      (Sail.BitVec.extractLsb new 31 0 : BitVec 32)
      (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) := by
  rw [amo_word_sltu_zext_extract_eq old new]
  unfold zopz0zI_u zopz0zK_u
  rfl

/-- A word select with a false flag keeps the old scratch value; with a true
flag it selects the new scratch value. -/
theorem amo_word_select_value_of_bool
    (old new : BitVec 64) (flag : Bool) :
    (new - old) * zero_extend (m := 64) (bool_to_bit flag) + old =
      if flag then new else old := by
  cases flag <;>
    unfold bool_to_bit bool_bit_forwards zero_extend Sail.BitVec.zeroExtend <;>
    simp

/-- The signed-min word select arithmetic matches Sail's 32-bit signed branch. -/
theorem amo_word_select_value_of_slt_sext (old new : BitVec 64) :
    (new - old) *
        zero_extend (m := 64)
          (bool_to_bit
            (zopz0zI_s
              (sign_extend (m := 64)
                (Sail.BitVec.extractLsb new 31 0 : BitVec 32))
              (sign_extend (m := 64)
                (Sail.BitVec.extractLsb old 31 0 : BitVec 32)))) +
        old =
      if (zopz0zI_s
          (Sail.BitVec.extractLsb new 31 0 : BitVec 32)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
        new
      else
        old := by
  rw [amo_word_slt_sext_extract_eq new old]
  exact
    amo_word_select_value_of_bool old new
      (zopz0zI_s
        (Sail.BitVec.extractLsb new 31 0 : BitVec 32)
        (Sail.BitVec.extractLsb old 31 0 : BitVec 32))

/-- The signed-max word select arithmetic matches Sail's 32-bit signed branch. -/
theorem amo_word_select_value_of_sgt_sext (old new : BitVec 64) :
    (new - old) *
        zero_extend (m := 64)
          (bool_to_bit
            (zopz0zI_s
              (sign_extend (m := 64)
                (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
              (sign_extend (m := 64)
                (Sail.BitVec.extractLsb new 31 0 : BitVec 32)))) +
        old =
      if (zopz0zK_s
          (Sail.BitVec.extractLsb new 31 0 : BitVec 32)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
        new
      else
        old := by
  rw [amo_word_slt_sext_reverse_eq_sgt old new]
  exact
    amo_word_select_value_of_bool old new
      (zopz0zK_s
        (Sail.BitVec.extractLsb new 31 0 : BitVec 32)
        (Sail.BitVec.extractLsb old 31 0 : BitVec 32))

/-- The unsigned-min word select arithmetic matches Sail's 32-bit unsigned
branch. -/
theorem amo_word_select_value_of_sltu_zext (old new : BitVec 64) :
    (new - old) *
        jolt_sltu_value
          (zero_extend (m := 64)
            (Sail.BitVec.extractLsb new 31 0 : BitVec 32))
          (zero_extend (m := 64)
            (Sail.BitVec.extractLsb old 31 0 : BitVec 32)) +
        old =
      if (zopz0zI_u
          (Sail.BitVec.extractLsb new 31 0 : BitVec 32)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
        new
      else
        old := by
  unfold jolt_sltu_value
  rw [amo_word_sltu_zext_extract_eq new old]
  exact
    amo_word_select_value_of_bool old new
      (zopz0zI_u
        (Sail.BitVec.extractLsb new 31 0 : BitVec 32)
        (Sail.BitVec.extractLsb old 31 0 : BitVec 32))

/-- The unsigned-max word select arithmetic matches Sail's 32-bit unsigned
branch. -/
theorem amo_word_select_value_of_sgtu_zext (old new : BitVec 64) :
    (new - old) *
        jolt_sltu_value
          (zero_extend (m := 64)
            (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
          (zero_extend (m := 64)
            (Sail.BitVec.extractLsb new 31 0 : BitVec 32)) +
        old =
      if (zopz0zK_u
          (Sail.BitVec.extractLsb new 31 0 : BitVec 32)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
        new
      else
        old := by
  unfold jolt_sltu_value
  rw [amo_word_sltu_zext_reverse_eq_sgtu old new]
  exact
    amo_word_select_value_of_bool old new
      (zopz0zK_u
        (Sail.BitVec.extractLsb new 31 0 : BitVec 32)
        (Sail.BitVec.extractLsb old 31 0 : BitVec 32))

/-- Extracting the low word of a selected 64-bit scratch value commutes with
the branch. -/
theorem amo_word_extract_select_result
    (old new : BitVec 64) (flag : Bool) :
    (Sail.BitVec.extractLsb (if flag then new else old) 31 0 :
      BitVec 32) =
      if flag then
        (Sail.BitVec.extractLsb new 31 0 : BitVec 32)
      else
        (Sail.BitVec.extractLsb old 31 0 : BitVec 32) := by
  cases flag
  · rfl
  · rfl

/-- A word-select middle block composes extension, comparison, and the shared
select tail. -/
theorem amo_word_select_middle_phase_run
    (extend : JoltISA.Dst → JoltISA.Src → JoltISA.Instr)
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src) (rs2 : regidx)
    (js : SailJoltState)
    (rs2Val old dword shift rs2Ext oldExt flag result : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hext :
      ∃ js_afterExt : SailJoltState,
        AmoWordSelectExtendStep extend rs2 old dword shift rs2Ext oldExt
          js js_afterExt)
    (hcompare :
      ∀ js_afterExt : SailJoltState,
        AmoWordSelectExtendStep extend rs2 old dword shift rs2Ext oldExt
          js js_afterExt →
        ∃ js_afterCmp : SailJoltState,
          AmoWordSelectCompareStep cmpInstr cmpLhs cmpRhs old dword shift
            flag js_afterExt js_afterCmp)
    (hresult : (rs2Val - old) * flag + old = result) :
    ∃ js_afterMiddle : SailJoltState,
      AmoWordSelectMiddleStep extend cmpInstr cmpLhs cmpRhs rs2
        old dword shift result js js_afterMiddle := by
  obtain ⟨js_afterExt, hext_step⟩ := hext
  obtain ⟨js_afterCmp, hcmp_step⟩ := hcompare js_afterExt hext_step
  have hrs2_afterCmp :
      rX_bits rs2 js_afterCmp.sail = .ok rs2Val js_afterCmp.sail := by
    rw [hcmp_step.sail, hext_step.sail]
    exact hrs2
  obtain ⟨js_afterTail, htail_step⟩ :=
    amo_word_select_tail_phase_run rs2 js_afterCmp rs2Val old flag dword shift
      hrs2_afterCmp hcmp_step.old_vreg hcmp_step.flag_vreg
      hcmp_step.dword_vreg hcmp_step.shift_vreg
  refine ⟨js_afterTail, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tail
    unfold amoWordSelectMiddleProgram
    rw [hext_step.run
      (amoWordSelectCompareProgram cmpInstr cmpLhs cmpRhs
        (amoWordSelectTailProgram rs2 tail))]
    rw [hcmp_step.run (amoWordSelectTailProgram rs2 tail)]
    rw [htail_step.run tail]
  · rw [htail_step.sail, hcmp_step.sail, hext_step.sail]
  · rw [htail_step.result_vreg, hresult]
  · exact htail_step.old_vreg
  · exact htail_step.dword_vreg
  · exact htail_step.shift_vreg

/-- `AMOMIN.W`'s select middle chooses the full `rs2` scratch value exactly
when the low words satisfy signed `<`. -/
theorem amo_word_min_middle_run
    (rs2 : regidx) (js_pre : SailJoltState)
    (rs2Val old dword shift : BitVec 64)
    (hrs2 : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail)
    (hold : js_pre.vregs JoltISA.amoOldVReg = old)
    (hdword : js_pre.vregs JoltISA.amoDwordVReg = dword)
    (hshift : js_pre.vregs JoltISA.amoShiftVReg = shift) :
    ∃ js_afterMiddle : SailJoltState,
      AmoWordSelectMiddleStep
        (fun dst src => .VirtualSignExtendWord dst src)
        (fun dst lhs rhs => .SLT dst lhs rhs)
        (.vreg JoltISA.amoNewVReg) (.vreg JoltISA.amoMaskVReg) rs2
        old dword shift
        (if (zopz0zI_s
            (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
            (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
          rs2Val
        else
          old)
        js_pre js_afterMiddle := by
  exact
    amo_word_select_middle_phase_run
      (fun dst src => .VirtualSignExtendWord dst src)
      (fun dst lhs rhs => .SLT dst lhs rhs)
      (.vreg JoltISA.amoNewVReg) (.vreg JoltISA.amoMaskVReg) rs2
      js_pre rs2Val old dword shift
      (sign_extend (m := 64)
        (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
      (sign_extend (m := 64)
        (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
      (zero_extend (m := 64)
        (bool_to_bit
          (zopz0zI_s
            (sign_extend (m := 64)
              (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
            (sign_extend (m := 64)
              (Sail.BitVec.extractLsb old 31 0 : BitVec 32)))))
      (if (zopz0zI_s
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
        rs2Val
      else
        old)
      hrs2
      (amo_word_signed_select_extend_phase_run rs2 js_pre rs2Val old dword
        shift hrs2 hold hdword hshift)
      (fun js_afterExt hext_step =>
        amo_word_slt_compare_phase_run_vreg_vreg
          JoltISA.amoNewVReg JoltISA.amoMaskVReg js_afterExt
          (sign_extend (m := 64)
            (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
          (sign_extend (m := 64)
            (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
          old dword shift hext_step.rs2_ext_vreg hext_step.old_ext_vreg
          hext_step.old_vreg hext_step.dword_vreg hext_step.shift_vreg)
      (amo_word_select_value_of_slt_sext old rs2Val)

/-- `AMOMAX.W`'s select middle chooses the full `rs2` scratch value exactly
when the low words satisfy signed `>`. -/
theorem amo_word_max_middle_run
    (rs2 : regidx) (js_pre : SailJoltState)
    (rs2Val old dword shift : BitVec 64)
    (hrs2 : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail)
    (hold : js_pre.vregs JoltISA.amoOldVReg = old)
    (hdword : js_pre.vregs JoltISA.amoDwordVReg = dword)
    (hshift : js_pre.vregs JoltISA.amoShiftVReg = shift) :
    ∃ js_afterMiddle : SailJoltState,
      AmoWordSelectMiddleStep
        (fun dst src => .VirtualSignExtendWord dst src)
        (fun dst lhs rhs => .SLT dst lhs rhs)
        (.vreg JoltISA.amoMaskVReg) (.vreg JoltISA.amoNewVReg) rs2
        old dword shift
        (if (zopz0zK_s
            (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
            (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
          rs2Val
        else
          old)
        js_pre js_afterMiddle := by
  exact
    amo_word_select_middle_phase_run
      (fun dst src => .VirtualSignExtendWord dst src)
      (fun dst lhs rhs => .SLT dst lhs rhs)
      (.vreg JoltISA.amoMaskVReg) (.vreg JoltISA.amoNewVReg) rs2
      js_pre rs2Val old dword shift
      (sign_extend (m := 64)
        (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
      (sign_extend (m := 64)
        (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
      (zero_extend (m := 64)
        (bool_to_bit
          (zopz0zI_s
            (sign_extend (m := 64)
              (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
            (sign_extend (m := 64)
              (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)))))
      (if (zopz0zK_s
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
        rs2Val
      else
        old)
      hrs2
      (amo_word_signed_select_extend_phase_run rs2 js_pre rs2Val old dword
        shift hrs2 hold hdword hshift)
      (fun js_afterExt hext_step =>
        amo_word_slt_compare_phase_run_vreg_vreg
          JoltISA.amoMaskVReg JoltISA.amoNewVReg js_afterExt
          (sign_extend (m := 64)
            (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
          (sign_extend (m := 64)
            (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
          old dword shift hext_step.old_ext_vreg hext_step.rs2_ext_vreg
          hext_step.old_vreg hext_step.dword_vreg hext_step.shift_vreg)
      (amo_word_select_value_of_sgt_sext old rs2Val)

/-- `AMOMINU.W`'s select middle chooses the full `rs2` scratch value exactly
when the low words satisfy unsigned `<`. -/
theorem amo_word_minu_middle_run
    (rs2 : regidx) (js_pre : SailJoltState)
    (rs2Val old dword shift : BitVec 64)
    (hrs2 : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail)
    (hold : js_pre.vregs JoltISA.amoOldVReg = old)
    (hdword : js_pre.vregs JoltISA.amoDwordVReg = dword)
    (hshift : js_pre.vregs JoltISA.amoShiftVReg = shift) :
    ∃ js_afterMiddle : SailJoltState,
      AmoWordSelectMiddleStep
        (fun dst src => .VirtualZeroExtendWord dst src)
        (fun dst lhs rhs => .SLTU dst lhs rhs)
        (.vreg JoltISA.amoNewVReg) (.vreg JoltISA.amoMaskVReg) rs2
        old dword shift
        (if (zopz0zI_u
            (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
            (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
          rs2Val
        else
          old)
        js_pre js_afterMiddle := by
  exact
    amo_word_select_middle_phase_run
      (fun dst src => .VirtualZeroExtendWord dst src)
      (fun dst lhs rhs => .SLTU dst lhs rhs)
      (.vreg JoltISA.amoNewVReg) (.vreg JoltISA.amoMaskVReg) rs2
      js_pre rs2Val old dword shift
      (zero_extend (m := 64)
        (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
      (zero_extend (m := 64)
        (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
      (jolt_sltu_value
        (zero_extend (m := 64)
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
        (zero_extend (m := 64)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32)))
      (if (zopz0zI_u
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
        rs2Val
      else
        old)
      hrs2
      (amo_word_unsigned_select_extend_phase_run rs2 js_pre rs2Val old dword
        shift hrs2 hold hdword hshift)
      (fun js_afterExt hext_step =>
        amo_word_sltu_compare_phase_run_vreg_vreg
          JoltISA.amoNewVReg JoltISA.amoMaskVReg js_afterExt
          (zero_extend (m := 64)
            (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
          (zero_extend (m := 64)
            (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
          old dword shift hext_step.rs2_ext_vreg hext_step.old_ext_vreg
          hext_step.old_vreg hext_step.dword_vreg hext_step.shift_vreg)
      (amo_word_select_value_of_sltu_zext old rs2Val)

/-- `AMOMAXU.W`'s select middle chooses the full `rs2` scratch value exactly
when the low words satisfy unsigned `>`. -/
theorem amo_word_maxu_middle_run
    (rs2 : regidx) (js_pre : SailJoltState)
    (rs2Val old dword shift : BitVec 64)
    (hrs2 : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail)
    (hold : js_pre.vregs JoltISA.amoOldVReg = old)
    (hdword : js_pre.vregs JoltISA.amoDwordVReg = dword)
    (hshift : js_pre.vregs JoltISA.amoShiftVReg = shift) :
    ∃ js_afterMiddle : SailJoltState,
      AmoWordSelectMiddleStep
        (fun dst src => .VirtualZeroExtendWord dst src)
        (fun dst lhs rhs => .SLTU dst lhs rhs)
        (.vreg JoltISA.amoMaskVReg) (.vreg JoltISA.amoNewVReg) rs2
        old dword shift
        (if (zopz0zK_u
            (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
            (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
          rs2Val
        else
          old)
        js_pre js_afterMiddle := by
  exact
    amo_word_select_middle_phase_run
      (fun dst src => .VirtualZeroExtendWord dst src)
      (fun dst lhs rhs => .SLTU dst lhs rhs)
      (.vreg JoltISA.amoMaskVReg) (.vreg JoltISA.amoNewVReg) rs2
      js_pre rs2Val old dword shift
      (zero_extend (m := 64)
        (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
      (zero_extend (m := 64)
        (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
      (jolt_sltu_value
        (zero_extend (m := 64)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
        (zero_extend (m := 64)
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)))
      (if (zopz0zK_u
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
        rs2Val
      else
        old)
      hrs2
      (amo_word_unsigned_select_extend_phase_run rs2 js_pre rs2Val old dword
        shift hrs2 hold hdword hshift)
      (fun js_afterExt hext_step =>
        amo_word_sltu_compare_phase_run_vreg_vreg
          JoltISA.amoMaskVReg JoltISA.amoNewVReg js_afterExt
          (zero_extend (m := 64)
            (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
          (zero_extend (m := 64)
            (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
          old dword shift hext_step.old_ext_vreg hext_step.rs2_ext_vreg
          hext_step.old_vreg hext_step.dword_vreg hext_step.shift_vreg)
      (amo_word_select_value_of_sgtu_zext old rs2Val)

/-- After the common word prelude, the `AMOMIN.W` middle block is ready for the
shared word-select program helper. -/
theorem amo_word_min_middle_after_pre
    (rs2 : regidx) (js : SailJoltState) (addr rs2Val : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail) :
    ∀ js_pre : SailJoltState,
      js_pre.sail = js.sail →
      js_pre.vregs JoltISA.amoDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr) →
      js_pre.vregs JoltISA.amoShiftVReg =
        shift_bits_left addr (3 : BitVec 6) →
      js_pre.vregs JoltISA.amoOldVReg =
        amoWordShiftedOld js.sail addr →
      ∃ js_afterMiddle : SailJoltState,
        AmoWordSelectMiddleStep
          (fun dst src => .VirtualSignExtendWord dst src)
          (fun dst lhs rhs => .SLT dst lhs rhs)
          (.vreg JoltISA.amoNewVReg) (.vreg JoltISA.amoMaskVReg) rs2
          (amoWordShiftedOld js.sail addr)
          (loaded_dword_at js.sail (amoWordBase addr))
          (shift_bits_left addr (3 : BitVec 6))
          (if (zopz0zI_s
              (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
              (Sail.BitVec.extractLsb (amoWordShiftedOld js.sail addr) 31 0 :
                BitVec 32) : Bool) then
            rs2Val
          else
            amoWordShiftedOld js.sail addr)
          js_pre js_afterMiddle := by
  intro js_pre hpre_sail hpre_dword hpre_shift hpre_old
  have hrs2_pre : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail := by
    rw [hpre_sail]
    exact hrs2
  exact
    amo_word_min_middle_run rs2 js_pre rs2Val
      (amoWordShiftedOld js.sail addr)
      (loaded_dword_at js.sail (amoWordBase addr))
      (shift_bits_left addr (3 : BitVec 6))
      hrs2_pre hpre_old hpre_dword hpre_shift

/-- After the common word prelude, the `AMOMAX.W` middle block is ready for the
shared word-select program helper. -/
theorem amo_word_max_middle_after_pre
    (rs2 : regidx) (js : SailJoltState) (addr rs2Val : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail) :
    ∀ js_pre : SailJoltState,
      js_pre.sail = js.sail →
      js_pre.vregs JoltISA.amoDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr) →
      js_pre.vregs JoltISA.amoShiftVReg =
        shift_bits_left addr (3 : BitVec 6) →
      js_pre.vregs JoltISA.amoOldVReg =
        amoWordShiftedOld js.sail addr →
      ∃ js_afterMiddle : SailJoltState,
        AmoWordSelectMiddleStep
          (fun dst src => .VirtualSignExtendWord dst src)
          (fun dst lhs rhs => .SLT dst lhs rhs)
          (.vreg JoltISA.amoMaskVReg) (.vreg JoltISA.amoNewVReg) rs2
          (amoWordShiftedOld js.sail addr)
          (loaded_dword_at js.sail (amoWordBase addr))
          (shift_bits_left addr (3 : BitVec 6))
          (if (zopz0zK_s
              (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
              (Sail.BitVec.extractLsb (amoWordShiftedOld js.sail addr) 31 0 :
                BitVec 32) : Bool) then
            rs2Val
          else
            amoWordShiftedOld js.sail addr)
          js_pre js_afterMiddle := by
  intro js_pre hpre_sail hpre_dword hpre_shift hpre_old
  have hrs2_pre : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail := by
    rw [hpre_sail]
    exact hrs2
  exact
    amo_word_max_middle_run rs2 js_pre rs2Val
      (amoWordShiftedOld js.sail addr)
      (loaded_dword_at js.sail (amoWordBase addr))
      (shift_bits_left addr (3 : BitVec 6))
      hrs2_pre hpre_old hpre_dword hpre_shift

/-- After the common word prelude, the `AMOMINU.W` middle block is ready for
the shared word-select program helper. -/
theorem amo_word_minu_middle_after_pre
    (rs2 : regidx) (js : SailJoltState) (addr rs2Val : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail) :
    ∀ js_pre : SailJoltState,
      js_pre.sail = js.sail →
      js_pre.vregs JoltISA.amoDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr) →
      js_pre.vregs JoltISA.amoShiftVReg =
        shift_bits_left addr (3 : BitVec 6) →
      js_pre.vregs JoltISA.amoOldVReg =
        amoWordShiftedOld js.sail addr →
      ∃ js_afterMiddle : SailJoltState,
        AmoWordSelectMiddleStep
          (fun dst src => .VirtualZeroExtendWord dst src)
          (fun dst lhs rhs => .SLTU dst lhs rhs)
          (.vreg JoltISA.amoNewVReg) (.vreg JoltISA.amoMaskVReg) rs2
          (amoWordShiftedOld js.sail addr)
          (loaded_dword_at js.sail (amoWordBase addr))
          (shift_bits_left addr (3 : BitVec 6))
          (if (zopz0zI_u
              (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
              (Sail.BitVec.extractLsb (amoWordShiftedOld js.sail addr) 31 0 :
                BitVec 32) : Bool) then
            rs2Val
          else
            amoWordShiftedOld js.sail addr)
          js_pre js_afterMiddle := by
  intro js_pre hpre_sail hpre_dword hpre_shift hpre_old
  have hrs2_pre : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail := by
    rw [hpre_sail]
    exact hrs2
  exact
    amo_word_minu_middle_run rs2 js_pre rs2Val
      (amoWordShiftedOld js.sail addr)
      (loaded_dword_at js.sail (amoWordBase addr))
      (shift_bits_left addr (3 : BitVec 6))
      hrs2_pre hpre_old hpre_dword hpre_shift

/-- After the common word prelude, the `AMOMAXU.W` middle block is ready for
the shared word-select program helper. -/
theorem amo_word_maxu_middle_after_pre
    (rs2 : regidx) (js : SailJoltState) (addr rs2Val : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail) :
    ∀ js_pre : SailJoltState,
      js_pre.sail = js.sail →
      js_pre.vregs JoltISA.amoDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr) →
      js_pre.vregs JoltISA.amoShiftVReg =
        shift_bits_left addr (3 : BitVec 6) →
      js_pre.vregs JoltISA.amoOldVReg =
        amoWordShiftedOld js.sail addr →
      ∃ js_afterMiddle : SailJoltState,
        AmoWordSelectMiddleStep
          (fun dst src => .VirtualZeroExtendWord dst src)
          (fun dst lhs rhs => .SLTU dst lhs rhs)
          (.vreg JoltISA.amoMaskVReg) (.vreg JoltISA.amoNewVReg) rs2
          (amoWordShiftedOld js.sail addr)
          (loaded_dword_at js.sail (amoWordBase addr))
          (shift_bits_left addr (3 : BitVec 6))
          (if (zopz0zK_u
              (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
              (Sail.BitVec.extractLsb (amoWordShiftedOld js.sail addr) 31 0 :
                BitVec 32) : Bool) then
            rs2Val
          else
            amoWordShiftedOld js.sail addr)
          js_pre js_afterMiddle := by
  intro js_pre hpre_sail hpre_dword hpre_shift hpre_old
  have hrs2_pre : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail := by
    rw [hpre_sail]
    exact hrs2
  exact
    amo_word_maxu_middle_run rs2 js_pre rs2Val
      (amoWordShiftedOld js.sail addr)
      (loaded_dword_at js.sail (amoWordBase addr))
      (shift_bits_left addr (3 : BitVec 6))
      hrs2_pre hpre_old hpre_dword hpre_shift

/-- The `AMOMIN.W` selected scratch value has the same low word as Sail's
signed-min result. -/
theorem amo_word_min_result_extract_eq
    (s : SailState) (addr rs2Val : BitVec 64)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    (Sail.BitVec.extractLsb
      (if (zopz0zI_s
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
          (Sail.BitVec.extractLsb (amoWordShiftedOld s addr) 31 0 :
            BitVec 32) : Bool) then
        rs2Val
      else
        amoWordShiftedOld s addr)
      31 0 : BitVec 32) =
      if (zopz0zI_s
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
          (loaded_word_at s addr) : Bool) then
        (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
      else
        loaded_word_at s addr := by
  rw [amo_word_extract_select_result]
  rw [amo_word_shifted_old_abbrev_extract_eq_loaded_word s addr h_align]

/-- The `AMOMAX.W` selected scratch value has the same low word as Sail's
signed-max result. -/
theorem amo_word_max_result_extract_eq
    (s : SailState) (addr rs2Val : BitVec 64)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    (Sail.BitVec.extractLsb
      (if (zopz0zK_s
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
          (Sail.BitVec.extractLsb (amoWordShiftedOld s addr) 31 0 :
            BitVec 32) : Bool) then
        rs2Val
      else
        amoWordShiftedOld s addr)
      31 0 : BitVec 32) =
      if (zopz0zK_s
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
          (loaded_word_at s addr) : Bool) then
        (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
      else
        loaded_word_at s addr := by
  rw [amo_word_extract_select_result]
  rw [amo_word_shifted_old_abbrev_extract_eq_loaded_word s addr h_align]

/-- The `AMOMINU.W` selected scratch value has the same low word as Sail's
unsigned-min result. -/
theorem amo_word_minu_result_extract_eq
    (s : SailState) (addr rs2Val : BitVec 64)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    (Sail.BitVec.extractLsb
      (if (zopz0zI_u
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
          (Sail.BitVec.extractLsb (amoWordShiftedOld s addr) 31 0 :
            BitVec 32) : Bool) then
        rs2Val
      else
        amoWordShiftedOld s addr)
      31 0 : BitVec 32) =
      if (zopz0zI_u
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
          (loaded_word_at s addr) : Bool) then
        (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
      else
        loaded_word_at s addr := by
  rw [amo_word_extract_select_result]
  rw [amo_word_shifted_old_abbrev_extract_eq_loaded_word s addr h_align]

/-- The `AMOMAXU.W` selected scratch value has the same low word as Sail's
unsigned-max result. -/
theorem amo_word_maxu_result_extract_eq
    (s : SailState) (addr rs2Val : BitVec 64)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    (Sail.BitVec.extractLsb
      (if (zopz0zK_u
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
          (Sail.BitVec.extractLsb (amoWordShiftedOld s addr) 31 0 :
            BitVec 32) : Bool) then
        rs2Val
      else
        amoWordShiftedOld s addr)
      31 0 : BitVec 32) =
      if (zopz0zK_u
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
          (loaded_word_at s addr) : Bool) then
        (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
      else
        loaded_word_at s addr := by
  rw [amo_word_extract_select_result]
  rw [amo_word_shifted_old_abbrev_extract_eq_loaded_word s addr h_align]





/-- Shared aligned concrete execution for word AMO select expansions.

The common prelude extracts the old word, the caller supplies the phased
extension/comparison/select middle block, and the shared postlude splices the
low word of the selected scratch value back to memory. -/
theorem amo_word_select_program_concrete_aligned
    (op : amoop)
    (extend : JoltISA.Dst → JoltISA.Src → JoltISA.Instr)
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src)
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr result64 : BitVec 64) (result : BitVec 32)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (h_mem : AmoMemoryContext op 4 (amoWordBase addr) addr js.sail)
    (h_align : addr &&& (3 : BitVec 64) = 0)
    (hresult : (Sail.BitVec.extractLsb result64 31 0 : BitVec 32) = result)
    (hmiddle :
      ∀ js_pre : SailJoltState,
        js_pre.sail = js.sail →
        js_pre.vregs JoltISA.amoDwordVReg =
          loaded_dword_at js.sail (amoWordBase addr) →
        js_pre.vregs JoltISA.amoShiftVReg =
          shift_bits_left addr (3 : BitVec 6) →
        js_pre.vregs JoltISA.amoOldVReg =
          amoWordShiftedOld js.sail addr →
        ∃ js_afterMiddle : SailJoltState,
          AmoWordSelectMiddleStep extend cmpInstr cmpLhs cmpRhs rs2
            (amoWordShiftedOld js.sail addr)
            (loaded_dword_at js.sail (amoWordBase addr))
            (shift_bits_left addr (3 : BitVec 6))
            result64 js_pre js_afterMiddle) :
    ∃ jsf : SailJoltState,
      (JoltISA.execProgram
        (JoltISA.amoWordSelectProgram extend cmpInstr cmpLhs cmpRhs
          rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail = amoWordFinalSailState rd js.sail addr result := by
  let post : JoltISA.Program :=
    amoWordSelectMiddleProgram extend cmpInstr cmpLhs cmpRhs rs2
      (JoltISA.amoPost64Program rs1 rd (.vreg JoltISA.amoNewVReg)
        JoltISA.amoDwordVReg JoltISA.amoShiftVReg
        JoltISA.amoMaskVReg JoltISA.amoOldVReg)
  have h_no_ovf := amo_word_base_no_ovf addr
  obtain ⟨js_pre, hpre_run, hpre_sail, hpre_dword, hpre_shift, hpre_old⟩ :=
    amo_word_pre64_aligned_run post rs1 js hcfg addr hrs1 h_mem
      h_no_ovf h_align
  have hpre_old_named :
      js_pre.vregs JoltISA.amoOldVReg = amoWordShiftedOld js.sail addr := by
    exact hpre_old
  obtain ⟨js_afterMiddle, hmiddle_step⟩ :=
    hmiddle js_pre hpre_sail hpre_dword hpre_shift hpre_old_named
  have hmiddle_sail : js_afterMiddle.sail = js.sail := by
    rw [hmiddle_step.sail, hpre_sail]
  obtain ⟨jsf, hpost_run, hpost_sail⟩ :=
    amo_word_post64_vreg_aligned_run rs1 rd
      js js_afterMiddle hcfg addr result64 hrs1 h_mem h_no_ovf h_align
      hmiddle_sail hmiddle_step.result_vreg
      hmiddle_step.dword_vreg hmiddle_step.shift_vreg hmiddle_step.old_vreg
  refine ⟨jsf, ?_, ?_⟩
  · unfold JoltISA.amoWordSelectProgram
    change
      (JoltISA.execProgram
        (JoltISA.amoPre64Program rs1 JoltISA.amoOldVReg
          JoltISA.amoDwordVReg JoltISA.amoShiftVReg post)).run js =
        .ok RETIRE_SUCCESS jsf
    rw [hpre_run]
    rw [hmiddle_step.run
      (JoltISA.amoPost64Program rs1 rd (.vreg JoltISA.amoNewVReg)
        JoltISA.amoDwordVReg JoltISA.amoShiftVReg
        JoltISA.amoMaskVReg JoltISA.amoOldVReg)]
    exact hpost_run
  · rw [hpost_sail, hresult]

/-- Shared misaligned concrete execution for word AMO select expansions. -/
theorem amo_word_select_program_concrete_misaligned
    (extend : JoltISA.Dst → JoltISA.Src → JoltISA.Instr)
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src)
    (rs2 rs1 rd : regidx) (js : SailJoltState) (addr : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (h_align : addr &&& (3 : BitVec 64) ≠ 0) :
    (JoltISA.execProgram
      (JoltISA.amoWordSelectProgram extend cmpInstr cmpLhs cmpRhs
        rs2 rs1 rd)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr addr, ExceptionType.E_SAMO_Addr_Align ())) js := by
  unfold JoltISA.amoWordSelectProgram
  exact
    amo_word_pre64_misaligned_run rs1 JoltISA.amoOldVReg
      JoltISA.amoDwordVReg JoltISA.amoShiftVReg
      (amoWordSelectMiddleProgram extend cmpInstr cmpLhs cmpRhs rs2
        (JoltISA.amoPost64Program rs1 rd (.vreg JoltISA.amoNewVReg)
          JoltISA.amoDwordVReg JoltISA.amoShiftVReg
          JoltISA.amoMaskVReg JoltISA.amoOldVReg))
      js addr hrs1 h_align

/-- Shared aligned public branch for word AMO select expansions. -/
theorem amo_word_select_program_eq_sail_aligned
    (op : amoop)
    (extend : JoltISA.Dst → JoltISA.Src → JoltISA.Instr)
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src)
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val result64 : BitVec 64) (result : BitVec 32)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryContext op 4 (amoWordBase addr) addr js.sail)
    (h_align : addr &&& (3 : BitVec 64) = 0)
    (hnot_cas : (op == amoop.AMOCAS) = false)
    (hresult_extract :
      (Sail.BitVec.extractLsb result64 31 0 : BitVec 32) = result)
    (hmiddle :
      ∀ js_pre : SailJoltState,
        js_pre.sail = js.sail →
        js_pre.vregs JoltISA.amoDwordVReg =
          loaded_dword_at js.sail (amoWordBase addr) →
        js_pre.vregs JoltISA.amoShiftVReg =
          shift_bits_left addr (3 : BitVec 6) →
        js_pre.vregs JoltISA.amoOldVReg =
          amoWordShiftedOld js.sail addr →
        ∃ js_afterMiddle : SailJoltState,
          AmoWordSelectMiddleStep extend cmpInstr cmpLhs cmpRhs rs2
            (amoWordShiftedOld js.sail addr)
            (loaded_dword_at js.sail (amoWordBase addr))
            (shift_bits_left addr (3 : BitVec 6))
            result64 js_pre js_afterMiddle)
    (hsail_result :
      amoWordSailResult op
        (show BitVec (4 * 8) from
          trunc (m := (((4 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
        (BitVec.setWidth (4 * 8) (loaded_word_at js.sail addr)) =
      result) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoWordSelectProgram extend cmpInstr cmpLhs cmpRhs
        rs2 rs1 rd)).run js) =
      (execute_AMO op false false rs2 rs1 4 rd).run js.sail := by
  rcases amo_word_select_program_concrete_aligned
      op extend cmpInstr cmpLhs cmpRhs rs2 rs1 rd js hcfg addr result64
      result hrs1 h_mem h_align hresult_extract hmiddle with
    ⟨jsf, hjolt, hjolt_sail⟩
  have hsail :=
    execute_AMO_word_non_cas_aligned
      op rs2 rs1 rd js hcfg addr rs2Val result
      hrs1 hrs2 hrd h_mem h_align hnot_cas hsail_result
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail, hsail]

/-- Shared misaligned public branch for word AMO select expansions. -/
theorem amo_word_select_program_eq_sail_misaligned
    (op : amoop)
    (extend : JoltISA.Dst → JoltISA.Src → JoltISA.Instr)
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src)
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_align : addr &&& (3 : BitVec 64) ≠ 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoWordSelectProgram extend cmpInstr cmpLhs cmpRhs
        rs2 rs1 rd)).run js) =
      (execute_AMO op false false rs2 rs1 4 rd).run js.sail := by
  have hjolt :=
    amo_word_select_program_concrete_misaligned
      extend cmpInstr cmpLhs cmpRhs rs2 rs1 rd js addr hrs1 h_align
  have hsail :=
    execute_AMO_word_misaligned
      op rs2 rs1 rd js hcfg addr rs2Val hrs1 hrs2 h_align
  rw [hjolt]
  simp only [projectResult, project]
  symm
  exact hsail

/-- Shared projection helper for word AMO select expansions. -/
theorem amo_word_select_program_project_eq_sail
    (op : amoop)
    (extend : JoltISA.Dst → JoltISA.Src → JoltISA.Instr)
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src)
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val result64 : BitVec 64) (result : BitVec 32)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryContext op 4 (amoWordBase addr) addr js.sail)
    (hnot_cas : (op == amoop.AMOCAS) = false)
    (hresult_extract :
      addr &&& (3 : BitVec 64) = 0 →
        (Sail.BitVec.extractLsb result64 31 0 : BitVec 32) = result)
    (hmiddle :
      ∀ js_pre : SailJoltState,
        js_pre.sail = js.sail →
        js_pre.vregs JoltISA.amoDwordVReg =
          loaded_dword_at js.sail (amoWordBase addr) →
        js_pre.vregs JoltISA.amoShiftVReg =
          shift_bits_left addr (3 : BitVec 6) →
        js_pre.vregs JoltISA.amoOldVReg =
          amoWordShiftedOld js.sail addr →
        ∃ js_afterMiddle : SailJoltState,
          AmoWordSelectMiddleStep extend cmpInstr cmpLhs cmpRhs rs2
            (amoWordShiftedOld js.sail addr)
            (loaded_dword_at js.sail (amoWordBase addr))
            (shift_bits_left addr (3 : BitVec 6))
            result64 js_pre js_afterMiddle)
    (hsail_result :
      amoWordSailResult op
        (show BitVec (4 * 8) from
          trunc (m := (((4 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
        (BitVec.setWidth (4 * 8) (loaded_word_at js.sail addr)) =
      result) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoWordSelectProgram extend cmpInstr cmpLhs cmpRhs
        rs2 rs1 rd)).run js) =
      (execute_AMO op false false rs2 rs1 4 rd).run js.sail := by
  by_cases h_align : addr &&& (3 : BitVec 64) = 0
  · exact
      amo_word_select_program_eq_sail_aligned
        op extend cmpInstr cmpLhs cmpRhs rs2 rs1 rd js hcfg addr rs2Val
        result64 result hrs1 hrs2 hrd h_mem h_align hnot_cas
        (hresult_extract h_align) hmiddle hsail_result
  · exact
      amo_word_select_program_eq_sail_misaligned
        op extend cmpInstr cmpLhs cmpRhs rs2 rs1 rd js hcfg addr rs2Val
        hrs1 hrs2 h_align

/-- The aligned `AMOSWAP.W` postlude stores `rs2[31:0]` into the selected word
lane and writes the sign-extended old word into `rd`. -/
theorem amo_word_post64_amoswap_aligned_run
    (rs2 rs1 rd : regidx) (js js_pre : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_mem : AmoMemoryContext amoop.AMOSWAP 4 (amoWordBase addr) addr js.sail)
    (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (3 : BitVec 64) = 0)
    (hpre_sail : js_pre.sail = js.sail)
    (hpre_dword :
      js_pre.vregs JoltISA.amoDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr))
    (hpre_shift :
      js_pre.vregs JoltISA.amoShiftVReg =
        shift_bits_left addr (3 : BitVec 6))
    (hpre_old :
      js_pre.vregs JoltISA.amoOldVReg =
        shift_bits_right
          (loaded_dword_at js.sail (amoWordBase addr))
          (Sail.BitVec.extractLsb
            (shift_bits_left addr (3 : BitVec 6)) 5 0)) :
    ∃ jsf : SailJoltState,
      (JoltISA.execProgram
        (JoltISA.amoPost64Program rs1 rd (.xreg rs2)
          JoltISA.amoDwordVReg JoltISA.amoShiftVReg
          JoltISA.amoMaskVReg JoltISA.amoOldVReg)).run js_pre =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail =
        amoWordFinalSailState rd js.sail addr
          (Sail.BitVec.extractLsb rs2Val 31 0) := by
  let shift64 := shift_bits_left addr (3 : BitVec 6)
  let shift6 := Sail.BitVec.extractLsb shift64 5 0
  let dword := loaded_dword_at js.sail (amoWordBase addr)
  let old := shift_bits_right dword shift6
  let mask32 := (0x00000000FFFFFFFF : BitVec 64)
  let shiftedMask := shift_bits_left mask32 shift6
  let shiftedNew := shift_bits_left rs2Val shift6
  let dwordNew := amoWordSplicedDword js.sail addr rs2Val
  let wordResult : BitVec 32 := Sail.BitVec.extractLsb rs2Val 31 0
  have hsetup := amo_word_store_setup addr h_no_ovf h_align
  obtain ⟨js_mask32, hmask_sail, hmask_mask, hmask_shift, hmask_dword,
      hmask_old, _hmask_new, hmask_tail⟩ :=
    amo_word_mask32_prefix_run js_pre js.sail shift64 dword old
      hpre_sail hpre_shift hpre_dword hpre_old
  obtain ⟨js_shifted_mask, hshift_mask_sail, hshift_mask_mask,
      hshift_mask_shift, hshift_mask_dword, hshift_mask_old,
      _hshift_mask_new, hshift_mask_tail⟩ :=
    amo_word_shift_mask_prefix_run js_mask32 js.sail shift64 dword old
      hmask_sail hmask_mask hmask_shift hmask_dword hmask_old
  obtain ⟨js_shifted_new, hshift_new_sail, hshift_new_shift,
      hshift_new_mask, hshift_new_dword, hshift_new_old,
      hshift_new_tail⟩ :=
    amo_word_shift_new_prefix_run rs2 js_shifted_mask js.sail rs2Val
      shift64 shiftedMask dword old hshift_mask_sail hrs2 hshift_mask_mask
      hshift_mask_shift hshift_mask_dword hshift_mask_old
  obtain ⟨js_splice, hsplice_sail, hsplice_dword, hsplice_old,
      hsplice_tail⟩ :=
    amo_word_splice_block_run js_shifted_new js.sail addr rs2Val old hsetup
      hshift_new_sail hshift_new_dword hshift_new_shift hshift_new_mask
      hshift_new_old
  obtain ⟨js_store_base, hstore_base_sail, hstore_base, hstore_base_dword,
      hstore_base_old, hstore_base_tail⟩ :=
    amo_word_store_base_prefix_run rs1 js_splice js.sail addr dwordNew old
      hsplice_sail hrs1 hsplice_dword hsplice_old
  obtain ⟨js_store, hstore_sail, hstore_old, hstore_tail⟩ :=
    amo_word_sd_spliced_dword_run js_store_base js.sail addr dwordNew old
      hcfg h_mem h_no_ovf hstore_base_sail hstore_base hstore_base_dword
      hstore_base_old
  have hword_store :
      state_after_dword_store js.sail (amoWordBase addr) dwordNew =
        state_after_word_store js.sail addr wordResult :=
    amo_word_spliced_dword_store_eq_word_store
      js.sail addr rs2Val hsetup h_mem.jolt_bytes
  have hstore_sail_word :
      js_store.sail = state_after_word_store js.sail addr wordResult := by
    rw [hstore_sail, hword_store]
  have hold_writeback :
      sign_extend (m := 64)
        ((Sail.BitVec.extractLsb old 31 0) : BitVec 32) =
      sign_extend (m := 64) (loaded_word_at js.sail addr) :=
    amo_word_shifted_old_sign_extend_eq_loaded_word js.sail addr h_align
  obtain ⟨jsf, hwriteback_sail, hwriteback_tail⟩ :=
    amo_word_writeback_old_run rd js_store js.sail addr wordResult old
      hstore_sail_word hstore_old hold_writeback
  refine ⟨jsf, ?_, ?_⟩
  · unfold JoltISA.amoPost64Program JoltISA.amoPost64ProgramWithScratch
    rw [hmask_tail]
    rw [hshift_mask_tail]
    rw [hshift_new_tail]
    rw [hsplice_tail]
    rw [hstore_base_tail]
    rw [hstore_tail]
    rw [hwriteback_tail]
    rfl
  · exact hwriteback_sail

end AtomicFamily

end
