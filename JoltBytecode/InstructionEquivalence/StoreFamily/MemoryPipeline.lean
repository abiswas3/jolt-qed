import JoltBytecode.InstructionEquivalence.StoreFamily.Splice
import JoltBytecode.InstructionEquivalence.LoadFamily.DwordArithmetic

/-!
# Store-family memory pipeline lemmas

This file proves the store-family Sail/Jolt memory-pipeline reductions.  Public
store theorem bundles live in `StoreFamily.Bundles`; this file defines and
consumes the internal `StoreMemoryContext` helper used by the store reduction
lemmas.
-/

set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace StoreFamily

/-- Internal memory context shared by store-family helper lemmas.

This is not a public theorem assumption. Public store theorems take
`StoreProgramEqSailAssumptions`; `StoreFamily.Derived` constructs this context
from that public bundle. -/
structure StoreMemoryContext
    (sailAddr joltAddr : BitVec 64) (sailWidth : Nat) (s : SailState) :
    Prop where
  jolt_mem : FlatLoadStoreMem joltAddr 8 s
  sail_store_mem : FlatStoreMem sailAddr sailWidth s
  cfg : JoltConfig s

/-- The read half of the Jolt read-modify-write dword access. -/
theorem StoreMemoryContext.jolt_load_mem
    {sailAddr joltAddr : BitVec 64} {sailWidth : Nat} {s : SailState}
    (h : StoreMemoryContext sailAddr joltAddr sailWidth s) :
    FlatPhysMem joltAddr 8 s :=
  h.jolt_mem.toFlatPhysMem

/-- The write half of the Jolt read-modify-write dword access. -/
theorem StoreMemoryContext.jolt_store_mem
    {sailAddr joltAddr : BitVec 64} {sailWidth : Nat} {s : SailState}
    (h : StoreMemoryContext sailAddr joltAddr sailWidth s) :
    FlatStoreMem joltAddr 8 s :=
  h.jolt_mem.toFlatStoreMem

/-- The Jolt-side dword bytes carried by the store memory context. -/
theorem StoreMemoryContext.jolt_bytes
    {sailAddr joltAddr : BitVec 64} {sailWidth : Nat} {s : SailState}
    (h : StoreMemoryContext sailAddr joltAddr sailWidth s) :
    DwordBytesPresent joltAddr s :=
  h.jolt_mem.bytes

/-- The enclosing dword base used by store expansions is eight-byte aligned. -/
theorem store_dword_base_aligns (val : BitVec 64) (imm : BitVec 12) :
    compute_aligned_dword_base_address val imm &&& (7 : BitVec 64) = 0 := by
  unfold compute_aligned_dword_base_address load_effective_address
  exact align_down_8_and_7_eq_zero _

/-- The enclosing dword base has room for all eight bytes in the 64-bit address
space. -/
theorem store_dword_base_no_ovf (val : BitVec 64) (imm : BitVec 12) :
    (compute_aligned_dword_base_address val imm).toNat + 7 < 2 ^ 64 := by
  exact aligned_addr_no_ovf_of_align _ (store_dword_base_aligns val imm)

/-- Re-express the low-three-bit offset as a 64-bit bit-vector. -/
private theorem offset_bv_eq_low_three (ea : BitVec 64) :
    BitVec.ofNat 64 (ea &&& (7 : BitVec 64)).toNat =
      ea &&& (7 : BitVec 64) := by
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- Subtracting the enclosing dword base leaves exactly the low three address
bits. -/
private theorem offset_sub_eq_low_three (ea : BitVec 64) :
    ea - (ea &&& (-8 : BitVec 64)) = ea &&& (7 : BitVec 64) := by
  have hsplit := addr_split_aligned_offset ea
  rw [offset_bv_eq_low_three ea] at hsplit
  nth_rewrite 1 [← hsplit]
  simp [add_comm]

/-- An address equals the dword base plus its low-three-bit lane offset at the
Nat level. -/
theorem store_ea_toNat_eq_base_plus_offset (ea : BitVec 64) :
    ea.toNat =
      (ea &&& (-8 : BitVec 64)).toNat +
        (ea - (ea &&& (-8 : BitVec 64))).toNat := by
  let base := ea &&& (-8 : BitVec 64)
  let off := (ea &&& (7 : BitVec 64)).toNat
  have hoff_lt : off < 8 := by
    exact addr_and_seven_lt_eight ea
  have hbase_no_ovf : base.toNat + 7 < 2 ^ 64 := by
    have hbase_align : base &&& (7 : BitVec 64) = 0 := by
      unfold base
      exact align_down_8_and_7_eq_zero _
    exact aligned_addr_no_ovf_of_align base hbase_align
  have hsub_toNat : (ea - base).toNat = off := by
    unfold base off
    rw [offset_sub_eq_low_three ea]
  have hoff_toNat : (BitVec.ofNat 64 off).toNat = off := by
    rw [BitVec.toNat_ofNat]
    have hoff64 : off < 2 ^ 64 := by omega
    exact Nat.mod_eq_of_lt hoff64
  have hsum_lt : base.toNat + (BitVec.ofNat 64 off).toNat < 2 ^ 64 := by
    rw [hoff_toNat]
    omega
  have hnat := BitVec.toNat_add_of_lt
    (x := base) (y := BitVec.ofNat 64 off) hsum_lt
  have hsplit := addr_split_aligned_offset ea
  unfold base off at hnat
  rw [hsplit] at hnat
  rw [hoff_toNat] at hnat
  rw [hsub_toNat]
  exact hnat

/-- Any byte address has one of the eight byte offsets inside its enclosing
dword. -/
theorem store_byte_offset_cases (ea : BitVec 64) :
    (ea - (ea &&& (-8 : BitVec 64))).toNat = 0 ∨
    (ea - (ea &&& (-8 : BitVec 64))).toNat = 1 ∨
    (ea - (ea &&& (-8 : BitVec 64))).toNat = 2 ∨
    (ea - (ea &&& (-8 : BitVec 64))).toNat = 3 ∨
    (ea - (ea &&& (-8 : BitVec 64))).toNat = 4 ∨
    (ea - (ea &&& (-8 : BitVec 64))).toNat = 5 ∨
    (ea - (ea &&& (-8 : BitVec 64))).toNat = 6 ∨
    (ea - (ea &&& (-8 : BitVec 64))).toNat = 7 := by
  have hsub_toNat :
      (ea - (ea &&& (-8 : BitVec 64))).toNat =
        (ea &&& (7 : BitVec 64)).toNat := by
    rw [offset_sub_eq_low_three ea]
  have hoff_lt : (ea &&& (7 : BitVec 64)).toNat < 8 := by
    exact addr_and_seven_lt_eight ea
  rw [hsub_toNat]
  omega

/-- A halfword-aligned address has one of the four halfword offsets inside its
enclosing dword. -/
theorem store_halfword_offset_cases (ea : BitVec 64)
    (halign : ea &&& (1 : BitVec 64) = 0) :
    (ea - (ea &&& (-8 : BitVec 64))).toNat = 0 ∨
    (ea - (ea &&& (-8 : BitVec 64))).toNat = 2 ∨
    (ea - (ea &&& (-8 : BitVec 64))).toNat = 4 ∨
    (ea - (ea &&& (-8 : BitVec 64))).toNat = 6 := by
  have hsub_toNat :
      (ea - (ea &&& (-8 : BitVec 64))).toNat =
        (ea &&& (7 : BitVec 64)).toNat := by
    rw [offset_sub_eq_low_three ea]
  have hoff_cases := halfword_offset_cases ea halign
  rw [hsub_toNat]
  exact hoff_cases

/-- A word-aligned address has one of the two word offsets inside its enclosing
dword. -/
theorem store_word_offset_cases (ea : BitVec 64)
    (halign : ea &&& (3 : BitVec 64) = 0) :
    (ea - (ea &&& (-8 : BitVec 64))).toNat = 0 ∨
    (ea - (ea &&& (-8 : BitVec 64))).toNat = 4 := by
  have hsub_toNat :
      (ea - (ea &&& (-8 : BitVec 64))).toNat =
        (ea &&& (7 : BitVec 64)).toNat := by
    rw [offset_sub_eq_low_three ea]
  have hoff_cases := word_offset_cases ea halign
  rw [hsub_toNat]
  exact hoff_cases

/-- Effective store addresses always supply the setup facts needed by `SB`. -/
theorem byteStoreSetup_of_effective_address
    (val : BitVec 64) (imm : BitVec 12) :
    StoreSplice.ByteStoreSetup
      (load_effective_address val imm)
      (compute_aligned_dword_base_address val imm) := by
  exact
    { base_is_aligned := rfl
      no_ovf := store_dword_base_no_ovf val imm
      ea_toNat := store_ea_toNat_eq_base_plus_offset
        (load_effective_address val imm)
      offset_cases := store_byte_offset_cases (load_effective_address val imm) }

/-- Effective aligned store addresses supply the setup facts needed by `SH`. -/
theorem halfwordStoreSetup_of_effective_address
    (val : BitVec 64) (imm : BitVec 12)
    (halign : load_effective_address val imm &&& (1 : BitVec 64) = 0) :
    StoreSplice.HalfwordStoreSetup
      (load_effective_address val imm)
      (compute_aligned_dword_base_address val imm) := by
  exact
    { base_is_aligned := rfl
      no_ovf := store_dword_base_no_ovf val imm
      ea_toNat := store_ea_toNat_eq_base_plus_offset
        (load_effective_address val imm)
      halfword_aligned := halign
      offset_cases := store_halfword_offset_cases
        (load_effective_address val imm) halign }

/-- Effective aligned store addresses supply the setup facts needed by `SW`. -/
theorem wordStoreSetup_of_effective_address
    (val : BitVec 64) (imm : BitVec 12)
    (halign : load_effective_address val imm &&& (3 : BitVec 64) = 0) :
    StoreSplice.WordStoreSetup
      (load_effective_address val imm)
      (compute_aligned_dword_base_address val imm) := by
  exact
    { base_is_aligned := rfl
      no_ovf := store_dword_base_no_ovf val imm
      ea_toNat := store_ea_toNat_eq_base_plus_offset
        (load_effective_address val imm)
      word_aligned := halign
      offset_cases := store_word_offset_cases
        (load_effective_address val imm) halign }

/-- Plain RAM byte writes are the canonical one-byte hashmap update. -/
theorem write_ram_byte_eq_state_after_byte_store
    (addr : BitVec 64) (data : BitVec 8) (s : SailState) :
    LeanRV64D.Functions.write_ram write_kind.Write_plain
      (physaddr.Physaddr addr) 1 data default_meta s =
    .ok true (state_after_byte_store s addr data) := by
  dsimp [LeanRV64D.Functions.write_ram,
    Sail.ConcurrencyInterfaceV1.sail_mem_write,
    PreSail.ConcurrencyInterfaceV1.sail_mem_write,
    PreSail.writeBytes,
    PreSail.writeByte,
    state_after_byte_store,
    byte_byte,
    default_meta,
    __WriteRAM_Meta]
  norm_num
  rfl

/-- Plain RAM halfword writes are the canonical two-byte hashmap update. -/
theorem write_ram_halfword_eq_state_after_halfword_store
    (addr : BitVec 64) (data : BitVec 16) (s : SailState) :
    LeanRV64D.Functions.write_ram write_kind.Write_plain
      (physaddr.Physaddr addr) 2 data default_meta s =
    .ok true (state_after_halfword_store s addr data) := by
  dsimp [LeanRV64D.Functions.write_ram,
    Sail.ConcurrencyInterfaceV1.sail_mem_write,
    PreSail.ConcurrencyInterfaceV1.sail_mem_write,
    PreSail.writeBytes,
    PreSail.writeByte,
    state_after_halfword_store,
    halfword_byte,
    default_meta,
    __WriteRAM_Meta]
  norm_num
  rfl

/-- Plain RAM word writes are the canonical four-byte hashmap update. -/
theorem write_ram_word_eq_state_after_word_store
    (addr : BitVec 64) (data : BitVec 32) (s : SailState) :
    LeanRV64D.Functions.write_ram write_kind.Write_plain
      (physaddr.Physaddr addr) 4 data default_meta s =
    .ok true (state_after_word_store s addr data) := by
  dsimp [LeanRV64D.Functions.write_ram,
    Sail.ConcurrencyInterfaceV1.sail_mem_write,
    PreSail.ConcurrencyInterfaceV1.sail_mem_write,
    PreSail.writeBytes,
    PreSail.writeByte,
    state_after_word_store,
    word_byte,
    default_meta,
    __WriteRAM_Meta]
  norm_num
  rfl

/-- The effective-address write phase for plain stores is a pure success. -/
theorem mem_write_ea_plain_store_ok
    (addr : BitVec 64) (width : Nat) (s : SailState) :
    mem_write_ea (physaddr.Physaddr addr) width false false false s =
      .ok (Ok ()) s := by
  unfold mem_write_ea
  simp only [Bool.false_or, Bool.false_and]
  simp only [Bool.false_eq_true, if_false]
  unfold write_kind_of_flags
  unfold write_ram_ea
  change
    (EStateM.bind (EStateM.pure write_kind.Write_plain)
      (fun _ => EStateM.pure (Ok ()))) s =
      .ok (Ok ()) s
  rfl

/-- Non-MMIO machine-mode byte writes reduce to the canonical byte-store
state. -/
theorem mem_write_value_byte_eq_state_after_byte_store
    (addr : BitVec 64) (data : BitVec 8) (s : SailState)
    (hcfg : JoltConfig s) (hstore : FlatStoreMem addr 1 s) :
    mem_write_value (physaddr.Physaddr addr) 1 data
      (Store Data) false false false s =
    .ok (Ok true) (state_after_byte_store s addr data) := by
  obtain ⟨mval, h_ms_regs, h_mprv⟩ := hcfg.mstatus_mprv.value
  have h_ms_read := readReg_eq Register.mstatus s mval h_ms_regs
  have h_priv := readReg_eq Register.cur_privilege s Privilege.Machine
    hcfg.cur_privilege.value
  unfold mem_write_value mem_write_value_meta mem_write_value_priv_meta
    checked_mem_write
  simp only [bind, EStateM.bind, pure, h_ms_read, h_priv]
  unfold effectivePrivilege
  simp (config := { decide := true }) only [h_mprv, bne, BEq.beq, pure]
  change
    (EStateM.bind
      (EStateM.bind
        (phys_access_check (Store Data) Privilege.Machine
          (physaddr.Physaddr addr) 1 false)
        (fun result =>
          match result with
          | some e => EStateM.pure (Err e)
          | none =>
              EStateM.bind (within_mmio_writable (physaddr.Physaddr addr) 1)
                (fun isMmio =>
                  if isMmio = true then
                    mmio_write (physaddr.Physaddr addr) 1 data
                  else
                    EStateM.bind (write_kind_of_flags false false false)
                      (fun wk =>
                        EStateM.bind
                          (LeanRV64D.Functions.write_ram wk
                            (physaddr.Physaddr addr) 1 data default_meta)
                          (fun ok => EStateM.pure (Ok ok))))))
      (fun result => EStateM.pure result)) s =
    .ok (Ok true) (state_after_byte_store s addr data)
  simp only [EStateM.bind, hstore.pmp]
  simp only [hstore.mmio]
  simp only [Bool.false_eq_true, if_false]
  unfold write_kind_of_flags
  simp only [EStateM.bind, pure, EStateM.pure]
  rw [write_ram_byte_eq_state_after_byte_store addr data s]

/-- Non-MMIO machine-mode halfword writes reduce to the canonical halfword-store
state. -/
theorem mem_write_value_halfword_eq_state_after_halfword_store
    (addr : BitVec 64) (data : BitVec 16) (s : SailState)
    (hcfg : JoltConfig s) (hstore : FlatStoreMem addr 2 s) :
    mem_write_value (physaddr.Physaddr addr) 2 data
      (Store Data) false false false s =
    .ok (Ok true) (state_after_halfword_store s addr data) := by
  obtain ⟨mval, h_ms_regs, h_mprv⟩ := hcfg.mstatus_mprv.value
  have h_ms_read := readReg_eq Register.mstatus s mval h_ms_regs
  have h_priv := readReg_eq Register.cur_privilege s Privilege.Machine
    hcfg.cur_privilege.value
  unfold mem_write_value mem_write_value_meta mem_write_value_priv_meta
    checked_mem_write
  simp only [bind, EStateM.bind, pure, h_ms_read, h_priv]
  unfold effectivePrivilege
  simp (config := { decide := true }) only [h_mprv, bne, BEq.beq, pure]
  change
    (EStateM.bind
      (EStateM.bind
        (phys_access_check (Store Data) Privilege.Machine
          (physaddr.Physaddr addr) 2 false)
        (fun result =>
          match result with
          | some e => EStateM.pure (Err e)
          | none =>
              EStateM.bind (within_mmio_writable (physaddr.Physaddr addr) 2)
                (fun isMmio =>
                  if isMmio = true then
                    mmio_write (physaddr.Physaddr addr) 2 data
                  else
                    EStateM.bind (write_kind_of_flags false false false)
                      (fun wk =>
                        EStateM.bind
                          (LeanRV64D.Functions.write_ram wk
                            (physaddr.Physaddr addr) 2 data default_meta)
                          (fun ok => EStateM.pure (Ok ok))))))
      (fun result => EStateM.pure result)) s =
    .ok (Ok true) (state_after_halfword_store s addr data)
  simp only [EStateM.bind, hstore.pmp]
  simp only [hstore.mmio]
  simp only [Bool.false_eq_true, if_false]
  unfold write_kind_of_flags
  simp only [EStateM.bind, pure, EStateM.pure]
  rw [write_ram_halfword_eq_state_after_halfword_store addr data s]

/-- Non-MMIO machine-mode word writes reduce to the canonical word-store
state. -/
theorem mem_write_value_word_eq_state_after_word_store
    (addr : BitVec 64) (data : BitVec 32) (s : SailState)
    (hcfg : JoltConfig s) (hstore : FlatStoreMem addr 4 s) :
    mem_write_value (physaddr.Physaddr addr) 4 data
      (Store Data) false false false s =
    .ok (Ok true) (state_after_word_store s addr data) := by
  obtain ⟨mval, h_ms_regs, h_mprv⟩ := hcfg.mstatus_mprv.value
  have h_ms_read := readReg_eq Register.mstatus s mval h_ms_regs
  have h_priv := readReg_eq Register.cur_privilege s Privilege.Machine
    hcfg.cur_privilege.value
  unfold mem_write_value mem_write_value_meta mem_write_value_priv_meta
    checked_mem_write
  simp only [bind, EStateM.bind, pure, h_ms_read, h_priv]
  unfold effectivePrivilege
  simp (config := { decide := true }) only [h_mprv, bne, BEq.beq, pure]
  change
    (EStateM.bind
      (EStateM.bind
        (phys_access_check (Store Data) Privilege.Machine
          (physaddr.Physaddr addr) 4 false)
        (fun result =>
          match result with
          | some e => EStateM.pure (Err e)
          | none =>
              EStateM.bind (within_mmio_writable (physaddr.Physaddr addr) 4)
                (fun isMmio =>
                  if isMmio = true then
                    mmio_write (physaddr.Physaddr addr) 4 data
                  else
                    EStateM.bind (write_kind_of_flags false false false)
                      (fun wk =>
                        EStateM.bind
                          (LeanRV64D.Functions.write_ram wk
                            (physaddr.Physaddr addr) 4 data default_meta)
                          (fun ok => EStateM.pure (Ok ok))))))
      (fun result => EStateM.pure result)) s =
    .ok (Ok true) (state_after_word_store s addr data)
  simp only [EStateM.bind, hstore.pmp]
  simp only [hstore.mmio]
  simp only [Bool.false_eq_true, if_false]
  unfold write_kind_of_flags
  simp only [EStateM.bind, pure, EStateM.pure]
  rw [write_ram_word_eq_state_after_word_store addr data s]

/-- Adding Sail's integer zero to a bit-vector address leaves it unchanged. -/
private theorem bitvec_addInt_zero (addr : BitVec 64) :
    Sail.BitVec.addInt addr 0 = addr := by
  unfold Sail.BitVec.addInt
  rw [show BitVec.ofInt 64 0 = (0 : BitVec 64) by decide]
  exact BitVec.add_zero addr

private theorem extractLsb_full_width {w : Nat} (hpos : 0 < w)
    (data : BitVec w) :
    BitVec.extractLsb (w - 1) 0 data = data := by
  ext i
  simp

/-- The computed enclosing dword base is an aligned Sail access address. -/
theorem store_dword_base_aligned_access
    (val : BitVec 64) (imm : BitVec 12) :
    AlignedAccess (compute_aligned_dword_base_address val imm) 8 :=
  { misalign := access_misaligned_8_aligned_false _
      (store_dword_base_aligns val imm)
    split := split_misaligned_aligned_8 _
      (store_dword_base_aligns val imm) }

/-- A halfword-aligned store address is an aligned Sail access address. -/
theorem halfword_store_aligned_access (addr : BitVec 64)
    (halign : addr &&& (1 : BitVec 64) = 0) :
    AlignedAccess addr 2 :=
  { misalign := access_misaligned_2_aligned_false addr halign
    split := split_misaligned_aligned_2 addr halign }

/-- A word-aligned store address is an aligned Sail access address. -/
theorem word_store_aligned_access (addr : BitVec 64)
    (halign : addr &&& (3 : BitVec 64) = 0) :
    AlignedAccess addr 4 :=
  { misalign := access_misaligned_4_aligned_false addr halign
    split := split_misaligned_aligned_4 addr halign }

/-- The one-iteration byte-store loop passes the byte payload through
unchanged. -/
private theorem byte_store_loop_data_eq (data : BitVec 8) :
    BitVec.setWidth (8 * (((1 : Int), (1 : Int)).2.toNat))
      (Sail.BitVec.extractLsb data
        (8 * ((↑(((false, (0 : Nat), true).2.1) : Nat) : Int) + 1) *
          ((1 : Int), (1 : Int)).2 - 1).toNat
        (8 * (↑(((false, (0 : Nat), true).2.1) : Nat) : Int) *
          ((1 : Int), (1 : Int)).2).toNat) = data := by
  simp [Sail.BitVec.extractLsb]
  exact extractLsb_full_width (by omega) data

/-- The one-iteration halfword-store loop passes the halfword payload through
unchanged. -/
private theorem halfword_store_loop_data_eq (data : BitVec 16) :
    BitVec.setWidth (8 * (((1 : Int), (2 : Int)).2.toNat))
      (Sail.BitVec.extractLsb data
        (8 * ((↑(((false, (0 : Nat), true).2.1) : Nat) : Int) + 1) *
          ((1 : Int), (2 : Int)).2 - 1).toNat
        (8 * (↑(((false, (0 : Nat), true).2.1) : Nat) : Int) *
          ((1 : Int), (2 : Int)).2).toNat) = data := by
  simp [Sail.BitVec.extractLsb]
  exact extractLsb_full_width (by omega) data

/-- The one-iteration word-store loop passes the word payload through
unchanged. -/
private theorem word_store_loop_data_eq (data : BitVec 32) :
    BitVec.setWidth (8 * (((1 : Int), (4 : Int)).2.toNat))
      (Sail.BitVec.extractLsb data
        (8 * ((↑(((false, (0 : Nat), true).2.1) : Nat) : Int) + 1) *
          ((1 : Int), (4 : Int)).2 - 1).toNat
        (8 * (↑(((false, (0 : Nat), true).2.1) : Nat) : Int) *
          ((1 : Int), (4 : Int)).2).toNat) = data := by
  simp [Sail.BitVec.extractLsb]
  exact extractLsb_full_width (by omega) data

/-- Collapse Sail's virtual byte-store pipeline once translation, effective
address write, and physical value write have been reduced. -/
theorem vmem_write_addr_byte_store_bridge
    (addr : BitVec 64) (data : BitVec 8) (s : SailState)
    (hcfg : JoltConfig s) (ha : AlignedAccess addr 1)
    (hea :
      mem_write_ea (physaddr.Physaddr addr) 1 false false false s =
        .ok (Ok ()) s)
    (hwrite :
      mem_write_value (physaddr.Physaddr addr) 1 data
        (Store Data) false false false s =
        .ok (Ok true) (state_after_byte_store s addr data)) :
    vmem_write_addr (Virtaddr addr) 1 data
      (Store Data) false false false s =
      .ok (Ok true) (state_after_byte_store s addr data) := by
  unfold vmem_write_addr
  simp only [ha.misalign, Bool.false_eq_true, if_false]
  unfold SailME.run PreSail.PreSailME.run
  have htranslate := translateAddr_store_data_of_joltConfig addr s hcfg
  simp only [ExceptT.mk, ExceptT.run,
    SailME.throw, PreSail.PreSailME.throw, MonadExceptOf.throw,
    misaligned_order, sys_misaligned_order_decreasing,
    bits_of_virtaddr, Sail.assert, PreSail.assert,
    untilFuelM, ha.split]
  norm_num
  unfold untilFuelM.go
  norm_num
  rw [byte_store_loop_data_eq data]
  rw [bitvec_addInt_zero addr]
  simp only [liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.mk, bind, EStateM.bind, EStateM.map,
    Functor.map, htranslate, ExceptT.bind, ExceptT.bindCont, ExceptT.map,
    is_store_conditional, if_true, pure, EStateM.pure, ExceptT.pure]
  have hwrite_int :
      mem_write_value (physaddr.Physaddr addr) (Int.toNat 1) data
        (Store Data) false false false s =
        .ok (Ok true) (state_after_byte_store s addr data) := by
    change mem_write_value (physaddr.Physaddr addr) 1 data
      (Store Data) false false false s =
      .ok (Ok true) (state_after_byte_store s addr data)
    exact hwrite
  simp only [EStateM.bind, EStateM.map, hea, hwrite_int]
  rfl

/-- Collapse Sail's virtual halfword-store pipeline once translation,
effective-address write, and physical value write have been reduced. -/
theorem vmem_write_addr_halfword_store_bridge
    (addr : BitVec 64) (data : BitVec 16) (s : SailState)
    (hcfg : JoltConfig s) (ha : AlignedAccess addr 2)
    (hea :
      mem_write_ea (physaddr.Physaddr addr) 2 false false false s =
        .ok (Ok ()) s)
    (hwrite :
      mem_write_value (physaddr.Physaddr addr) 2 data
        (Store Data) false false false s =
        .ok (Ok true) (state_after_halfword_store s addr data)) :
    vmem_write_addr (Virtaddr addr) 2 data
      (Store Data) false false false s =
      .ok (Ok true) (state_after_halfword_store s addr data) := by
  unfold vmem_write_addr
  simp only [ha.misalign, Bool.false_eq_true, if_false]
  unfold SailME.run PreSail.PreSailME.run
  have htranslate := translateAddr_store_data_of_joltConfig addr s hcfg
  simp only [ExceptT.mk, ExceptT.run,
    SailME.throw, PreSail.PreSailME.throw, MonadExceptOf.throw,
    misaligned_order, sys_misaligned_order_decreasing,
    bits_of_virtaddr, Sail.assert, PreSail.assert,
    untilFuelM, ha.split]
  norm_num
  unfold untilFuelM.go
  norm_num
  rw [halfword_store_loop_data_eq data]
  rw [bitvec_addInt_zero addr]
  simp only [liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.mk, bind, EStateM.bind, EStateM.map,
    Functor.map, htranslate, ExceptT.bind, ExceptT.bindCont, ExceptT.map,
    is_store_conditional, if_true, pure, EStateM.pure, ExceptT.pure]
  have hea_int :
      mem_write_ea (physaddr.Physaddr addr) (Int.toNat 2)
        false false false s =
        .ok (Ok ()) s := by
    change mem_write_ea (physaddr.Physaddr addr) 2 false false false s =
      .ok (Ok ()) s
    exact hea
  have hwrite_int :
      mem_write_value (physaddr.Physaddr addr) (Int.toNat 2) data
        (Store Data) false false false s =
        .ok (Ok true) (state_after_halfword_store s addr data) := by
    change mem_write_value (physaddr.Physaddr addr) 2 data
      (Store Data) false false false s =
      .ok (Ok true) (state_after_halfword_store s addr data)
    exact hwrite
  simp only [EStateM.bind, EStateM.map, hea_int, hwrite_int]
  rfl

/-- Collapse Sail's virtual word-store pipeline once translation, effective
address write, and physical value write have been reduced. -/
theorem vmem_write_addr_word_store_bridge
    (addr : BitVec 64) (data : BitVec 32) (s : SailState)
    (hcfg : JoltConfig s) (ha : AlignedAccess addr 4)
    (hea :
      mem_write_ea (physaddr.Physaddr addr) 4 false false false s =
        .ok (Ok ()) s)
    (hwrite :
      mem_write_value (physaddr.Physaddr addr) 4 data
        (Store Data) false false false s =
        .ok (Ok true) (state_after_word_store s addr data)) :
    vmem_write_addr (Virtaddr addr) 4 data
      (Store Data) false false false s =
      .ok (Ok true) (state_after_word_store s addr data) := by
  unfold vmem_write_addr
  simp only [ha.misalign, Bool.false_eq_true, if_false]
  unfold SailME.run PreSail.PreSailME.run
  have htranslate := translateAddr_store_data_of_joltConfig addr s hcfg
  simp only [ExceptT.mk, ExceptT.run,
    SailME.throw, PreSail.PreSailME.throw, MonadExceptOf.throw,
    misaligned_order, sys_misaligned_order_decreasing,
    bits_of_virtaddr, Sail.assert, PreSail.assert,
    untilFuelM, ha.split]
  norm_num
  unfold untilFuelM.go
  norm_num
  rw [word_store_loop_data_eq data]
  rw [bitvec_addInt_zero addr]
  simp only [liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.mk, bind, EStateM.bind, EStateM.map,
    Functor.map, htranslate, ExceptT.bind, ExceptT.bindCont, ExceptT.map,
    is_store_conditional, if_true, pure, EStateM.pure, ExceptT.pure]
  have hea_int :
      mem_write_ea (physaddr.Physaddr addr) (Int.toNat 4)
        false false false s =
        .ok (Ok ()) s := by
    change mem_write_ea (physaddr.Physaddr addr) 4 false false false s =
      .ok (Ok ()) s
    exact hea
  have hwrite_int :
      mem_write_value (physaddr.Physaddr addr) (Int.toNat 4) data
        (Store Data) false false false s =
        .ok (Ok true) (state_after_word_store s addr data) := by
    change mem_write_value (physaddr.Physaddr addr) 4 data
      (Store Data) false false false s =
      .ok (Ok true) (state_after_word_store s addr data)
    exact hwrite
  simp only [EStateM.bind, EStateM.map, hea_int, hwrite_int]
  rfl

/-- Under exact byte-store memory evidence, virtual byte stores are the
canonical one-byte hashmap update. -/
theorem vmem_write_addr_byte_store_reduces
    (addr : BitVec 64) (data : BitVec 8) (s : SailState)
    (hcfg : JoltConfig s) (hstore : FlatStoreMem addr 1 s) :
    vmem_write_addr (Virtaddr addr) 1 data
      (Store Data) false false false s =
      .ok (Ok true) (state_after_byte_store s addr data) :=
  vmem_write_addr_byte_store_bridge addr data s hcfg
    (aligned_access_1 addr)
    (mem_write_ea_plain_store_ok addr 1 s)
    (mem_write_value_byte_eq_state_after_byte_store addr data s hcfg hstore)

/-- Under exact aligned halfword-store memory evidence, virtual halfword
stores are the canonical two-byte hashmap update. -/
theorem vmem_write_addr_halfword_store_reduces
    (addr : BitVec 64) (data : BitVec 16) (s : SailState)
    (hcfg : JoltConfig s)
    (halign : addr &&& (1 : BitVec 64) = 0)
    (hstore : FlatStoreMem addr 2 s) :
    vmem_write_addr (Virtaddr addr) 2 data
      (Store Data) false false false s =
      .ok (Ok true) (state_after_halfword_store s addr data) :=
  vmem_write_addr_halfword_store_bridge addr data s hcfg
    (halfword_store_aligned_access addr halign)
    (mem_write_ea_plain_store_ok addr 2 s)
    (mem_write_value_halfword_eq_state_after_halfword_store
      addr data s hcfg hstore)

/-- Under exact aligned word-store memory evidence, virtual word stores are
the canonical four-byte hashmap update. -/
theorem vmem_write_addr_word_store_reduces
    (addr : BitVec 64) (data : BitVec 32) (s : SailState)
    (hcfg : JoltConfig s)
    (halign : addr &&& (3 : BitVec 64) = 0)
    (hstore : FlatStoreMem addr 4 s) :
    vmem_write_addr (Virtaddr addr) 4 data
      (Store Data) false false false s =
      .ok (Ok true) (state_after_word_store s addr data) :=
  vmem_write_addr_word_store_bridge addr data s hcfg
    (word_store_aligned_access addr halign)
    (mem_write_ea_plain_store_ok addr 4 s)
    (mem_write_value_word_eq_state_after_word_store addr data s hcfg hstore)

/-- The Jolt-side final dword store for a store expansion reduces from internal
`StoreMemoryContext`. -/
theorem vmem_write_addr_store_dword_base_reduces
    {sailAddr : BitVec 64} {sailWidth : Nat}
    (val : BitVec 64) (imm : BitVec 12) (data : BitVec 64)
    (s : SailState) (hcfg : JoltConfig s)
    (hmem : StoreMemoryContext
      sailAddr (compute_aligned_dword_base_address val imm) sailWidth s) :
    vmem_write_addr
      (Virtaddr (compute_aligned_dword_base_address val imm)) 8 data
      (Store Data) false false false s =
      .ok (Ok true)
        (state_after_dword_store s
          (compute_aligned_dword_base_address val imm) data) :=
  vmem_write_addr_dword_store_reduces
    (compute_aligned_dword_base_address val imm) data s hcfg
    (store_dword_base_aligned_access val imm)
    (hmem.jolt_store_mem).pmp
    (hmem.jolt_store_mem).mmio

/-- Register-addressed byte stores reduce through exact store memory evidence
for the effective address. -/
theorem vmem_write_byte_store_reduces (imm : BitVec 12) (rs1 : regidx)
    (s : SailState) (hcfg : JoltConfig s)
    (v : BitVec 64) (hrx : rX_bits rs1 s = .ok v s)
    (data : BitVec 8)
    (hstore : FlatStoreMem (load_effective_address v imm) 1 s) :
    vmem_write rs1 (sign_extend (m := 64) imm) 1 data
      (Store Data) false false false s =
    .ok (Ok true)
      (state_after_byte_store s (load_effective_address v imm) data) := by
  unfold load_effective_address
  unfold vmem_write
  unfold SailME.run PreSail.PreSailME.run
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    ExceptT.pure, ExceptT.lift,
    MonadLift.monadLift, liftM, monadLift, Functor.map,
    ext_data_get_addr, hrx,
    vmem_write_addr_byte_store_reduces _ data s hcfg hstore]

/-- Register-addressed halfword stores reduce through exact store memory evidence
for the aligned effective address. -/
theorem vmem_write_halfword_store_reduces (imm : BitVec 12) (rs1 : regidx)
    (s : SailState) (hcfg : JoltConfig s)
    (v : BitVec 64) (hrx : rX_bits rs1 s = .ok v s)
    (data : BitVec 16)
    (halign : load_effective_address v imm &&& (1 : BitVec 64) = 0)
    (hstore : FlatStoreMem (load_effective_address v imm) 2 s) :
    vmem_write rs1 (sign_extend (m := 64) imm) 2 data
      (Store Data) false false false s =
    .ok (Ok true)
      (state_after_halfword_store s (load_effective_address v imm) data) := by
  unfold load_effective_address at halign hstore ⊢
  unfold vmem_write
  unfold SailME.run PreSail.PreSailME.run
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    ExceptT.pure, ExceptT.lift,
    MonadLift.monadLift, liftM, monadLift, Functor.map,
    ext_data_get_addr, hrx,
    vmem_write_addr_halfword_store_reduces _ data s hcfg halign hstore]

/-- Register-addressed word stores reduce through exact store memory evidence
for the aligned effective address. -/
theorem vmem_write_word_store_reduces (imm : BitVec 12) (rs1 : regidx)
    (s : SailState) (hcfg : JoltConfig s)
    (v : BitVec 64) (hrx : rX_bits rs1 s = .ok v s)
    (data : BitVec 32)
    (halign : load_effective_address v imm &&& (3 : BitVec 64) = 0)
    (hstore : FlatStoreMem (load_effective_address v imm) 4 s) :
    vmem_write rs1 (sign_extend (m := 64) imm) 4 data
      (Store Data) false false false s =
    .ok (Ok true)
      (state_after_word_store s (load_effective_address v imm) data) := by
  unfold load_effective_address at halign hstore ⊢
  unfold vmem_write
  unfold SailME.run PreSail.PreSailME.run
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    ExceptT.pure, ExceptT.lift,
    MonadLift.monadLift, liftM, monadLift, Functor.map,
    ext_data_get_addr, hrx,
    vmem_write_addr_word_store_reduces _ data s hcfg halign hstore]

end StoreFamily

end
