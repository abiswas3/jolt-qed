import JoltBytecode.InstructionEquivalence.AtomicFamily.Common
import JoltBytecode.InstructionEquivalence.LoadDefUtils
import JoltBytecode.JoltISA.Semantics.Lemmas
import JoltBytecode.JoltISA.Semantics.Instructions.ADDI
import JoltBytecode.JoltISA.Semantics.Instructions.SD
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualAssertAlignment
import JoltBytecode.JoltISA.Semantics.RegisterOps
import JoltBytecode.InstructionEquivalence.Memory.WriteReasoning

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace AtomicFamily

/-- Canonical Sail state after aligned `AMOSWAP.D`.

The atomic swap reads the old dword at `addr`, writes `rs2Val` to that dword,
then writes the old dword value into `rd`. -/
abbrev amoswapdFinalSailState
    (rd : regidx) (s : SailState) (addr rs2Val : BitVec 64) : SailState :=
  stateAfterWrite
    (state_after_dword_store s addr rs2Val)
    rd
    (loaded_dword_at s addr)

/-- An 8-byte aligned 64-bit address has room for the full dword window. -/
theorem amoswapd_aligned_no_ovf (addr : BitVec 64)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    addr.toNat + 7 < 2 ^ 64 := by
  exact aligned_addr_no_ovf_of_align addr h_align

/-- `LD old, 0(rs1)` reads the old dword into the AMO scratch register and
leaves the Sail state unchanged. -/
theorem amoswapd_ld_old_run
    (rs1 : regidx) (js : SailJoltState) (addr oldVal : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hload :
      vmem_read_addr (Virtaddr addr) 0 8 (Load Data) false false false js.sail =
        .ok (Ok oldVal) js.sail) :
    ∃ js_afterLoad : SailJoltState,
      (JoltISA.execInstr
        (.LD (.vreg JoltISA.amoOldVReg) (.xreg rs1) (0 : BitVec 12))).run js =
        .ok RETIRE_SUCCESS js_afterLoad ∧
      js_afterLoad.sail = js.sail ∧
      js_afterLoad.vregs JoltISA.amoOldVReg = oldVal := by
  let js_afterLoad : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.amoOldVReg then oldVal else js.vregs r }
  refine ⟨js_afterLoad, ?_, ?_, ?_⟩
  · have hsext0 :
        sign_extend (m := 64) (0 : BitVec 12) = (0 : BitVec 64) := by
      decide
    have haddr0 :
        addr + sign_extend (m := 64) (0 : BitVec 12) = addr := by
      rw [hsext0]
      bv_decide
    have hread :
        vmem_read_addr
          (Virtaddr (addr + sign_extend (m := 64) (0 : BitVec 12))) 0 8
          (Load Data) false false false js.sail =
          .ok (Ok oldVal) js.sail := by
      rw [haddr0]
      exact hload
    exact
      JoltISA.ld_run_vreg_xreg_from_memory_read
        JoltISA.amoOldVReg rs1 (0 : BitVec 12) js addr oldVal hrs1 hread
  · rfl
  · change (if JoltISA.amoOldVReg = JoltISA.amoOldVReg then oldVal
        else js.vregs JoltISA.amoOldVReg) = oldVal
    rw [if_pos rfl]

/-- `SD rs2, 0(rs1)` writes the new dword and preserves virtual registers. -/
theorem amoswapd_sd_new_run
    (rs2 rs1 : regidx) (js_afterLoad : SailJoltState)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js_afterLoad.sail = .ok addr js_afterLoad.sail)
    (hrs2 : rX_bits rs2 js_afterLoad.sail = .ok rs2Val js_afterLoad.sail)
    (hwrite :
      vmem_write_addr (Virtaddr addr) 8 rs2Val
        (Store Data) false false false js_afterLoad.sail =
        .ok (Ok true)
          (state_after_dword_store js_afterLoad.sail addr rs2Val)) :
    ∃ js_afterStore : SailJoltState,
      (JoltISA.execInstr
        (.SD (.xreg rs1) (.xreg rs2) (0 : BitVec 12))).run js_afterLoad =
        .ok RETIRE_SUCCESS js_afterStore ∧
      js_afterStore.sail =
        state_after_dword_store js_afterLoad.sail addr rs2Val ∧
      js_afterStore.vregs = js_afterLoad.vregs := by
  let js_afterStore : SailJoltState :=
    { sail := state_after_dword_store js_afterLoad.sail addr rs2Val
      vregs := js_afterLoad.vregs }
  refine ⟨js_afterStore, ?_, ?_, ?_⟩
  · have hsext0 :
        sign_extend (m := 64) (0 : BitVec 12) = (0 : BitVec 64) := by
      decide
    have haddr0 :
        addr + sign_extend (m := 64) (0 : BitVec 12) = addr := by
      rw [hsext0]
      bv_decide
    have hwrite' :
        vmem_write_addr
          (Virtaddr (addr + sign_extend (m := 64) (0 : BitVec 12))) 8
          rs2Val (Store Data) false false false js_afterLoad.sail =
          .ok (Ok true)
            (state_after_dword_store js_afterLoad.sail addr rs2Val) := by
      rw [haddr0]
      exact hwrite
    exact
      JoltISA.execInstr_sd_xreg_xreg_run_of_write
        rs1 rs2 (0 : BitVec 12) js_afterLoad addr rs2Val
        (state_after_dword_store js_afterLoad.sail addr rs2Val)
        hrs1 hrs2 hwrite'
  · rfl
  · rfl

/-- `ADDI rd, old, 0` writes the old dword value back to `rd`. -/
theorem amoswapd_addi_writeback_old_run
    (rd : regidx) (js_afterStore : SailJoltState) (oldVal : BitVec 64)
    (hold : js_afterStore.vregs JoltISA.amoOldVReg = oldVal) :
    ∃ js_afterWrite : SailJoltState,
      (JoltISA.execInstr
        (.ADDI (.xreg rd) (.vreg JoltISA.amoOldVReg) (0 : BitVec 12))).run
          js_afterStore =
        .ok RETIRE_SUCCESS js_afterWrite ∧
      js_afterWrite.sail = stateAfterWrite js_afterStore.sail rd oldVal ∧
      js_afterWrite.vregs = js_afterStore.vregs := by
  obtain ⟨s', hw⟩ := wX_shape rd oldVal js_afterStore.sail
  let js_afterWrite : SailJoltState :=
    { sail := s'
      vregs := js_afterStore.vregs }
  refine ⟨js_afterWrite, ?_, ?_, ?_⟩
  · have hsext0 :
        sign_extend (m := 64) (0 : BitVec 12) = (0 : BitVec 64) := by
      decide
    have hvalue0 :
        js_afterStore.vregs JoltISA.amoOldVReg +
          sign_extend (m := 64) (0 : BitVec 12) = oldVal := by
      rw [hold, hsext0]
      bv_decide
    have hw' :
        wX_bits rd
          (js_afterStore.vregs JoltISA.amoOldVReg +
            sign_extend (m := 64) (0 : BitVec 12))
          js_afterStore.sail = .ok () s' := by
      rw [hvalue0]
      exact hw
    exact
      JoltISA.addi_run_xreg_vreg
        rd JoltISA.amoOldVReg (0 : BitVec 12) js_afterStore s' hw'
  · exact wX_bits_eq_stateAfterWrite rd oldVal js_afterStore.sail s' hw
  · rfl

/-- Jolt-side aligned concrete execution for `AMOSWAP.D`.

This is the intended composition point for the three instruction lemmas above:
load old dword, store `rs2`, then write old dword to `rd`. -/
theorem amoswapdProgram_concrete_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_mem : AmoMemoryAssumptions amoop.AMOSWAP 8 addr addr js.sail)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    ∃ jsf : SailJoltState,
      (JoltISA.execProgram (JoltISA.amoswapdProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail = amoswapdFinalSailState rd js.sail addr rs2Val := by
  have hsext0 :
      sign_extend (m := 64) (0 : BitVec 12) = (0 : BitVec 64) := by
    decide
  have haddr0 :
      addr + sign_extend (m := 64) (0 : BitVec 12) = addr := by
    rw [hsext0]
    bv_decide
  have h_align0 :
      (addr + sign_extend (m := 64) (0 : BitVec 12)) &&& (7 : BitVec 64) = 0 := by
    rw [haddr0]
    exact h_align
  have hassert :
      (JoltISA.execInstr
        (.VirtualAssertDwordAlignment rs1 (0 : BitVec 12)
          (ExceptionType.E_SAMO_Addr_Align ()))).run js =
        .ok RETIRE_SUCCESS js := by
    exact
      JoltISA.virtual_assert_dword_alignment_run_aligned
        rs1 (0 : BitVec 12) (ExceptionType.E_SAMO_Addr_Align ())
        js addr hrs1 h_align0
  have haligned : AlignedDwordAccess addr :=
    { misalign := access_misaligned_8_aligned_false addr h_align
      split := split_misaligned_aligned_8 addr h_align
      align := h_align
      no_ovf := amoswapd_aligned_no_ovf addr h_align }
  have hload_assumptions : DwordLoadAssumptions addr js.sail :=
    dwordLoadAssumptions_of_aligned_phys addr js.sail haligned
      (AmoMemoryAssumptions.jolt_load_mem h_mem)
  have hload :
      vmem_read_addr (Virtaddr addr) 0 8 (Load Data) false false false js.sail =
        .ok (Ok (loaded_dword_at js.sail addr)) js.sail :=
    aligned_dword_vmem_read_reduces addr js.sail hcfg hload_assumptions
  obtain ⟨js_afterLoad, hld, hld_sail, hld_old⟩ :=
    amoswapd_ld_old_run rs1 js addr (loaded_dword_at js.sail addr) hrs1 hload
  have hwrite :
      vmem_write_addr (Virtaddr addr) 8 rs2Val
        (Store Data) false false false js.sail =
        .ok (Ok true) (state_after_dword_store js.sail addr rs2Val) :=
    vmem_write_addr_dword_store_reduces addr rs2Val js.sail hcfg
      haligned.toAlignedAccess
      (AmoMemoryAssumptions.jolt_store_mem h_mem).pmp
      (AmoMemoryAssumptions.jolt_store_mem h_mem).mmio
  have hrs1_afterLoad :
      rX_bits rs1 js_afterLoad.sail = .ok addr js_afterLoad.sail := by
    rw [hld_sail]
    exact hrs1
  have hrs2_afterLoad :
      rX_bits rs2 js_afterLoad.sail = .ok rs2Val js_afterLoad.sail := by
    rw [hld_sail]
    exact hrs2
  have hwrite_afterLoad :
      vmem_write_addr (Virtaddr addr) 8 rs2Val
        (Store Data) false false false js_afterLoad.sail =
        .ok (Ok true)
          (state_after_dword_store js_afterLoad.sail addr rs2Val) := by
    rw [hld_sail]
    exact hwrite
  obtain ⟨js_afterStore, hsd, hsd_sail, hsd_vregs⟩ :=
    amoswapd_sd_new_run rs2 rs1 js_afterLoad addr rs2Val
      hrs1_afterLoad hrs2_afterLoad hwrite_afterLoad
  have hold_afterStore :
      js_afterStore.vregs JoltISA.amoOldVReg =
        loaded_dword_at js.sail addr := by
    rw [hsd_vregs]
    exact hld_old
  obtain ⟨js_afterWrite, haddi, haddi_sail, _haddi_vregs⟩ :=
    amoswapd_addi_writeback_old_run rd js_afterStore
      (loaded_dword_at js.sail addr) hold_afterStore
  refine ⟨js_afterWrite, ?_, ?_⟩
  · unfold JoltISA.amoswapdProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js hassert]
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterLoad hld]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterLoad js_afterStore hsd]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterStore js_afterWrite haddi]
    rfl
  · rw [haddi_sail, hsd_sail, hld_sail]

/-- An 8-byte aligned virtual address satisfies Sail's aligned-address test. -/
theorem amoswapd_is_aligned_vaddr_true (addr : BitVec 64)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    is_aligned_vaddr (Virtaddr addr) 8 = true := by
  unfold is_aligned_vaddr Sail.BitVec.toNatInt
  have h_mod : addr.toNat % 8 = 0 := by
    have h := congrArg BitVec.toNat h_align
    rw [BitVec.toNat_and] at h
    have h7 : (7 : BitVec 64).toNat = 7 := by decide
    have h0 : (0 : BitVec 64).toNat = 0 := by decide
    rw [h7, h0,
      show (7 : Nat) = 2^3 - 1 from by norm_num,
      Nat.and_two_pow_sub_one_eq_mod] at h
    exact h
  simp only [Int.tmod]
  change ((Int.ofNat (addr.toNat % 8)) == (0 : Int)) = true
  have h_int : Int.ofNat (addr.toNat % 8) = 0 := by
    rw [h_mod]
    rfl
  rw [h_int]
  rfl

/-- An 8-byte aligned physical address satisfies Sail's aligned-address test. -/
theorem amoswapd_is_aligned_paddr_true (addr : BitVec 64)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    is_aligned_paddr (physaddr.Physaddr addr) 8 = true := by
  unfold is_aligned_paddr Sail.BitVec.toNatInt
  have h_mod : addr.toNat % 8 = 0 := by
    have h := congrArg BitVec.toNat h_align
    rw [BitVec.toNat_and] at h
    have h7 : (7 : BitVec 64).toNat = 7 := by decide
    have h0 : (0 : BitVec 64).toNat = 0 := by decide
    rw [h7, h0,
      show (7 : Nat) = 2^3 - 1 from by norm_num,
      Nat.and_two_pow_sub_one_eq_mod] at h
    exact h
  simp only [Int.tmod]
  change ((Int.ofNat (addr.toNat % 8)) == (0 : Int)) = true
  have h_int : Int.ofNat (addr.toNat % 8) = 0 := by
    rw [h_mod]
    rfl
  rw [h_int]
  rfl

/-- Sail RAM reads for AMO reserved dword reads return the canonical hashmap
dword value. -/
theorem amoswapd_read_ram_reserved_eq_loaded_dword
    (addr : BitVec 64) (s : SailState)
    (h_pop : ∀ a : Nat, s.mem.get? a ≠ none)
    (h_no_ovf : addr.toNat + 7 < 2 ^ 64) :
    LeanRV64D.Functions.read_ram read_kind.Read_RISCV_reserved
      (physaddr.Physaddr addr) 8 false s =
    .ok (loaded_dword_at s addr, default_meta) s := by
  dsimp [LeanRV64D.Functions.read_ram,
    Sail.ConcurrencyInterfaceV1.sail_mem_read,
    PreSail.ConcurrencyInterfaceV1.sail_mem_read,
    default_meta]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  rw [readBytes_8_eq_loaded_dword addr s h_pop h_no_ovf]
  simp only [EStateM.pure]

theorem amoswapd_checked_mem_read_eq_loaded_dword
    (addr : BitVec 64) (s : SailState)
    (h_pop : ∀ a : Nat, s.mem.get? a ≠ none)
    (h_no_ovf : addr.toNat + 7 < 2 ^ 64)
    (hfm : FlatAtomicMem amoop.AMOSWAP addr 8 s) :
    checked_mem_read (Atomic (amoop.AMOSWAP, Data, Data)) Privilege.Machine
      (physaddr.Physaddr addr) 8 false false true false s =
    .ok (Ok (loaded_dword_at s addr, default_meta)) s := by
  unfold checked_mem_read
  simp only [bind, EStateM.bind, pure, EStateM.pure, hfm.pmp, hfm.readable,
    Bool.false_eq_true, if_false]
  unfold read_kind_of_flags
  simp only [pure, EStateM.pure]
  rw [amoswapd_read_ram_reserved_eq_loaded_dword addr s h_pop h_no_ovf]

theorem amoswapd_mem_read_eq_loaded_dword
    (addr : BitVec 64) (s : SailState)
    (hcfg : JoltConfig s)
    (h_no_ovf : addr.toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (7 : BitVec 64) = 0)
    (hfm : FlatAtomicMem amoop.AMOSWAP addr 8 s) :
    mem_read (Atomic (amoop.AMOSWAP, Data, Data))
      (physaddr.Physaddr addr) 8 false false true s =
    .ok (Ok (loaded_dword_at s addr)) s := by
  obtain ⟨mval, h_ms_regs, h_mprv⟩ := hcfg.mstatus_ok
  have h_ms_read := readReg_eq Register.mstatus s mval h_ms_regs
  have h_priv := readReg_eq Register.cur_privilege s Privilege.Machine hcfg.machine_mode
  have h_paddr_aligned := amoswapd_is_aligned_paddr_true addr h_align
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
  rw [amoswapd_checked_mem_read_eq_loaded_dword
    addr s hcfg.mem_populated h_no_ovf hfm]
  rfl

theorem amoswapd_mem_write_ea_ok
    (addr : BitVec 64) (s : SailState)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    mem_write_ea (physaddr.Physaddr addr) 8 false false true s =
      .ok (Ok ()) s := by
  have h_paddr_aligned := amoswapd_is_aligned_paddr_true addr h_align
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

theorem amoswapd_write_ram_conditional_eq_state_after_dword_store
    (addr data : BitVec 64) (s : SailState) :
    LeanRV64D.Functions.write_ram write_kind.Write_RISCV_conditional
      (physaddr.Physaddr addr) 8 data default_meta s =
    .ok true (state_after_dword_store s addr data) := by
  dsimp [LeanRV64D.Functions.write_ram,
    Sail.ConcurrencyInterfaceV1.sail_mem_write,
    PreSail.ConcurrencyInterfaceV1.sail_mem_write,
    PreSail.writeBytes,
    PreSail.writeByte,
    state_after_dword_store,
    dword_byte,
    default_meta,
    __WriteRAM_Meta]
  rfl

theorem amoswapd_mem_write_value_eq_state_after_dword_store
    (addr data : BitVec 64) (s : SailState)
    (hcfg : JoltConfig s)
    (h_align : addr &&& (7 : BitVec 64) = 0)
    (hfm : FlatAtomicMem amoop.AMOSWAP addr 8 s) :
    mem_write_value (physaddr.Physaddr addr) 8 data
      (Atomic (amoop.AMOSWAP, Data, Data)) false false true s =
    .ok (Ok true) (state_after_dword_store s addr data) := by
  obtain ⟨mval, h_ms_regs, h_mprv⟩ := hcfg.mstatus_ok
  have h_ms_read := readReg_eq Register.mstatus s mval h_ms_regs
  have h_priv := readReg_eq Register.cur_privilege s Privilege.Machine hcfg.machine_mode
  have h_paddr_aligned := amoswapd_is_aligned_paddr_true addr h_align
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
        (phys_access_check (Atomic (amoop.AMOSWAP, Data, Data)) Privilege.Machine
          (physaddr.Physaddr addr) 8 true)
        (fun result =>
          match result with
          | some e => EStateM.pure (Err e)
          | none =>
              EStateM.bind
                (within_mmio_writable (physaddr.Physaddr addr) 8)
                (fun isMmio =>
                  if isMmio = true then
                    mmio_write (physaddr.Physaddr addr) 8 data
                  else
                    EStateM.bind
                      (write_kind_of_flags false false true)
                      (fun wk =>
                        EStateM.bind
                          (LeanRV64D.Functions.write_ram wk
                            (physaddr.Physaddr addr) 8 data default_meta)
                          (fun ok => EStateM.pure (Ok ok))))))
      (fun result => EStateM.pure result)) s =
    .ok (Ok true) (state_after_dword_store s addr data)
  simp only [EStateM.bind, hfm.pmp]
  simp only [hfm.writable]
  simp only [Bool.false_eq_true, if_false]
  unfold write_kind_of_flags
  simp only [EStateM.bind, pure, EStateM.pure]
  rw [amoswapd_write_ram_conditional_eq_state_after_dword_store addr data s]

/-- Sail-side aligned concrete execution for native `AMOSWAP.D`. -/
theorem execute_AMOSWAPD_reduces_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryAssumptions amoop.AMOSWAP 8 addr addr js.sail)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    (execute_AMO amoop.AMOSWAP false false rs2 rs1 8 rd).run js.sail =
      .ok RETIRE_SUCCESS (amoswapdFinalSailState rd js.sail addr rs2Val) := by
  let oldVal := loaded_dword_at js.sail addr
  let storeState := state_after_dword_store js.sail addr rs2Val
  obtain ⟨rdVal, hrd_read⟩ := hrd
  obtain ⟨writebackState, hwriteback⟩ := wX_shape rd oldVal storeState
  have hwriteback_state :
      writebackState = amoswapdFinalSailState rd js.sail addr rs2Val := by
    exact wX_bits_eq_stateAfterWrite rd oldVal storeState writebackState hwriteback
  have haddr0 : addr + zeros (n := 64) = addr := by
    unfold zeros
    exact BitVec.add_zero addr
  have h_vaddr_aligned := amoswapd_is_aligned_vaddr_true addr h_align
  have htranslate :=
    translateAddr_atomic_data_of_joltConfig amoop.AMOSWAP addr js.sail hcfg
  have hea := amoswapd_mem_write_ea_ok addr js.sail h_align
  have hread := amoswapd_mem_read_eq_loaded_dword addr js.sail hcfg
    (amoswapd_aligned_no_ovf addr h_align) h_align h_mem.sail_atomic_mem
  have hsign_result : sign_extend (m := 8 * 8) rs2Val = rs2Val := by
    unfold sign_extend Sail.BitVec.signExtend
    bv_decide
  have htrunc_rs2 :
      trunc (m := (((8 : Nat) : Int) * (8 : Int)).toNat) rs2Val =
        rs2Val := by
    unfold trunc Sail.BitVec.truncate
    rfl
  have hwrite_value :
      mem_write_value (physaddr.Physaddr addr) 8
        (sign_extend (m := ((8 : Int) * ((8 : Nat) : Int)).toNat)
          (show BitVec (8 * 8) from
            trunc (m := (((8 : Nat) : Int) * (8 : Int)).toNat) rs2Val))
        (Atomic (amoop.AMOSWAP, Data, Data)) false false true js.sail =
      .ok (Ok true) storeState := by
    rw [htrunc_rs2]
    change
      mem_write_value (physaddr.Physaddr addr) 8
        (sign_extend (m := 8 * 8) rs2Val)
        (Atomic (amoop.AMOSWAP, Data, Data)) false false true js.sail =
      .ok (Ok true) storeState
    rw [hsign_result]
    exact amoswapd_mem_write_value_eq_state_after_dword_store
      addr rs2Val js.sail hcfg h_align h_mem.sail_atomic_mem
  have hloaded_width : BitVec.setWidth (8 * 8) oldVal = oldVal := by
    rfl
  have hsign_loaded : sign_extend (m := 64) oldVal = oldVal := by
    unfold sign_extend Sail.BitVec.signExtend
    bv_decide
  have hwriteback_loaded :
      wX_bits rd
        (sign_extend (m := 64) (BitVec.setWidth (8 * 8) oldVal))
        storeState =
      .ok () writebackState := by
    rw [hloaded_width]
    rw [hsign_loaded]
    exact hwriteback
  have hwriteback_loaded_direct :
      wX_bits rd
        (sign_extend (m := 64)
          (BitVec.setWidth (8 * 8) (loaded_dword_at js.sail addr)))
        storeState =
      .ok () writebackState := by
    exact hwriteback_loaded
  have hwidth_assert :
      (8 ≤b (((8 : Nat) : Int) * (2 : Int)).toNat) = true := by
    decide
  have hwidth8 : (8 ≤b (8 : Nat)) = true := by
    decide
  have hcas_check : decide (amoop.AMOSWAP.ctorIdx = amoop.AMOCAS.ctorIdx) = false := by
    decide
  unfold execute_AMO
  simp only [bind, pure]
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  simp only [hwidth_assert, PreSail.assert, pure, EStateM.run, if_true]
  unfold SailME.run PreSail.PreSailME.run
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    ExceptT.pure, ExceptT.lift, MonadLift.monadLift, liftM, monadLift,
    Functor.map, SailME.throw, PreSail.PreSailME.throw,
    MonadExceptOf.throw, ext_data_get_addr, hrs1, haddr0,
    h_vaddr_aligned, LeanRV64D.Functions.not, Bool.not_true,
    Bool.false_eq_true, if_false, if_true, htranslate, hwidth8, hrs2,
    hea, hread, hrd_read, hcas_check, Bool.false_and,
    instBEqAmoop.beq, BEq.beq]
  rw [hwrite_value]
  simp only [EStateM.bind, EStateM.map, ExceptT.bindCont, EStateM.pure,
    hwriteback_loaded_direct, hwriteback_state]

/-- Jolt-side misaligned execution for `AMOSWAP.D`.

The AMO expansion performs the leading dword alignment check with Sail's
store/AMO alignment exception, so the body is not executed on this path. -/
theorem amoswapdProgram_concrete_misaligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (addr : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (h_align : addr &&& (7 : BitVec 64) ≠ 0) :
    (JoltISA.execProgram (JoltISA.amoswapdProgram rs2 rs1 rd)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr addr, ExceptionType.E_SAMO_Addr_Align ())) js := by
  let rest : JoltISA.Program :=
    .instr (.LD (.vreg JoltISA.amoOldVReg) (.xreg rs1) (0 : BitVec 12)) <|
    .instr (.SD (.xreg rs1) (.xreg rs2) (0 : BitVec 12)) <|
    .instr (.ADDI (.xreg rd) (.vreg JoltISA.amoOldVReg) (0 : BitVec 12)) <|
    .done RETIRE_SUCCESS
  let e := (Virtaddr addr, ExceptionType.E_SAMO_Addr_Align ())
  have hassert :
      (JoltISA.execInstr
        (.VirtualAssertDwordAlignment rs1 (0 : BitVec 12)
          (ExceptionType.E_SAMO_Addr_Align ()))).run js =
        .ok (ExecutionResult.Memory_Exception e) js := by
    have hsext0 :
        sign_extend (m := 64) (0 : BitVec 12) = (0 : BitVec 64) := by
      decide
    have haddr0 :
        addr + sign_extend (m := 64) (0 : BitVec 12) = addr := by
      rw [hsext0]
      bv_decide
    have h_align0 :
        (addr + sign_extend (m := 64) (0 : BitVec 12)) &&& (7 : BitVec 64) ≠ 0 := by
      rw [haddr0]
      exact h_align
    have hrun :=
      JoltISA.virtual_assert_dword_alignment_run_misaligned rs1 (0 : BitVec 12)
        (ExceptionType.E_SAMO_Addr_Align ()) js addr hrs1 h_align0
    rw [haddr0] at hrun
    change
      (JoltISA.execInstr
        (.VirtualAssertDwordAlignment rs1 (0 : BitVec 12)
          (ExceptionType.E_SAMO_Addr_Align ()))).run js =
        .ok (ExecutionResult.Memory_Exception e) js
    exact hrun
  unfold JoltISA.amoswapdProgram
  exact
    JoltISA.execProgram_instr_run_memory_exception
      (.VirtualAssertDwordAlignment rs1 (0 : BitVec 12)
        (ExceptionType.E_SAMO_Addr_Align ()))
      rest js js e hassert

/-- Sail-side misaligned execution for native `AMOSWAP.D`. -/
theorem execute_AMOSWAPD_misaligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_align : addr &&& (7 : BitVec 64) ≠ 0) :
    (execute_AMO amoop.AMOSWAP false false rs2 rs1 8 rd).run js.sail =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr addr, ExceptionType.E_SAMO_Addr_Align ())) js.sail := by
  unfold execute_AMO
  simp only [bind, pure]
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  have hwidth_assert :
      (8 ≤b (((8 : Nat) : Int) * (2 : Int)).toNat) = true := by
    decide
  simp only [hwidth_assert, PreSail.assert, pure, EStateM.run, if_true]
  unfold SailME.run PreSail.PreSailME.run
  have haddr0 : addr + zeros (n := 64) = addr := by
    unfold zeros
    exact BitVec.add_zero addr
  have hnot_aligned :
      is_aligned_vaddr (Virtaddr addr) 8 = false :=
    is_aligned_vaddr_8_unaligned_false addr h_align
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    ExceptT.pure, ExceptT.lift, MonadLift.monadLift, liftM, monadLift,
    Functor.map, ext_data_get_addr, hrs1, haddr0, hnot_aligned,
    LeanRV64D.Functions.not, Bool.not_false, if_true]

theorem amoswapdProgram_eq_sail_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryAssumptions amoop.AMOSWAP 8 addr addr js.sail)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoswapdProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOSWAP false false rs2 rs1 8 rd).run js.sail := by
  rcases amoswapdProgram_concrete_aligned
      rs2 rs1 rd js hcfg addr rs2Val hrs1 hrs2 h_mem h_align with
    ⟨jsf, hjolt, hjolt_sail⟩
  have hsail := execute_AMOSWAPD_reduces_aligned
    rs2 rs1 rd js hcfg addr rs2Val hrs1 hrs2 hrd h_mem h_align
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail, hsail]

/-- Misaligned public branch for `AMOSWAP.D`. -/
theorem amoswapdProgram_eq_sail_misaligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_align : addr &&& (7 : BitVec 64) ≠ 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoswapdProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOSWAP false false rs2 rs1 8 rd).run js.sail := by
  have hjolt := amoswapdProgram_concrete_misaligned
    rs2 rs1 rd js addr hrs1 h_align
  have hsail := execute_AMOSWAPD_misaligned
    rs2 rs1 rd js hcfg addr rs2Val hrs1 hrs2 h_align
  rw [hjolt]
  simp only [projectResult, project]
  symm
  exact hsail

/-- Main public theorem for `AMOSWAP.D`.

The outer theorem mirrors LoadFamily: it exposes no alignment hypothesis and
dispatches on the exact predicate checked by the AMO dword access. -/
theorem amoswapdProgram_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryAssumptions amoop.AMOSWAP 8 addr addr js.sail) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoswapdProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOSWAP false false rs2 rs1 8 rd).run js.sail := by
  by_cases h_align : addr &&& (7 : BitVec 64) = 0
  · exact amoswapdProgram_eq_sail_aligned
      rs2 rs1 rd js hcfg addr rs2Val hrs1 hrs2 hrd h_mem h_align
  · exact amoswapdProgram_eq_sail_misaligned
      rs2 rs1 rd js hcfg addr rs2Val hrs1 hrs2 h_align

end AtomicFamily

end
