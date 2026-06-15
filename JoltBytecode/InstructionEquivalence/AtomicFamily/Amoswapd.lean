import JoltBytecode.InstructionEquivalence.AtomicFamily.Dword

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
  amoDwordFinalSailState rd s addr rs2Val

/-- An 8-byte aligned 64-bit address has room for the full dword window. -/
theorem amoswapd_aligned_no_ovf (addr : BitVec 64)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    addr.toNat + 7 < 2 ^ 64 := by
  exact amo_dword_aligned_no_ovf addr h_align

/-- `LD old, 0(rs1)` reads the old dword into the AMO scratch register and
leaves the Sail state unchanged. -/
theorem amoswapd_ld_old_run
    (rs1 : regidx) (js : SailJoltState) (addr oldVal : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (h_align : addr &&& (7 : BitVec 64) = 0)
    (hload :
      vmem_read_addr (Virtaddr addr) 0 8 (Load Data) false false false js.sail =
        .ok (Ok oldVal) js.sail) :
    ∃ js_afterLoad : SailJoltState,
      (JoltISA.execInstr
        (.LD (.vreg JoltISA.amoOldVReg) (.xreg rs1) (0 : BitVec 12))).run js =
        .ok RETIRE_SUCCESS js_afterLoad ∧
      js_afterLoad.sail = js.sail ∧
      js_afterLoad.vregs JoltISA.amoOldVReg = oldVal := by
  exact amo_dword_ld_old_run rs1 js addr oldVal hrs1 h_align hload

/-- `SD rs2, 0(rs1)` writes the new dword and preserves virtual registers. -/
theorem amoswapd_sd_new_run
    (rs2 rs1 : regidx) (js_afterLoad : SailJoltState)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js_afterLoad.sail = .ok addr js_afterLoad.sail)
    (hrs2 : rX_bits rs2 js_afterLoad.sail = .ok rs2Val js_afterLoad.sail)
    (h_align : addr &&& (7 : BitVec 64) = 0)
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
  exact
    amo_dword_sd_result_run rs2 rs1 js_afterLoad addr rs2Val
      hrs1 hrs2 h_align hwrite

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
  exact amo_dword_addi_writeback_old_run rd js_afterStore oldVal hold

/-- Jolt-side aligned concrete execution for `AMOSWAP.D`.

Rust emits `LD; SD; ADDI` for AMOSWAP.D, with no leading dword alignment row.
This composition follows that emitted row sequence. -/
theorem amoswapdProgram_concrete_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_mem : AmoMemoryContext amoop.AMOSWAP 8 addr addr js.sail)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    ∃ jsf : SailJoltState,
      (JoltISA.execProgram (JoltISA.amoswapdProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail = amoswapdFinalSailState rd js.sail addr rs2Val := by
  obtain ⟨js_afterLoad, hld, hld_sail, hld_old⟩ :=
    amo_dword_load_old_aligned_run rs1 js hcfg addr hrs1 h_mem h_align
  obtain ⟨js_afterStore, hsd, hsd_sail, hsd_vregs⟩ :=
    amo_dword_store_xreg_result_after_load_aligned_run
      rs2 rs1 js js_afterLoad hcfg addr rs2Val
      hrs1 hrs2 h_mem h_align hld_sail
  obtain ⟨js_afterWrite, haddi, haddi_sail, _haddi_vregs⟩ :=
    amo_dword_writeback_after_store_run rd js_afterLoad js_afterStore addr
      (loaded_dword_at js.sail addr) hsd_vregs hld_old
  refine ⟨js_afterWrite, ?_, ?_⟩
  · unfold JoltISA.amoswapdProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterLoad hld]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterLoad js_afterStore hsd]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterStore js_afterWrite haddi]
    rfl
  · rw [haddi_sail, hsd_sail, hld_sail]

/-- AMOSWAPD inherits the shared dword virtual-address alignment fact. -/
theorem amoswapd_is_aligned_vaddr_true (addr : BitVec 64)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    is_aligned_vaddr (Virtaddr addr) 8 = true := by
  exact amo_dword_is_aligned_vaddr_true addr h_align

/-- AMOSWAPD inherits the shared dword physical-address alignment fact. -/
theorem amoswapd_is_aligned_paddr_true (addr : BitVec 64)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    is_aligned_paddr (physaddr.Physaddr addr) 8 = true := by
  exact amo_dword_is_aligned_paddr_true addr h_align

/-- AMOSWAPD reserved RAM reads use the shared dword RAM read reduction. -/
theorem amoswapd_read_ram_reserved_eq_loaded_dword
    (addr : BitVec 64) (s : SailState)
    (hbytes : DwordBytesPresent addr s)
    (h_no_ovf : addr.toNat + 7 < 2 ^ 64) :
    LeanRV64D.Functions.read_ram read_kind.Read_RISCV_reserved
      (physaddr.Physaddr addr) 8 false s =
    .ok (loaded_dword_at s addr, default_meta) s := by
  exact amo_dword_read_ram_reserved_eq_loaded_dword addr s hbytes h_no_ovf

/-- AMOSWAPD checked memory reads use the shared dword AMO read reduction. -/
theorem amoswapd_checked_mem_read_eq_loaded_dword
    (addr : BitVec 64) (s : SailState)
    (hbytes : DwordBytesPresent addr s)
    (h_no_ovf : addr.toNat + 7 < 2 ^ 64)
    (hfm : FlatAtomicMem amoop.AMOSWAP addr 8 s) :
    checked_mem_read (Atomic (amoop.AMOSWAP, Data, Data)) Privilege.Machine
      (physaddr.Physaddr addr) 8 false false true false s =
    .ok (Ok (loaded_dword_at s addr, default_meta)) s := by
  exact
    amo_dword_checked_mem_read_eq_loaded_dword
      amoop.AMOSWAP addr s hbytes h_no_ovf hfm

/-- AMOSWAPD memory reads use the shared dword AMO memory reduction. -/
theorem amoswapd_mem_read_eq_loaded_dword
    (addr : BitVec 64) (s : SailState)
    (hcfg : JoltConfig s)
    (h_no_ovf : addr.toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (7 : BitVec 64) = 0)
    (hfm : FlatAtomicMem amoop.AMOSWAP addr 8 s) :
    mem_read (Atomic (amoop.AMOSWAP, Data, Data))
      (physaddr.Physaddr addr) 8 false false true s =
    .ok (Ok (loaded_dword_at s addr)) s := by
  exact
    amo_dword_mem_read_eq_loaded_dword
      amoop.AMOSWAP addr s hcfg h_no_ovf h_align hfm

/-- AMOSWAPD memory-write effective-address checks use the shared dword AMO
write check reduction. -/
theorem amoswapd_mem_write_ea_ok
    (addr : BitVec 64) (s : SailState)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    mem_write_ea (physaddr.Physaddr addr) 8 false false true s =
      .ok (Ok ()) s := by
  exact amo_dword_mem_write_ea_ok addr s h_align

/-- AMOSWAPD conditional RAM writes use the shared dword RAM store reduction. -/
theorem amoswapd_write_ram_conditional_eq_state_after_dword_store
    (addr data : BitVec 64) (s : SailState) :
    LeanRV64D.Functions.write_ram write_kind.Write_RISCV_conditional
      (physaddr.Physaddr addr) 8 data default_meta s =
      .ok true (state_after_dword_store s addr data) := by
  exact amo_dword_write_ram_conditional_eq_state_after_dword_store addr data s

/-- AMOSWAPD memory-value writes use the shared dword AMO store reduction. -/
theorem amoswapd_mem_write_value_eq_state_after_dword_store
    (addr data : BitVec 64) (s : SailState)
    (hcfg : JoltConfig s)
    (h_align : addr &&& (7 : BitVec 64) = 0)
    (hfm : FlatAtomicMem amoop.AMOSWAP addr 8 s) :
    mem_write_value (physaddr.Physaddr addr) 8 data
      (Atomic (amoop.AMOSWAP, Data, Data)) false false true s =
    .ok (Ok true) (state_after_dword_store s addr data) := by
  exact
    amo_dword_mem_write_value_eq_state_after_dword_store
      amoop.AMOSWAP addr data s hcfg h_align hfm

/-- Sail-side aligned concrete execution for native `AMOSWAP.D`. -/
theorem execute_AMOSWAPD_reduces_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryContext amoop.AMOSWAP 8 addr addr js.sail)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    (execute_AMO amoop.AMOSWAP false false rs2 rs1 8 rd).run js.sail =
      .ok RETIRE_SUCCESS (amoswapdFinalSailState rd js.sail addr rs2Val) := by
  change
    (execute_AMO amoop.AMOSWAP false false rs2 rs1 8 rd).run js.sail =
      .ok RETIRE_SUCCESS (amoDwordFinalSailState rd js.sail addr rs2Val)
  exact
    execute_AMO_dword_non_cas_aligned
      amoop.AMOSWAP rs2 rs1 rd js hcfg addr rs2Val rs2Val
      hrs1 hrs2 hrd h_mem h_align
      (by decide)
      (by
        unfold amoDwordSailResult
        unfold trunc Sail.BitVec.truncate
        rfl)

/-- Jolt-side misaligned execution for `AMOSWAP.D`.

The Rust-emitted expansion starts with `LD`; on a misaligned AMO.D address that
dword memory row returns the store/AMO alignment exception and the body is not
executed. -/
theorem amoswapdProgram_concrete_misaligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (addr : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (h_align : addr &&& (7 : BitVec 64) ≠ 0) :
    (JoltISA.execProgram (JoltISA.amoswapdProgram rs2 rs1 rd)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr addr, ExceptionType.E_SAMO_Addr_Align ())) js := by
  let rest : JoltISA.Program :=
    .instr (.SD (.xreg rs1) (.xreg rs2) (0 : BitVec 12)) <|
    .instr (.ADDI (.xreg rd) (.vreg JoltISA.amoOldVReg) (0 : BitVec 12)) <|
    .done RETIRE_SUCCESS
  let e := (Virtaddr addr, ExceptionType.E_SAMO_Addr_Align ())
  have hld :
      (JoltISA.execInstr
        (.LD (.vreg JoltISA.amoOldVReg) (.xreg rs1) (0 : BitVec 12))).run js =
      .ok (ExecutionResult.Memory_Exception e) js := by
    exact amo_dword_ld_xreg_misaligned_run
      JoltISA.amoOldVReg rs1 js addr hrs1 h_align
  unfold JoltISA.amoswapdProgram
  exact
    JoltISA.execProgram_instr_run_memory_exception
      (.LD (.vreg JoltISA.amoOldVReg) (.xreg rs1) (0 : BitVec 12))
      rest js js e hld

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
  exact
    execute_AMO_dword_misaligned
      amoop.AMOSWAP rs2 rs1 rd js hcfg addr rs2Val hrs1 hrs2 h_align

/-- Aligned public branch for `AMOSWAP.D`, composing the Jolt expansion and
native Sail reductions. -/
theorem amoswapdProgram_eq_sail_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryContext amoop.AMOSWAP 8 addr addr js.sail)
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

/-- Internal memory-context theorem for `AMOSWAP.D`.

The outer theorem mirrors LoadFamily: it exposes no alignment hypothesis and
dispatches on the exact predicate checked by the AMO dword access. -/
theorem amoswapdProgram_eq_sail_of_memory_context
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryContext amoop.AMOSWAP 8 addr addr js.sail) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoswapdProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOSWAP false false rs2 rs1 8 rd).run js.sail := by
  by_cases h_align : addr &&& (7 : BitVec 64) = 0
  · exact amoswapdProgram_eq_sail_aligned
      rs2 rs1 rd js hcfg addr rs2Val hrs1 hrs2 hrd h_mem h_align
  · exact amoswapdProgram_eq_sail_misaligned
      rs2 rs1 rd js hcfg addr rs2Val hrs1 hrs2 h_align

/-- Main public theorem for `AMOSWAP.D`.

The theorem takes one primitive-only atomic bundle. Exact memory context is
derived internally from that bundle. -/
theorem amoswapdProgram_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoDwordProgramEqSailAssumptions amoop.AMOSWAP rs2 rs1 rd js) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoswapdProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOSWAP false false rs2 rs1 8 rd).run js.sail := by
  let addr := h.rs1_val
  let rs2Val := h.rs2_val
  have h_mem : AmoMemoryContext amoop.AMOSWAP 8 addr addr js.sail := by
    simpa [addr] using h.memoryContext
  exact amoswapdProgram_eq_sail_of_memory_context
    rs2 rs1 rd js h.cfg addr rs2Val
    h.rs1_read.value_eq h.rs2_read.value_eq h.rd_readable.exists_value h_mem

end AtomicFamily

end
