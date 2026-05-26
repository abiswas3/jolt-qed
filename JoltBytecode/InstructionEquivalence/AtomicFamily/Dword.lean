import JoltBytecode.InstructionEquivalence.AtomicFamily.Common
import JoltBytecode.InstructionEquivalence.LoadDefUtils
import JoltBytecode.JoltISA.Semantics.Lemmas
import JoltBytecode.JoltISA.Semantics.Instructions.Add
import JoltBytecode.JoltISA.Semantics.Instructions.ADDI
import JoltBytecode.JoltISA.Semantics.Instructions.Mul
import JoltBytecode.JoltISA.Semantics.Instructions.SD
import JoltBytecode.JoltISA.Semantics.Instructions.SLTU
import JoltBytecode.JoltISA.Semantics.Instructions.Sub
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualAssertAlignment
import JoltBytecode.JoltISA.Semantics.ProgramComposition
import JoltBytecode.JoltISA.Semantics.RegisterOps
import JoltBytecode.InstructionEquivalence.Memory.WriteReasoning

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace AtomicFamily

/-- Canonical Sail state after an aligned 64-bit AMO that stores `result` and
writes the old dword value into `rd`. -/
abbrev amoDwordFinalSailState
    (rd : regidx) (s : SailState) (addr result : BitVec 64) : SailState :=
  stateAfterWrite
    (state_after_dword_store s addr result)
    rd
    (loaded_dword_at s addr)

/-- An 8-byte aligned 64-bit address has room for the full dword window. -/
theorem amo_dword_aligned_no_ovf (addr : BitVec 64)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    addr.toNat + 7 < 2 ^ 64 := by
  exact aligned_addr_no_ovf_of_align addr h_align

/-- The zero immediate used by dword AMO expansion instructions leaves the
effective address unchanged. -/
theorem amo_dword_zero_offset_addr (addr : BitVec 64) :
    addr + sign_extend (m := 64) (0 : BitVec 12) = addr := by
  have hsext0 :
      sign_extend (m := 64) (0 : BitVec 12) = (0 : BitVec 64) := by
    decide
  rw [hsext0]
  bv_decide

/-- Sail's generated zero AMO offset leaves the effective address unchanged. -/
theorem amo_dword_zero_sail_addr (addr : BitVec 64) :
    addr + zeros (n := 64) = addr := by
  unfold zeros
  exact BitVec.add_zero addr

/-- Alignment at the base address is preserved by the AMO expansion's zero
offset. -/
theorem amo_dword_zero_offset_aligned (addr : BitVec 64)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    (addr + sign_extend (m := 64) (0 : BitVec 12)) &&& (7 : BitVec 64) = 0 := by
  rw [amo_dword_zero_offset_addr addr]
  exact h_align

/-- Misalignment at the base address is preserved by the AMO expansion's zero
offset. -/
theorem amo_dword_zero_offset_misaligned (addr : BitVec 64)
    (h_align : addr &&& (7 : BitVec 64) ≠ 0) :
    (addr + sign_extend (m := 64) (0 : BitVec 12)) &&& (7 : BitVec 64) ≠ 0 := by
  rw [amo_dword_zero_offset_addr addr]
  exact h_align

/-- An aligned dword address packages the access facts expected by load/store
memory helpers. -/
theorem amo_dword_aligned_access (addr : BitVec 64)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    AlignedDwordAccess addr :=
  { misalign := access_misaligned_8_aligned_false addr h_align
    split := split_misaligned_aligned_8 addr h_align
    align := h_align
    no_ovf := amo_dword_aligned_no_ovf addr h_align }

/-- The leading dword alignment assertion retires on aligned AMO expansion
paths. -/
theorem amo_dword_virtual_assert_aligned_run
    (rs1 : regidx) (js : SailJoltState) (addr : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    (JoltISA.execInstr
      (.VirtualAssertDwordAlignment rs1 (0 : BitVec 12)
        (ExceptionType.E_SAMO_Addr_Align ()))).run js =
      .ok RETIRE_SUCCESS js := by
  exact
    JoltISA.virtual_assert_dword_alignment_run_aligned
      rs1 (0 : BitVec 12) (ExceptionType.E_SAMO_Addr_Align ())
      js addr hrs1 (amo_dword_zero_offset_aligned addr h_align)

/-- The leading dword alignment assertion raises the AMO alignment exception on
misaligned expansion paths. -/
theorem amo_dword_virtual_assert_misaligned_run
    (rs1 : regidx) (js : SailJoltState) (addr : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (h_align : addr &&& (7 : BitVec 64) ≠ 0) :
    (JoltISA.execInstr
      (.VirtualAssertDwordAlignment rs1 (0 : BitVec 12)
        (ExceptionType.E_SAMO_Addr_Align ()))).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr addr, ExceptionType.E_SAMO_Addr_Align ())) js := by
  have hrun :=
    JoltISA.virtual_assert_dword_alignment_run_misaligned
      rs1 (0 : BitVec 12) (ExceptionType.E_SAMO_Addr_Align ())
      js addr hrs1 (amo_dword_zero_offset_misaligned addr h_align)
  rw [amo_dword_zero_offset_addr addr] at hrun
  exact hrun

/-- A 64-bit value is unchanged by Sail sign-extension to 64 bits. -/
theorem amo_dword_sign_extend_64_eq_self (value : BitVec 64) :
    sign_extend (m := 64) value = value := by
  unfold sign_extend Sail.BitVec.signExtend
  bv_decide

/-- A 64-bit value is unchanged by Sail sign-extension at the generated `8 * 8`
width. -/
theorem amo_dword_sign_extend_8x8_eq_self (value : BitVec 64) :
    sign_extend (m := 8 * 8) value = value := by
  unfold sign_extend Sail.BitVec.signExtend
  bv_decide

/-- The generated dword width cast leaves an already-64-bit value unchanged. -/
theorem amo_dword_setWidth_8x8_eq_self (value : BitVec 64) :
    BitVec.setWidth (8 * 8) value = value := by
  rfl

/-- The generated AMO width assertion succeeds for an 8-byte non-CAS dword
operation. -/
theorem amo_dword_width_assert_true :
    (8 ≤b (((8 : Nat) : Int) * (2 : Int)).toNat) = true := by
  decide

/-- The generated AMO memory width check succeeds for an 8-byte dword access. -/
theorem amo_dword_width8_true : (8 ≤b (8 : Nat)) = true := by
  decide

/-- `LD old, 0(rs1)` reads the old dword into the AMO scratch register and
leaves the Sail state unchanged. -/
theorem amo_dword_ld_old_run
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

/-- `SD rs2, 0(rs1)` writes the AMO result dword and preserves virtual
registers. -/
theorem amo_dword_sd_result_run
    (rs2 rs1 : regidx) (js_afterLoad : SailJoltState)
    (addr result : BitVec 64)
    (hrs1 : rX_bits rs1 js_afterLoad.sail = .ok addr js_afterLoad.sail)
    (hrs2 : rX_bits rs2 js_afterLoad.sail = .ok result js_afterLoad.sail)
    (hwrite :
      vmem_write_addr (Virtaddr addr) 8 result
        (Store Data) false false false js_afterLoad.sail =
        .ok (Ok true)
          (state_after_dword_store js_afterLoad.sail addr result)) :
    ∃ js_afterStore : SailJoltState,
      (JoltISA.execInstr
        (.SD (.xreg rs1) (.xreg rs2) (0 : BitVec 12))).run js_afterLoad =
        .ok RETIRE_SUCCESS js_afterStore ∧
      js_afterStore.sail =
        state_after_dword_store js_afterLoad.sail addr result ∧
      js_afterStore.vregs = js_afterLoad.vregs := by
  let js_afterStore : SailJoltState :=
    { sail := state_after_dword_store js_afterLoad.sail addr result
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
          result (Store Data) false false false js_afterLoad.sail =
          .ok (Ok true)
            (state_after_dword_store js_afterLoad.sail addr result) := by
      rw [haddr0]
      exact hwrite
    exact
      JoltISA.execInstr_sd_xreg_xreg_run_of_write
        rs1 rs2 (0 : BitVec 12) js_afterLoad addr result
        (state_after_dword_store js_afterLoad.sail addr result)
        hrs1 hrs2 hwrite'
  · rfl
  · rfl

/-- Successful `SD` from an architectural-register base and a virtual-register
value source. -/
theorem amo_dword_sd_xreg_vreg_run_of_write
    (base : regidx) (value : JoltISA.VReg) (imm : BitVec 12)
    (js : SailJoltState) (baseValue stored : BitVec 64) (s' : SailState)
    (hbase : rX_bits base js.sail = .ok baseValue js.sail)
    (hvalue : js.vregs value = stored)
    (hwrite :
      vmem_write_addr (Virtaddr (baseValue + sign_extend (m := 64) imm)) 8
        stored (Store Data) false false false js.sail =
        .ok (Ok true) s') :
    (JoltISA.execInstr (.SD (.xreg base) (.vreg value) imm)).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold JoltISA.execInstr JoltISA.readSrc JoltISA.writeDst readVReg liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get, hbase, hvalue, hwrite]

/-- `SD valueReg, 0(rs1)` writes a computed AMO dword result and preserves
virtual registers. -/
theorem amo_dword_sd_vreg_result_run
    (rs1 : regidx) (valueReg : JoltISA.VReg) (js : SailJoltState)
    (addr result : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hvalue : js.vregs valueReg = result)
    (hwrite :
      vmem_write_addr (Virtaddr addr) 8 result
        (Store Data) false false false js.sail =
        .ok (Ok true)
          (state_after_dword_store js.sail addr result)) :
    ∃ js_afterStore : SailJoltState,
      (JoltISA.execInstr
        (.SD (.xreg rs1) (.vreg valueReg) (0 : BitVec 12))).run js =
        .ok RETIRE_SUCCESS js_afterStore ∧
      js_afterStore.sail =
        state_after_dword_store js.sail addr result ∧
      js_afterStore.vregs = js.vregs := by
  let js_afterStore : SailJoltState :=
    { sail := state_after_dword_store js.sail addr result
      vregs := js.vregs }
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
          result (Store Data) false false false js.sail =
          .ok (Ok true)
            (state_after_dword_store js.sail addr result) := by
      rw [haddr0]
      exact hwrite
    exact
      amo_dword_sd_xreg_vreg_run_of_write
        rs1 valueReg (0 : BitVec 12) js addr result
        (state_after_dword_store js.sail addr result)
        hrs1 hvalue hwrite'
  · rfl
  · rfl

/-- `ADDI rd, old, 0` writes the old dword value back to `rd`. -/
theorem amo_dword_addi_writeback_old_run
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

/-- The aligned AMO expansion load reads the old dword into `amoOldVReg`. -/
theorem amo_dword_load_old_aligned_run
    {op : amoop} {amoAddr : BitVec 64}
    (rs1 : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (h_mem : AmoMemoryAssumptions op 8 addr amoAddr js.sail)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    ∃ js_afterLoad : SailJoltState,
      (JoltISA.execInstr
        (.LD (.vreg JoltISA.amoOldVReg) (.xreg rs1) (0 : BitVec 12))).run js =
        .ok RETIRE_SUCCESS js_afterLoad ∧
      js_afterLoad.sail = js.sail ∧
      js_afterLoad.vregs JoltISA.amoOldVReg =
        loaded_dword_at js.sail addr := by
  have haligned := amo_dword_aligned_access addr h_align
  have hload_assumptions : DwordLoadAssumptions addr js.sail :=
    dwordLoadAssumptions_of_aligned_phys addr js.sail haligned
      (AmoMemoryAssumptions.jolt_load_mem h_mem)
  have hload :
      vmem_read_addr (Virtaddr addr) 0 8 (Load Data) false false false js.sail =
        .ok (Ok (loaded_dword_at js.sail addr)) js.sail :=
    aligned_dword_vmem_read_reduces addr js.sail hcfg hload_assumptions
  exact
    amo_dword_ld_old_run rs1 js addr (loaded_dword_at js.sail addr) hrs1 hload

/-- After the old-value load, `SD rs2, 0(rs1)` writes the AMO result dword from
the source register. -/
theorem amo_dword_store_xreg_result_after_load_aligned_run
    {op : amoop} {amoAddr : BitVec 64}
    (rs2 rs1 : regidx) (js js_afterLoad : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr result : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok result js.sail)
    (h_mem : AmoMemoryAssumptions op 8 addr amoAddr js.sail)
    (h_align : addr &&& (7 : BitVec 64) = 0)
    (hld_sail : js_afterLoad.sail = js.sail) :
    ∃ js_afterStore : SailJoltState,
      (JoltISA.execInstr
        (.SD (.xreg rs1) (.xreg rs2) (0 : BitVec 12))).run js_afterLoad =
        .ok RETIRE_SUCCESS js_afterStore ∧
      js_afterStore.sail =
        state_after_dword_store js_afterLoad.sail addr result ∧
      js_afterStore.vregs = js_afterLoad.vregs := by
  have haligned := amo_dword_aligned_access addr h_align
  have hwrite :
      vmem_write_addr (Virtaddr addr) 8 result
        (Store Data) false false false js.sail =
        .ok (Ok true) (state_after_dword_store js.sail addr result) :=
    vmem_write_addr_dword_store_reduces addr result js.sail hcfg
      haligned.toAlignedAccess
      (AmoMemoryAssumptions.jolt_store_mem h_mem).pmp
      (AmoMemoryAssumptions.jolt_store_mem h_mem).mmio
  have hrs1_afterLoad :
      rX_bits rs1 js_afterLoad.sail = .ok addr js_afterLoad.sail := by
    rw [hld_sail]
    exact hrs1
  have hrs2_afterLoad :
      rX_bits rs2 js_afterLoad.sail = .ok result js_afterLoad.sail := by
    rw [hld_sail]
    exact hrs2
  have hwrite_afterLoad :
      vmem_write_addr (Virtaddr addr) 8 result
        (Store Data) false false false js_afterLoad.sail =
        .ok (Ok true)
          (state_after_dword_store js_afterLoad.sail addr result) := by
    rw [hld_sail]
    exact hwrite
  exact
    amo_dword_sd_result_run rs2 rs1 js_afterLoad addr result
      hrs1_afterLoad hrs2_afterLoad hwrite_afterLoad

/-- Shape produced by the pure middle instruction in a dword AMO binop
expansion.

The middle instruction computes the new dword into `amoNewVReg`, leaves the
Sail state unchanged, and preserves the loaded old dword in `amoOldVReg`. -/
structure AmoDwordMiddleStep
    (middle : JoltISA.Instr) (old result : BitVec 64)
    (js_before js_after : SailJoltState) : Prop where
  run :
    (JoltISA.execInstr middle).run js_before =
      .ok RETIRE_SUCCESS js_after
  sail : js_after.sail = js_before.sail
  result_vreg : js_after.vregs JoltISA.amoNewVReg = result
  old_vreg : js_after.vregs JoltISA.amoOldVReg = old

/-- Dword addition is commutative at the bitvector level. -/
theorem amo_dword_add_comm (lhs rhs : BitVec 64) :
    lhs + rhs = rhs + lhs := by
  bv_decide

/-- Dword xor is commutative at the bitvector level. -/
theorem amo_dword_xor_comm (lhs rhs : BitVec 64) :
    lhs ^^^ rhs = rhs ^^^ lhs := by
  bv_decide

/-- Dword and is commutative at the bitvector level. -/
theorem amo_dword_and_comm (lhs rhs : BitVec 64) :
    lhs &&& rhs = rhs &&& lhs := by
  bv_decide

/-- Dword or is commutative at the bitvector level. -/
theorem amo_dword_or_comm (lhs rhs : BitVec 64) :
    lhs ||| rhs = rhs ||| lhs := by
  bv_decide

/-- The `AMOADD.D` middle instruction writes `rs2 + old` to `amoNewVReg` and
preserves the loaded old dword. -/
theorem amo_dword_add_middle_run
    (rs2 : regidx) (js_afterLoad : SailJoltState)
    (rs2Val old : BitVec 64)
    (hrs2 : rX_bits rs2 js_afterLoad.sail =
      .ok rs2Val js_afterLoad.sail)
    (hold : js_afterLoad.vregs JoltISA.amoOldVReg = old) :
    ∃ js_afterMiddle : SailJoltState,
      AmoDwordMiddleStep
        (.ADD (.vreg JoltISA.amoNewVReg)
          (.vreg JoltISA.amoOldVReg) (.xreg rs2))
        old (rs2Val + old) js_afterLoad js_afterMiddle := by
  let js_afterMiddle : SailJoltState :=
    { sail := js_afterLoad.sail
      vregs := fun r =>
        if r = JoltISA.amoNewVReg then old + rs2Val else js_afterLoad.vregs r }
  refine ⟨js_afterMiddle, ?_, ?_, ?_, ?_⟩
  · unfold JoltISA.execInstr JoltISA.readSrc JoltISA.writeDst readVReg
      writeVReg liftSail
    simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
      get, getThe, MonadStateOf.get, EStateM.get,
      modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
      hold, hrs2]
    rfl
  · rfl
  · change
      (if JoltISA.amoNewVReg = JoltISA.amoNewVReg then old + rs2Val
        else js_afterLoad.vregs JoltISA.amoNewVReg) = rs2Val + old
    rw [if_pos rfl]
    exact amo_dword_add_comm old rs2Val
  · change
      (if JoltISA.amoOldVReg = JoltISA.amoNewVReg then old + rs2Val
        else js_afterLoad.vregs JoltISA.amoOldVReg) = old
    rw [if_neg (by decide)]
    exact hold

/-- The `AMOXOR.D` middle instruction writes `rs2 ^ old` to `amoNewVReg` and
preserves the loaded old dword. -/
theorem amo_dword_xor_middle_run
    (rs2 : regidx) (js_afterLoad : SailJoltState)
    (rs2Val old : BitVec 64)
    (hrs2 : rX_bits rs2 js_afterLoad.sail =
      .ok rs2Val js_afterLoad.sail)
    (hold : js_afterLoad.vregs JoltISA.amoOldVReg = old) :
    ∃ js_afterMiddle : SailJoltState,
      AmoDwordMiddleStep
        (.XOR (.vreg JoltISA.amoNewVReg)
          (.vreg JoltISA.amoOldVReg) (.xreg rs2))
        old (rs2Val ^^^ old) js_afterLoad js_afterMiddle := by
  let js_afterMiddle : SailJoltState :=
    { sail := js_afterLoad.sail
      vregs := fun r =>
        if r = JoltISA.amoNewVReg then old ^^^ rs2Val else js_afterLoad.vregs r }
  refine ⟨js_afterMiddle, ?_, ?_, ?_, ?_⟩
  · unfold JoltISA.execInstr JoltISA.readSrc JoltISA.writeDst readVReg
      writeVReg liftSail
    simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
      get, getThe, MonadStateOf.get, EStateM.get,
      modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
      hold, hrs2]
    rfl
  · rfl
  · change
      (if JoltISA.amoNewVReg = JoltISA.amoNewVReg then old ^^^ rs2Val
        else js_afterLoad.vregs JoltISA.amoNewVReg) = rs2Val ^^^ old
    rw [if_pos rfl]
    exact amo_dword_xor_comm old rs2Val
  · change
      (if JoltISA.amoOldVReg = JoltISA.amoNewVReg then old ^^^ rs2Val
        else js_afterLoad.vregs JoltISA.amoOldVReg) = old
    rw [if_neg (by decide)]
    exact hold

/-- The `AMOAND.D` middle instruction writes `rs2 & old` to `amoNewVReg` and
preserves the loaded old dword. -/
theorem amo_dword_and_middle_run
    (rs2 : regidx) (js_afterLoad : SailJoltState)
    (rs2Val old : BitVec 64)
    (hrs2 : rX_bits rs2 js_afterLoad.sail =
      .ok rs2Val js_afterLoad.sail)
    (hold : js_afterLoad.vregs JoltISA.amoOldVReg = old) :
    ∃ js_afterMiddle : SailJoltState,
      AmoDwordMiddleStep
        (.AND (.vreg JoltISA.amoNewVReg)
          (.vreg JoltISA.amoOldVReg) (.xreg rs2))
        old (rs2Val &&& old) js_afterLoad js_afterMiddle := by
  let js_afterMiddle : SailJoltState :=
    { sail := js_afterLoad.sail
      vregs := fun r =>
        if r = JoltISA.amoNewVReg then old &&& rs2Val else js_afterLoad.vregs r }
  refine ⟨js_afterMiddle, ?_, ?_, ?_, ?_⟩
  · unfold JoltISA.execInstr JoltISA.readSrc JoltISA.writeDst readVReg
      writeVReg liftSail
    simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
      get, getThe, MonadStateOf.get, EStateM.get,
      modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
      hold, hrs2]
    rfl
  · rfl
  · change
      (if JoltISA.amoNewVReg = JoltISA.amoNewVReg then old &&& rs2Val
        else js_afterLoad.vregs JoltISA.amoNewVReg) = rs2Val &&& old
    rw [if_pos rfl]
    exact amo_dword_and_comm old rs2Val
  · change
      (if JoltISA.amoOldVReg = JoltISA.amoNewVReg then old &&& rs2Val
        else js_afterLoad.vregs JoltISA.amoOldVReg) = old
    rw [if_neg (by decide)]
    exact hold

/-- The `AMOOR.D` middle instruction writes `rs2 | old` to `amoNewVReg` and
preserves the loaded old dword. -/
theorem amo_dword_or_middle_run
    (rs2 : regidx) (js_afterLoad : SailJoltState)
    (rs2Val old : BitVec 64)
    (hrs2 : rX_bits rs2 js_afterLoad.sail =
      .ok rs2Val js_afterLoad.sail)
    (hold : js_afterLoad.vregs JoltISA.amoOldVReg = old) :
    ∃ js_afterMiddle : SailJoltState,
      AmoDwordMiddleStep
        (.OR (.vreg JoltISA.amoNewVReg)
          (.vreg JoltISA.amoOldVReg) (.xreg rs2))
        old (rs2Val ||| old) js_afterLoad js_afterMiddle := by
  let js_afterMiddle : SailJoltState :=
    { sail := js_afterLoad.sail
      vregs := fun r =>
        if r = JoltISA.amoNewVReg then old ||| rs2Val else js_afterLoad.vregs r }
  refine ⟨js_afterMiddle, ?_, ?_, ?_, ?_⟩
  · unfold JoltISA.execInstr JoltISA.readSrc JoltISA.writeDst readVReg
      writeVReg liftSail
    simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
      get, getThe, MonadStateOf.get, EStateM.get,
      modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
      hold, hrs2]
    rfl
  · rfl
  · change
      (if JoltISA.amoNewVReg = JoltISA.amoNewVReg then old ||| rs2Val
        else js_afterLoad.vregs JoltISA.amoNewVReg) = rs2Val ||| old
    rw [if_pos rfl]
    exact amo_dword_or_comm old rs2Val
  · change
      (if JoltISA.amoOldVReg = JoltISA.amoNewVReg then old ||| rs2Val
        else js_afterLoad.vregs JoltISA.amoOldVReg) = old
    rw [if_neg (by decide)]
    exact hold

/-- After the common dword load, the `AMOADD.D` middle instruction is ready
for the shared double-binop program helper. -/
theorem amo_dword_add_middle_after_load
    (rs2 : regidx) (js : SailJoltState) (addr rs2Val : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail) :
    ∀ js_afterLoad : SailJoltState,
      js_afterLoad.sail = js.sail →
      js_afterLoad.vregs JoltISA.amoOldVReg =
        loaded_dword_at js.sail addr →
      ∃ js_afterMiddle : SailJoltState,
        AmoDwordMiddleStep
          (.ADD (.vreg JoltISA.amoNewVReg)
            (.vreg JoltISA.amoOldVReg) (.xreg rs2))
          (loaded_dword_at js.sail addr)
          (rs2Val + loaded_dword_at js.sail addr)
          js_afterLoad js_afterMiddle := by
  intro js_afterLoad hld_sail hld_old
  have hrs2_afterLoad :
      rX_bits rs2 js_afterLoad.sail =
        .ok rs2Val js_afterLoad.sail := by
    rw [hld_sail]
    exact hrs2
  exact
    amo_dword_add_middle_run rs2 js_afterLoad rs2Val
      (loaded_dword_at js.sail addr) hrs2_afterLoad hld_old

/-- After the common dword load, the `AMOXOR.D` middle instruction is ready
for the shared double-binop program helper. -/
theorem amo_dword_xor_middle_after_load
    (rs2 : regidx) (js : SailJoltState) (addr rs2Val : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail) :
    ∀ js_afterLoad : SailJoltState,
      js_afterLoad.sail = js.sail →
      js_afterLoad.vregs JoltISA.amoOldVReg =
        loaded_dword_at js.sail addr →
      ∃ js_afterMiddle : SailJoltState,
        AmoDwordMiddleStep
          (.XOR (.vreg JoltISA.amoNewVReg)
            (.vreg JoltISA.amoOldVReg) (.xreg rs2))
          (loaded_dword_at js.sail addr)
          (rs2Val ^^^ loaded_dword_at js.sail addr)
          js_afterLoad js_afterMiddle := by
  intro js_afterLoad hld_sail hld_old
  have hrs2_afterLoad :
      rX_bits rs2 js_afterLoad.sail =
        .ok rs2Val js_afterLoad.sail := by
    rw [hld_sail]
    exact hrs2
  exact
    amo_dword_xor_middle_run rs2 js_afterLoad rs2Val
      (loaded_dword_at js.sail addr) hrs2_afterLoad hld_old

/-- After the common dword load, the `AMOAND.D` middle instruction is ready
for the shared double-binop program helper. -/
theorem amo_dword_and_middle_after_load
    (rs2 : regidx) (js : SailJoltState) (addr rs2Val : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail) :
    ∀ js_afterLoad : SailJoltState,
      js_afterLoad.sail = js.sail →
      js_afterLoad.vregs JoltISA.amoOldVReg =
        loaded_dword_at js.sail addr →
      ∃ js_afterMiddle : SailJoltState,
        AmoDwordMiddleStep
          (.AND (.vreg JoltISA.amoNewVReg)
            (.vreg JoltISA.amoOldVReg) (.xreg rs2))
          (loaded_dword_at js.sail addr)
          (rs2Val &&& loaded_dword_at js.sail addr)
          js_afterLoad js_afterMiddle := by
  intro js_afterLoad hld_sail hld_old
  have hrs2_afterLoad :
      rX_bits rs2 js_afterLoad.sail =
        .ok rs2Val js_afterLoad.sail := by
    rw [hld_sail]
    exact hrs2
  exact
    amo_dword_and_middle_run rs2 js_afterLoad rs2Val
      (loaded_dword_at js.sail addr) hrs2_afterLoad hld_old

/-- After the common dword load, the `AMOOR.D` middle instruction is ready
for the shared double-binop program helper. -/
theorem amo_dword_or_middle_after_load
    (rs2 : regidx) (js : SailJoltState) (addr rs2Val : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail) :
    ∀ js_afterLoad : SailJoltState,
      js_afterLoad.sail = js.sail →
      js_afterLoad.vregs JoltISA.amoOldVReg =
        loaded_dword_at js.sail addr →
      ∃ js_afterMiddle : SailJoltState,
        AmoDwordMiddleStep
          (.OR (.vreg JoltISA.amoNewVReg)
            (.vreg JoltISA.amoOldVReg) (.xreg rs2))
          (loaded_dword_at js.sail addr)
          (rs2Val ||| loaded_dword_at js.sail addr)
          js_afterLoad js_afterMiddle := by
  intro js_afterLoad hld_sail hld_old
  have hrs2_afterLoad :
      rX_bits rs2 js_afterLoad.sail =
        .ok rs2Val js_afterLoad.sail := by
    rw [hld_sail]
    exact hrs2
  exact
    amo_dword_or_middle_run rs2 js_afterLoad rs2Val
      (loaded_dword_at js.sail addr) hrs2_afterLoad hld_old

/-- The comparison phase of dword select AMOs writes the boolean flag into
`amoNewVReg`. -/
abbrev amoDwordSelectComparePhase
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src) : JoltISA.Program :=
  .instr (cmpInstr (.vreg JoltISA.amoNewVReg) cmpLhs cmpRhs) <|
  .done RETIRE_SUCCESS

/-- The common arithmetic tail of dword select AMOs consumes the flag in
`amoNewVReg` and writes `old + (rs2 - old) * flag` back to `amoNewVReg`. -/
abbrev amoDwordSelectTailPhase (rs2 : regidx) : JoltISA.Program :=
  .instr (.SUB (.vreg JoltISA.amoTmpVReg)
    (.xreg rs2) (.vreg JoltISA.amoOldVReg)) <|
  .instr (.MUL (.vreg JoltISA.amoTmpVReg)
    (.vreg JoltISA.amoTmpVReg) (.vreg JoltISA.amoNewVReg)) <|
  .instr (.ADD (.vreg JoltISA.amoNewVReg)
    (.vreg JoltISA.amoOldVReg) (.vreg JoltISA.amoTmpVReg)) <|
  .done RETIRE_SUCCESS

/-- The full middle block shared by dword select AMOs is the comparison phase
followed by the common select tail and then the caller-provided continuation. -/
abbrev amoDwordSelectMiddleProgram
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src) (rs2 : regidx)
    (tail : JoltISA.Program) : JoltISA.Program :=
  (amoDwordSelectComparePhase cmpInstr cmpLhs cmpRhs).append <|
  (amoDwordSelectTailPhase rs2).append tail

/-- Shape produced by the comparison phase of a dword select AMO.

The phase only computes the comparison flag, leaves Sail unchanged, and
preserves the loaded old dword. -/
structure AmoDwordSelectCompareStep
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src) (old flag : BitVec 64)
    (js_before js_after : SailJoltState) : Prop where
  run :
    JoltISA.Program.Run
      (amoDwordSelectComparePhase cmpInstr cmpLhs cmpRhs) js_before js_after
  sail : js_after.sail = js_before.sail
  flag_vreg : js_after.vregs JoltISA.amoNewVReg = flag
  old_vreg : js_after.vregs JoltISA.amoOldVReg = old

/-- Shape produced by the common select-tail phase.

The phase consumes the comparison flag already in `amoNewVReg`, computes the
selected dword into `amoNewVReg`, leaves Sail unchanged, and preserves the
loaded old dword in `amoOldVReg`. -/
structure AmoDwordSelectTailStep
    (rs2 : regidx) (old result : BitVec 64)
    (js_before js_after : SailJoltState) : Prop where
  run : JoltISA.Program.Run (amoDwordSelectTailPhase rs2) js_before js_after
  sail : js_after.sail = js_before.sail
  result_vreg : js_after.vregs JoltISA.amoNewVReg = result
  old_vreg : js_after.vregs JoltISA.amoOldVReg = old

/-- Shape produced by the full dword select middle block.

The block computes the selected new dword into `amoNewVReg`, leaves Sail
unchanged, and preserves the loaded old dword in `amoOldVReg`. -/
structure AmoDwordSelectMiddleStep
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src) (rs2 : regidx)
    (old result : BitVec 64)
    (js_before js_after : SailJoltState) : Prop where
  run :
    ∀ tail,
      (JoltISA.execProgram
        (amoDwordSelectMiddleProgram cmpInstr cmpLhs cmpRhs rs2 tail)).run
          js_before =
        (JoltISA.execProgram tail).run js_after
  sail : js_after.sail = js_before.sail
  result_vreg : js_after.vregs JoltISA.amoNewVReg = result
  old_vreg : js_after.vregs JoltISA.amoOldVReg = old

/-- `SLTU` with a real left source and virtual right source writes the unsigned
less-than flag to a virtual destination without changing Sail state. -/
theorem amo_dword_sltu_run_vreg_xreg_vreg
    (vd rhs : JoltISA.VReg) (lhs : regidx)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits lhs js.sail = .ok x js.sail) :
    (JoltISA.execInstr (.SLTU (.vreg vd) (.xreg lhs) (.vreg rhs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then jolt_sltu_value x (js.vregs rhs) else js.vregs r } := by
  unfold JoltISA.execInstr JoltISA.readSrc JoltISA.writeDst
    readVReg writeVReg liftSail
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `SLTU` with a virtual left source and real right source writes the unsigned
less-than flag to a virtual destination without changing Sail state. -/
theorem amo_dword_sltu_run_vreg_vreg_xreg
    (vd lhs : JoltISA.VReg) (rhs : regidx)
    (js : SailJoltState) (y : BitVec 64)
    (h : rX_bits rhs js.sail = .ok y js.sail) :
    (JoltISA.execInstr (.SLTU (.vreg vd) (.vreg lhs) (.xreg rhs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then jolt_sltu_value (js.vregs lhs) y else js.vregs r } := by
  unfold JoltISA.execInstr JoltISA.readSrc JoltISA.writeDst
    readVReg writeVReg liftSail
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `SLT` with a real left source and virtual right source writes the signed
less-than flag to a virtual destination without changing Sail state. -/
theorem amo_dword_slt_run_vreg_xreg_vreg
    (vd rhs : JoltISA.VReg) (lhs : regidx)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits lhs js.sail = .ok x js.sail) :
    (JoltISA.execInstr (.SLT (.vreg vd) (.xreg lhs) (.vreg rhs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then zero_extend (m := 64)
              (bool_to_bit (zopz0zI_s x (js.vregs rhs)))
            else js.vregs r } := by
  unfold JoltISA.execInstr JoltISA.readSrc JoltISA.writeDst
    readVReg writeVReg liftSail
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `SLT` with a virtual left source and real right source writes the signed
less-than flag to a virtual destination without changing Sail state. -/
theorem amo_dword_slt_run_vreg_vreg_xreg
    (vd lhs : JoltISA.VReg) (rhs : regidx)
    (js : SailJoltState) (y : BitVec 64)
    (h : rX_bits rhs js.sail = .ok y js.sail) :
    (JoltISA.execInstr (.SLT (.vreg vd) (.vreg lhs) (.xreg rhs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then zero_extend (m := 64)
              (bool_to_bit (zopz0zI_s (js.vregs lhs) y))
            else js.vregs r } := by
  unfold JoltISA.execInstr JoltISA.readSrc JoltISA.writeDst
    readVReg writeVReg liftSail
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- The shared select-tail phase computes `old + (rs2 - old) * flag` from the
old value in `amoOldVReg` and the flag already in `amoNewVReg`. -/
theorem amo_dword_select_tail_phase_run
    (rs2 : regidx) (js : SailJoltState)
    (rs2Val old flag : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hold : js.vregs JoltISA.amoOldVReg = old)
    (hflag : js.vregs JoltISA.amoNewVReg = flag) :
    ∃ js_afterTail : SailJoltState,
      AmoDwordSelectTailStep rs2 old
        (old + (rs2Val - old) * flag) js js_afterTail := by
  let delta : BitVec 64 := rs2Val - old
  let scaled : BitVec 64 := delta * flag
  let js_afterSub : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.amoTmpVReg then delta else js.vregs r }
  let js_afterMul : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.amoTmpVReg then scaled else js_afterSub.vregs r }
  let js_afterAdd : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.amoNewVReg then old + scaled else js_afterMul.vregs r }
  have hsub_new : js_afterSub.vregs JoltISA.amoNewVReg = flag := by
    change (if JoltISA.amoNewVReg = JoltISA.amoTmpVReg then delta
      else js.vregs JoltISA.amoNewVReg) = flag
    rw [if_neg (by decide), hflag]
  have hsub_old : js_afterSub.vregs JoltISA.amoOldVReg = old := by
    change (if JoltISA.amoOldVReg = JoltISA.amoTmpVReg then delta
      else js.vregs JoltISA.amoOldVReg) = old
    rw [if_neg (by decide), hold]
  have hsub_tmp : js_afterSub.vregs JoltISA.amoTmpVReg = delta := by
    change (if JoltISA.amoTmpVReg = JoltISA.amoTmpVReg then delta
      else js.vregs JoltISA.amoTmpVReg) = delta
    rw [if_pos rfl]
  have hsub_run :
      (JoltISA.execInstr
        (.SUB (.vreg JoltISA.amoTmpVReg)
          (.xreg rs2) (.vreg JoltISA.amoOldVReg))).run js =
        .ok RETIRE_SUCCESS js_afterSub := by
    rw [JoltISA.sub_run_vreg_xreg_vreg
      JoltISA.amoTmpVReg rs2 JoltISA.amoOldVReg js rs2Val hrs2]
    unfold js_afterSub delta
    rw [hold]
  have hmul_old : js_afterMul.vregs JoltISA.amoOldVReg = old := by
    change (if JoltISA.amoOldVReg = JoltISA.amoTmpVReg then scaled
      else js_afterSub.vregs JoltISA.amoOldVReg) = old
    rw [if_neg (by decide), hsub_old]
  have hmul_tmp : js_afterMul.vregs JoltISA.amoTmpVReg = scaled := by
    change (if JoltISA.amoTmpVReg = JoltISA.amoTmpVReg then scaled
      else js_afterSub.vregs JoltISA.amoTmpVReg) = scaled
    rw [if_pos rfl]
  have hmul_run :
      (JoltISA.execInstr
        (.MUL (.vreg JoltISA.amoTmpVReg)
          (.vreg JoltISA.amoTmpVReg) (.vreg JoltISA.amoNewVReg))).run
          js_afterSub =
        .ok RETIRE_SUCCESS js_afterMul := by
    rw [JoltISA.mul_run_vreg_vreg_vreg
      JoltISA.amoTmpVReg JoltISA.amoTmpVReg JoltISA.amoNewVReg js_afterSub]
    unfold js_afterMul scaled
    rw [hsub_tmp, hsub_new]
  have hadd_old : js_afterAdd.vregs JoltISA.amoOldVReg = old := by
    change (if JoltISA.amoOldVReg = JoltISA.amoNewVReg then old + scaled
      else js_afterMul.vregs JoltISA.amoOldVReg) = old
    rw [if_neg (by decide), hmul_old]
  have hadd_result :
      js_afterAdd.vregs JoltISA.amoNewVReg =
        old + (rs2Val - old) * flag := by
    change (if JoltISA.amoNewVReg = JoltISA.amoNewVReg then old + scaled
      else js_afterMul.vregs JoltISA.amoNewVReg) =
        old + (rs2Val - old) * flag
    rw [if_pos rfl]
  have hadd_run :
      (JoltISA.execInstr
        (.ADD (.vreg JoltISA.amoNewVReg)
          (.vreg JoltISA.amoOldVReg) (.vreg JoltISA.amoTmpVReg))).run
          js_afterMul =
        .ok RETIRE_SUCCESS js_afterAdd := by
    rw [JoltISA.add_run_vreg_vreg_vreg
      JoltISA.amoNewVReg JoltISA.amoOldVReg JoltISA.amoTmpVReg js_afterMul]
    unfold js_afterAdd
    rw [hmul_old, hmul_tmp]
  refine ⟨js_afterAdd, ?_, ?_, ?_, ?_⟩
  · change (JoltISA.execProgram (amoDwordSelectTailPhase rs2)).run js =
      .ok RETIRE_SUCCESS js_afterAdd
    unfold amoDwordSelectTailPhase
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterSub hsub_run]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterSub js_afterMul
      hmul_run]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterMul js_afterAdd
      hadd_run]
    rfl
  · rfl
  · exact hadd_result
  · exact hadd_old

/-- `AMOMINU.D`'s comparison phase writes the unsigned less-than flag for
`rs2 < old`. -/
theorem amo_dword_minu_compare_phase_run
    (rs2 : regidx) (js : SailJoltState) (rs2Val old : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hold : js.vregs JoltISA.amoOldVReg = old) :
    ∃ js_afterCmp : SailJoltState,
      AmoDwordSelectCompareStep
        (fun dst lhs rhs => .SLTU dst lhs rhs)
        (.xreg rs2) (.vreg JoltISA.amoOldVReg) old
        (jolt_sltu_value rs2Val old) js js_afterCmp := by
  let flag : BitVec 64 := jolt_sltu_value rs2Val old
  let js_afterCmp : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.amoNewVReg then flag else js.vregs r }
  have hcmp_run :
      (JoltISA.execInstr
        (.SLTU (.vreg JoltISA.amoNewVReg)
          (.xreg rs2) (.vreg JoltISA.amoOldVReg))).run js =
        .ok RETIRE_SUCCESS js_afterCmp := by
    rw [amo_dword_sltu_run_vreg_xreg_vreg
      JoltISA.amoNewVReg JoltISA.amoOldVReg rs2 js rs2Val hrs2]
    unfold js_afterCmp flag
    rw [hold]
  refine ⟨js_afterCmp, ?_, ?_, ?_, ?_⟩
  · change
      (JoltISA.execProgram
        (amoDwordSelectComparePhase
          (fun dst lhs rhs => .SLTU dst lhs rhs)
          (.xreg rs2) (.vreg JoltISA.amoOldVReg))).run js =
        .ok RETIRE_SUCCESS js_afterCmp
    unfold amoDwordSelectComparePhase
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterCmp hcmp_run]
    rfl
  · rfl
  · change (if JoltISA.amoNewVReg = JoltISA.amoNewVReg then flag
      else js.vregs JoltISA.amoNewVReg) = jolt_sltu_value rs2Val old
    rw [if_pos rfl]
  · change (if JoltISA.amoOldVReg = JoltISA.amoNewVReg then flag
      else js.vregs JoltISA.amoOldVReg) = old
    rw [if_neg (by decide), hold]

/-- A dword select middle block composes an instruction-specific comparison
phase with the shared select-tail phase. -/
theorem amo_dword_select_middle_phase_run
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src) (rs2 : regidx)
    (js : SailJoltState) (rs2Val old flag result : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hcompare :
      ∃ js_afterCmp : SailJoltState,
        AmoDwordSelectCompareStep cmpInstr cmpLhs cmpRhs old flag
          js js_afterCmp)
    (hresult : old + (rs2Val - old) * flag = result) :
    ∃ js_afterMiddle : SailJoltState,
      AmoDwordSelectMiddleStep cmpInstr cmpLhs cmpRhs rs2 old result
        js js_afterMiddle := by
  obtain ⟨js_afterCmp, hcmp_step⟩ := hcompare
  have hrs2_afterCmp :
      rX_bits rs2 js_afterCmp.sail = .ok rs2Val js_afterCmp.sail := by
    rw [hcmp_step.sail]
    exact hrs2
  obtain ⟨js_afterTail, htail_step⟩ :=
    amo_dword_select_tail_phase_run rs2 js_afterCmp rs2Val old flag
      hrs2_afterCmp hcmp_step.old_vreg hcmp_step.flag_vreg
  refine ⟨js_afterTail, ?_, ?_, ?_, ?_⟩
  · intro tail
    unfold amoDwordSelectMiddleProgram
    have hcmp_append :
        (JoltISA.execProgram
          ((amoDwordSelectComparePhase cmpInstr cmpLhs cmpRhs).append
            ((amoDwordSelectTailPhase rs2).append tail))).run js =
          (JoltISA.execProgram
            ((amoDwordSelectTailPhase rs2).append tail)).run js_afterCmp := by
      exact
        JoltISA.execProgram_append_of_first_succeeds
          (amoDwordSelectComparePhase cmpInstr cmpLhs cmpRhs)
          ((amoDwordSelectTailPhase rs2).append tail)
          js js_afterCmp hcmp_step.run
    have htail_append :
        (JoltISA.execProgram
          ((amoDwordSelectTailPhase rs2).append tail)).run js_afterCmp =
          (JoltISA.execProgram tail).run js_afterTail := by
      exact
        JoltISA.execProgram_append_of_first_succeeds
          (amoDwordSelectTailPhase rs2) tail
          js_afterCmp js_afterTail htail_step.run
    rw [hcmp_append, htail_append]
  · rw [htail_step.sail, hcmp_step.sail]
  · rw [htail_step.result_vreg, hresult]
  · exact htail_step.old_vreg

/-- A select AMO with a false flag keeps the old dword; with a true flag it
chooses `new`. -/
theorem amo_dword_select_value_of_bool
    (old new : BitVec 64) (flag : Bool) :
    old + (new - old) * zero_extend (m := 64) (bool_to_bit flag) =
      if flag then new else old := by
  cases flag
  · unfold bool_to_bit bool_bit_forwards zero_extend Sail.BitVec.zeroExtend
    bv_decide
  · unfold bool_to_bit bool_bit_forwards zero_extend Sail.BitVec.zeroExtend
    bv_decide

/-- The unsigned-min dword select arithmetic matches Sail's unsigned
less-than branch. -/
theorem amo_dword_select_value_of_sltu
    (old new : BitVec 64) :
    old + (new - old) * jolt_sltu_value new old =
      if (zopz0zI_u new old : Bool) then new else old := by
  unfold jolt_sltu_value
  exact amo_dword_select_value_of_bool old new (zopz0zI_u new old)

/-- The signed-min dword select arithmetic matches Sail's signed less-than
branch. -/
theorem amo_dword_select_value_of_slt
    (old new : BitVec 64) :
    old + (new - old) *
      zero_extend (m := 64) (bool_to_bit (zopz0zI_s new old)) =
      if (zopz0zI_s new old : Bool) then new else old := by
  exact amo_dword_select_value_of_bool old new (zopz0zI_s new old)

/-- Signed less-than with reversed operands is Sail's signed greater-than test. -/
theorem amo_dword_slt_reverse_eq_sgt (old new : BitVec 64) :
    (zopz0zI_s old new : Bool) = (zopz0zK_s new old : Bool) := by
  unfold zopz0zI_s zopz0zK_s
  rfl

/-- Unsigned less-than with reversed operands is Sail's unsigned greater-than
test. -/
theorem amo_dword_sltu_reverse_eq_sgtu (old new : BitVec 64) :
    (zopz0zI_u old new : Bool) = (zopz0zK_u new old : Bool) := by
  unfold zopz0zI_u zopz0zK_u
  rfl

/-- The signed-max dword select arithmetic matches Sail's signed greater-than
branch. -/
theorem amo_dword_select_value_of_sgt
    (old new : BitVec 64) :
    old + (new - old) *
      zero_extend (m := 64) (bool_to_bit (zopz0zI_s old new)) =
      if (zopz0zK_s new old : Bool) then new else old := by
  rw [amo_dword_slt_reverse_eq_sgt old new]
  exact amo_dword_select_value_of_bool old new (zopz0zK_s new old)

/-- The unsigned-max dword select arithmetic matches Sail's unsigned
greater-than branch. -/
theorem amo_dword_select_value_of_sgtu
    (old new : BitVec 64) :
    old + (new - old) * jolt_sltu_value old new =
      if (zopz0zK_u new old : Bool) then new else old := by
  unfold jolt_sltu_value
  rw [amo_dword_sltu_reverse_eq_sgtu old new]
  exact amo_dword_select_value_of_bool old new (zopz0zK_u new old)

/-- `AMOMIN.D`'s comparison phase writes the signed less-than flag for
`rs2 < old`. -/
theorem amo_dword_min_compare_phase_run
    (rs2 : regidx) (js : SailJoltState) (rs2Val old : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hold : js.vregs JoltISA.amoOldVReg = old) :
    ∃ js_afterCmp : SailJoltState,
      AmoDwordSelectCompareStep
        (fun dst lhs rhs => .SLT dst lhs rhs)
        (.xreg rs2) (.vreg JoltISA.amoOldVReg) old
        (zero_extend (m := 64) (bool_to_bit (zopz0zI_s rs2Val old)))
        js js_afterCmp := by
  let flag : BitVec 64 :=
    zero_extend (m := 64) (bool_to_bit (zopz0zI_s rs2Val old))
  let js_afterCmp : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.amoNewVReg then flag else js.vregs r }
  have hcmp_run :
      (JoltISA.execInstr
        (.SLT (.vreg JoltISA.amoNewVReg)
          (.xreg rs2) (.vreg JoltISA.amoOldVReg))).run js =
        .ok RETIRE_SUCCESS js_afterCmp := by
    rw [amo_dword_slt_run_vreg_xreg_vreg
      JoltISA.amoNewVReg JoltISA.amoOldVReg rs2 js rs2Val hrs2]
    unfold js_afterCmp flag
    rw [hold]
  refine ⟨js_afterCmp, ?_, ?_, ?_, ?_⟩
  · change
      (JoltISA.execProgram
        (amoDwordSelectComparePhase
          (fun dst lhs rhs => .SLT dst lhs rhs)
          (.xreg rs2) (.vreg JoltISA.amoOldVReg))).run js =
        .ok RETIRE_SUCCESS js_afterCmp
    unfold amoDwordSelectComparePhase
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterCmp hcmp_run]
    rfl
  · rfl
  · change (if JoltISA.amoNewVReg = JoltISA.amoNewVReg then flag
      else js.vregs JoltISA.amoNewVReg) =
      zero_extend (m := 64) (bool_to_bit (zopz0zI_s rs2Val old))
    rw [if_pos rfl]
  · change (if JoltISA.amoOldVReg = JoltISA.amoNewVReg then flag
      else js.vregs JoltISA.amoOldVReg) = old
    rw [if_neg (by decide), hold]

/-- `AMOMIN.D`'s select middle block chooses `rs2` exactly when `rs2 < old`
as signed dwords. -/
theorem amo_dword_min_middle_run
    (rs2 : regidx) (js_afterLoad : SailJoltState)
    (rs2Val old : BitVec 64)
    (hrs2 : rX_bits rs2 js_afterLoad.sail =
      .ok rs2Val js_afterLoad.sail)
    (hold : js_afterLoad.vregs JoltISA.amoOldVReg = old) :
    ∃ js_afterMiddle : SailJoltState,
      AmoDwordSelectMiddleStep
        (fun dst lhs rhs => .SLT dst lhs rhs)
        (.xreg rs2) (.vreg JoltISA.amoOldVReg) rs2
        old
        (if (zopz0zI_s rs2Val old : Bool) then rs2Val else old)
        js_afterLoad js_afterMiddle := by
  exact
    amo_dword_select_middle_phase_run
      (fun dst lhs rhs => .SLT dst lhs rhs)
      (.xreg rs2) (.vreg JoltISA.amoOldVReg) rs2
      js_afterLoad rs2Val old
      (zero_extend (m := 64) (bool_to_bit (zopz0zI_s rs2Val old)))
      (if (zopz0zI_s rs2Val old : Bool) then rs2Val else old)
      hrs2
      (amo_dword_min_compare_phase_run rs2 js_afterLoad rs2Val old hrs2 hold)
      (amo_dword_select_value_of_slt old rs2Val)

/-- After the common dword load, the `AMOMIN.D` select middle block is ready for
the shared double-select program helper. -/
theorem amo_dword_min_middle_after_load
    (rs2 : regidx) (js : SailJoltState) (addr rs2Val : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail) :
    ∀ js_afterLoad : SailJoltState,
      js_afterLoad.sail = js.sail →
      js_afterLoad.vregs JoltISA.amoOldVReg =
        loaded_dword_at js.sail addr →
      ∃ js_afterMiddle : SailJoltState,
        AmoDwordSelectMiddleStep
          (fun dst lhs rhs => .SLT dst lhs rhs)
          (.xreg rs2) (.vreg JoltISA.amoOldVReg) rs2
          (loaded_dword_at js.sail addr)
          (if (zopz0zI_s rs2Val (loaded_dword_at js.sail addr) : Bool) then
            rs2Val
          else
            loaded_dword_at js.sail addr)
          js_afterLoad js_afterMiddle := by
  intro js_afterLoad hld_sail hld_old
  have hrs2_afterLoad :
      rX_bits rs2 js_afterLoad.sail =
        .ok rs2Val js_afterLoad.sail := by
    rw [hld_sail]
    exact hrs2
  exact
    amo_dword_min_middle_run rs2 js_afterLoad rs2Val
      (loaded_dword_at js.sail addr) hrs2_afterLoad hld_old

/-- `AMOMAX.D`'s comparison phase writes the signed less-than flag for
`old < rs2`. -/
theorem amo_dword_max_compare_phase_run
    (rs2 : regidx) (js : SailJoltState) (rs2Val old : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hold : js.vregs JoltISA.amoOldVReg = old) :
    ∃ js_afterCmp : SailJoltState,
      AmoDwordSelectCompareStep
        (fun dst lhs rhs => .SLT dst lhs rhs)
        (.vreg JoltISA.amoOldVReg) (.xreg rs2) old
        (zero_extend (m := 64) (bool_to_bit (zopz0zI_s old rs2Val)))
        js js_afterCmp := by
  let flag : BitVec 64 :=
    zero_extend (m := 64) (bool_to_bit (zopz0zI_s old rs2Val))
  let js_afterCmp : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.amoNewVReg then flag else js.vregs r }
  have hcmp_run :
      (JoltISA.execInstr
        (.SLT (.vreg JoltISA.amoNewVReg)
          (.vreg JoltISA.amoOldVReg) (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js_afterCmp := by
    rw [amo_dword_slt_run_vreg_vreg_xreg
      JoltISA.amoNewVReg JoltISA.amoOldVReg rs2 js rs2Val hrs2]
    unfold js_afterCmp flag
    rw [hold]
  refine ⟨js_afterCmp, ?_, ?_, ?_, ?_⟩
  · change
      (JoltISA.execProgram
        (amoDwordSelectComparePhase
          (fun dst lhs rhs => .SLT dst lhs rhs)
          (.vreg JoltISA.amoOldVReg) (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js_afterCmp
    unfold amoDwordSelectComparePhase
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterCmp hcmp_run]
    rfl
  · rfl
  · change (if JoltISA.amoNewVReg = JoltISA.amoNewVReg then flag
      else js.vregs JoltISA.amoNewVReg) =
      zero_extend (m := 64) (bool_to_bit (zopz0zI_s old rs2Val))
    rw [if_pos rfl]
  · change (if JoltISA.amoOldVReg = JoltISA.amoNewVReg then flag
      else js.vregs JoltISA.amoOldVReg) = old
    rw [if_neg (by decide), hold]

/-- `AMOMAX.D`'s select middle block chooses `rs2` exactly when `rs2 > old`
as signed dwords. -/
theorem amo_dword_max_middle_run
    (rs2 : regidx) (js_afterLoad : SailJoltState)
    (rs2Val old : BitVec 64)
    (hrs2 : rX_bits rs2 js_afterLoad.sail =
      .ok rs2Val js_afterLoad.sail)
    (hold : js_afterLoad.vregs JoltISA.amoOldVReg = old) :
    ∃ js_afterMiddle : SailJoltState,
      AmoDwordSelectMiddleStep
        (fun dst lhs rhs => .SLT dst lhs rhs)
        (.vreg JoltISA.amoOldVReg) (.xreg rs2) rs2
        old
        (if (zopz0zK_s rs2Val old : Bool) then rs2Val else old)
        js_afterLoad js_afterMiddle := by
  exact
    amo_dword_select_middle_phase_run
      (fun dst lhs rhs => .SLT dst lhs rhs)
      (.vreg JoltISA.amoOldVReg) (.xreg rs2) rs2
      js_afterLoad rs2Val old
      (zero_extend (m := 64) (bool_to_bit (zopz0zI_s old rs2Val)))
      (if (zopz0zK_s rs2Val old : Bool) then rs2Val else old)
      hrs2
      (amo_dword_max_compare_phase_run rs2 js_afterLoad rs2Val old hrs2 hold)
      (amo_dword_select_value_of_sgt old rs2Val)

/-- After the common dword load, the `AMOMAX.D` select middle block is ready for
the shared double-select program helper. -/
theorem amo_dword_max_middle_after_load
    (rs2 : regidx) (js : SailJoltState) (addr rs2Val : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail) :
    ∀ js_afterLoad : SailJoltState,
      js_afterLoad.sail = js.sail →
      js_afterLoad.vregs JoltISA.amoOldVReg =
        loaded_dword_at js.sail addr →
      ∃ js_afterMiddle : SailJoltState,
        AmoDwordSelectMiddleStep
          (fun dst lhs rhs => .SLT dst lhs rhs)
          (.vreg JoltISA.amoOldVReg) (.xreg rs2) rs2
          (loaded_dword_at js.sail addr)
          (if (zopz0zK_s rs2Val (loaded_dword_at js.sail addr) : Bool) then
            rs2Val
          else
            loaded_dword_at js.sail addr)
          js_afterLoad js_afterMiddle := by
  intro js_afterLoad hld_sail hld_old
  have hrs2_afterLoad :
      rX_bits rs2 js_afterLoad.sail =
        .ok rs2Val js_afterLoad.sail := by
    rw [hld_sail]
    exact hrs2
  exact
    amo_dword_max_middle_run rs2 js_afterLoad rs2Val
      (loaded_dword_at js.sail addr) hrs2_afterLoad hld_old

/-- `AMOMINU.D`'s select middle block chooses `rs2` exactly when `rs2 < old`
as unsigned dwords. -/
theorem amo_dword_minu_middle_run
    (rs2 : regidx) (js_afterLoad : SailJoltState)
    (rs2Val old : BitVec 64)
    (hrs2 : rX_bits rs2 js_afterLoad.sail =
      .ok rs2Val js_afterLoad.sail)
    (hold : js_afterLoad.vregs JoltISA.amoOldVReg = old) :
    ∃ js_afterMiddle : SailJoltState,
      AmoDwordSelectMiddleStep
        (fun dst lhs rhs => .SLTU dst lhs rhs)
        (.xreg rs2) (.vreg JoltISA.amoOldVReg) rs2
        old
        (if (zopz0zI_u rs2Val old : Bool) then rs2Val else old)
        js_afterLoad js_afterMiddle := by
  exact
    amo_dword_select_middle_phase_run
      (fun dst lhs rhs => .SLTU dst lhs rhs)
      (.xreg rs2) (.vreg JoltISA.amoOldVReg) rs2
      js_afterLoad rs2Val old (jolt_sltu_value rs2Val old)
      (if (zopz0zI_u rs2Val old : Bool) then rs2Val else old)
      hrs2
      (amo_dword_minu_compare_phase_run rs2 js_afterLoad rs2Val old hrs2 hold)
      (amo_dword_select_value_of_sltu old rs2Val)

/-- After the common dword load, the `AMOMINU.D` select middle block is ready
for the shared double-select program helper. -/
theorem amo_dword_minu_middle_after_load
    (rs2 : regidx) (js : SailJoltState) (addr rs2Val : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail) :
    ∀ js_afterLoad : SailJoltState,
      js_afterLoad.sail = js.sail →
      js_afterLoad.vregs JoltISA.amoOldVReg =
        loaded_dword_at js.sail addr →
      ∃ js_afterMiddle : SailJoltState,
        AmoDwordSelectMiddleStep
          (fun dst lhs rhs => .SLTU dst lhs rhs)
          (.xreg rs2) (.vreg JoltISA.amoOldVReg) rs2
          (loaded_dword_at js.sail addr)
          (if (zopz0zI_u rs2Val (loaded_dword_at js.sail addr) : Bool) then
            rs2Val
          else
            loaded_dword_at js.sail addr)
          js_afterLoad js_afterMiddle := by
  intro js_afterLoad hld_sail hld_old
  have hrs2_afterLoad :
      rX_bits rs2 js_afterLoad.sail =
        .ok rs2Val js_afterLoad.sail := by
    rw [hld_sail]
    exact hrs2
  exact
    amo_dword_minu_middle_run rs2 js_afterLoad rs2Val
      (loaded_dword_at js.sail addr) hrs2_afterLoad hld_old

/-- `AMOMAXU.D`'s comparison phase writes the unsigned less-than flag for
`old < rs2`. -/
theorem amo_dword_maxu_compare_phase_run
    (rs2 : regidx) (js : SailJoltState) (rs2Val old : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hold : js.vregs JoltISA.amoOldVReg = old) :
    ∃ js_afterCmp : SailJoltState,
      AmoDwordSelectCompareStep
        (fun dst lhs rhs => .SLTU dst lhs rhs)
        (.vreg JoltISA.amoOldVReg) (.xreg rs2) old
        (jolt_sltu_value old rs2Val) js js_afterCmp := by
  let flag : BitVec 64 := jolt_sltu_value old rs2Val
  let js_afterCmp : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.amoNewVReg then flag else js.vregs r }
  have hcmp_run :
      (JoltISA.execInstr
        (.SLTU (.vreg JoltISA.amoNewVReg)
          (.vreg JoltISA.amoOldVReg) (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js_afterCmp := by
    rw [amo_dword_sltu_run_vreg_vreg_xreg
      JoltISA.amoNewVReg JoltISA.amoOldVReg rs2 js rs2Val hrs2]
    unfold js_afterCmp flag
    rw [hold]
  refine ⟨js_afterCmp, ?_, ?_, ?_, ?_⟩
  · change
      (JoltISA.execProgram
        (amoDwordSelectComparePhase
          (fun dst lhs rhs => .SLTU dst lhs rhs)
          (.vreg JoltISA.amoOldVReg) (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js_afterCmp
    unfold amoDwordSelectComparePhase
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterCmp hcmp_run]
    rfl
  · rfl
  · change (if JoltISA.amoNewVReg = JoltISA.amoNewVReg then flag
      else js.vregs JoltISA.amoNewVReg) = jolt_sltu_value old rs2Val
    rw [if_pos rfl]
  · change (if JoltISA.amoOldVReg = JoltISA.amoNewVReg then flag
      else js.vregs JoltISA.amoOldVReg) = old
    rw [if_neg (by decide), hold]

/-- `AMOMAXU.D`'s select middle block chooses `rs2` exactly when `rs2 > old`
as unsigned dwords. -/
theorem amo_dword_maxu_middle_run
    (rs2 : regidx) (js_afterLoad : SailJoltState)
    (rs2Val old : BitVec 64)
    (hrs2 : rX_bits rs2 js_afterLoad.sail =
      .ok rs2Val js_afterLoad.sail)
    (hold : js_afterLoad.vregs JoltISA.amoOldVReg = old) :
    ∃ js_afterMiddle : SailJoltState,
      AmoDwordSelectMiddleStep
        (fun dst lhs rhs => .SLTU dst lhs rhs)
        (.vreg JoltISA.amoOldVReg) (.xreg rs2) rs2
        old
        (if (zopz0zK_u rs2Val old : Bool) then rs2Val else old)
        js_afterLoad js_afterMiddle := by
  exact
    amo_dword_select_middle_phase_run
      (fun dst lhs rhs => .SLTU dst lhs rhs)
      (.vreg JoltISA.amoOldVReg) (.xreg rs2) rs2
      js_afterLoad rs2Val old (jolt_sltu_value old rs2Val)
      (if (zopz0zK_u rs2Val old : Bool) then rs2Val else old)
      hrs2
      (amo_dword_maxu_compare_phase_run rs2 js_afterLoad rs2Val old hrs2 hold)
      (amo_dword_select_value_of_sgtu old rs2Val)

/-- After the common dword load, the `AMOMAXU.D` select middle block is ready for
the shared double-select program helper. -/
theorem amo_dword_maxu_middle_after_load
    (rs2 : regidx) (js : SailJoltState) (addr rs2Val : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail) :
    ∀ js_afterLoad : SailJoltState,
      js_afterLoad.sail = js.sail →
      js_afterLoad.vregs JoltISA.amoOldVReg =
        loaded_dword_at js.sail addr →
      ∃ js_afterMiddle : SailJoltState,
        AmoDwordSelectMiddleStep
          (fun dst lhs rhs => .SLTU dst lhs rhs)
          (.vreg JoltISA.amoOldVReg) (.xreg rs2) rs2
          (loaded_dword_at js.sail addr)
          (if (zopz0zK_u rs2Val (loaded_dword_at js.sail addr) : Bool) then
            rs2Val
          else
            loaded_dword_at js.sail addr)
          js_afterLoad js_afterMiddle := by
  intro js_afterLoad hld_sail hld_old
  have hrs2_afterLoad :
      rX_bits rs2 js_afterLoad.sail =
        .ok rs2Val js_afterLoad.sail := by
    rw [hld_sail]
    exact hrs2
  exact
    amo_dword_maxu_middle_run rs2 js_afterLoad rs2Val
      (loaded_dword_at js.sail addr) hrs2_afterLoad hld_old

/-- After a pure AMO middle instruction, `SD amoNewVReg, 0(rs1)` writes the
computed dword result. -/
theorem amo_dword_store_vreg_result_after_middle_aligned_run
    {op : amoop} {amoAddr : BitVec 64}
    (rs1 : regidx) (js js_afterMiddle : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr result : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (h_mem : AmoMemoryAssumptions op 8 addr amoAddr js.sail)
    (h_align : addr &&& (7 : BitVec 64) = 0)
    (hmiddle_sail : js_afterMiddle.sail = js.sail)
    (hmiddle_result : js_afterMiddle.vregs JoltISA.amoNewVReg = result) :
    ∃ js_afterStore : SailJoltState,
      (JoltISA.execInstr
        (.SD (.xreg rs1) (.vreg JoltISA.amoNewVReg) (0 : BitVec 12))).run
          js_afterMiddle =
        .ok RETIRE_SUCCESS js_afterStore ∧
      js_afterStore.sail =
        state_after_dword_store js_afterMiddle.sail addr result ∧
      js_afterStore.vregs = js_afterMiddle.vregs := by
  have haligned := amo_dword_aligned_access addr h_align
  have hwrite :
      vmem_write_addr (Virtaddr addr) 8 result
        (Store Data) false false false js.sail =
        .ok (Ok true) (state_after_dword_store js.sail addr result) :=
    vmem_write_addr_dword_store_reduces addr result js.sail hcfg
      haligned.toAlignedAccess
      (AmoMemoryAssumptions.jolt_store_mem h_mem).pmp
      (AmoMemoryAssumptions.jolt_store_mem h_mem).mmio
  have hrs1_afterMiddle :
      rX_bits rs1 js_afterMiddle.sail =
        .ok addr js_afterMiddle.sail := by
    rw [hmiddle_sail]
    exact hrs1
  have hwrite_afterMiddle :
      vmem_write_addr (Virtaddr addr) 8 result
        (Store Data) false false false js_afterMiddle.sail =
        .ok (Ok true)
          (state_after_dword_store js_afterMiddle.sail addr result) := by
    rw [hmiddle_sail]
    exact hwrite
  exact
    amo_dword_sd_vreg_result_run rs1 JoltISA.amoNewVReg js_afterMiddle
      addr result hrs1_afterMiddle hmiddle_result hwrite_afterMiddle

/-- After the AMO store, the final `ADDI rd, old, 0` writes the loaded old
dword into `rd`. -/
theorem amo_dword_writeback_after_store_run
    (rd : regidx) (js js_afterStore : SailJoltState)
    (addr oldVal : BitVec 64)
    (hstore_vregs : js_afterStore.vregs = js.vregs)
    (hold : js.vregs JoltISA.amoOldVReg = oldVal) :
    ∃ js_afterWrite : SailJoltState,
      (JoltISA.execInstr
        (.ADDI (.xreg rd) (.vreg JoltISA.amoOldVReg) (0 : BitVec 12))).run
          js_afterStore =
        .ok RETIRE_SUCCESS js_afterWrite ∧
      js_afterWrite.sail = stateAfterWrite js_afterStore.sail rd oldVal ∧
      js_afterWrite.vregs = js_afterStore.vregs := by
  have hold_afterStore :
      js_afterStore.vregs JoltISA.amoOldVReg = oldVal := by
    rw [hstore_vregs]
    exact hold
  exact amo_dword_addi_writeback_old_run rd js_afterStore oldVal hold_afterStore

/-- Shared aligned concrete execution for `amoDoubleBinopProgram`.

The prelude and postlude are common to `AMOADD.D`, `AMOXOR.D`, `AMOAND.D`,
and `AMOOR.D`: assert dword alignment, load the old dword, run one pure middle
instruction into `amoNewVReg`, store that new dword, then write the old dword
back to `rd`. -/
theorem amo_dword_double_binop_program_concrete_aligned
    (op : amoop) (binop : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr result : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (h_mem : AmoMemoryAssumptions op 8 addr addr js.sail)
    (h_align : addr &&& (7 : BitVec 64) = 0)
    (hmiddle :
      ∀ js_afterLoad : SailJoltState,
        js_afterLoad.sail = js.sail →
        js_afterLoad.vregs JoltISA.amoOldVReg =
          loaded_dword_at js.sail addr →
        ∃ js_afterMiddle : SailJoltState,
          AmoDwordMiddleStep
            (binop (.vreg JoltISA.amoNewVReg)
              (.vreg JoltISA.amoOldVReg) (.xreg rs2))
            (loaded_dword_at js.sail addr) result
            js_afterLoad js_afterMiddle) :
    ∃ jsf : SailJoltState,
      (JoltISA.execProgram (JoltISA.amoDoubleBinopProgram binop rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail = amoDwordFinalSailState rd js.sail addr result := by
  have hassert :=
    amo_dword_virtual_assert_aligned_run rs1 js addr hrs1 h_align
  obtain ⟨js_afterLoad, hld, hld_sail, hld_old⟩ :=
    amo_dword_load_old_aligned_run rs1 js hcfg addr hrs1 h_mem h_align
  obtain ⟨js_afterMiddle, hmiddle_step⟩ :=
    hmiddle js_afterLoad hld_sail hld_old
  have hmiddle_sail : js_afterMiddle.sail = js.sail := by
    rw [hmiddle_step.sail, hld_sail]
  obtain ⟨js_afterStore, hsd, hsd_sail, hsd_vregs⟩ :=
    amo_dword_store_vreg_result_after_middle_aligned_run
      rs1 js js_afterMiddle hcfg addr result hrs1 h_mem h_align
      hmiddle_sail hmiddle_step.result_vreg
  obtain ⟨js_afterWrite, haddi, haddi_sail, _haddi_vregs⟩ :=
    amo_dword_writeback_after_store_run rd js_afterMiddle js_afterStore addr
      (loaded_dword_at js.sail addr) hsd_vregs hmiddle_step.old_vreg
  refine ⟨js_afterWrite, ?_, ?_⟩
  · unfold JoltISA.amoDoubleBinopProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js hassert]
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterLoad hld]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterLoad js_afterMiddle
      hmiddle_step.run]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterMiddle js_afterStore hsd]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterStore js_afterWrite haddi]
    rfl
  · rw [haddi_sail, hsd_sail, hmiddle_sail]

/-- Shared misaligned concrete execution for `amoDoubleBinopProgram`.

All dword double-binop expansions begin with the same dword alignment
assertion, so a misaligned address stops before the load, middle instruction,
store, or writeback can run. -/
theorem amo_dword_double_binop_program_concrete_misaligned
    (binop : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (addr : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (h_align : addr &&& (7 : BitVec 64) ≠ 0) :
    (JoltISA.execProgram (JoltISA.amoDoubleBinopProgram binop rs2 rs1 rd)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr addr, ExceptionType.E_SAMO_Addr_Align ())) js := by
  let rest : JoltISA.Program :=
    .instr (.LD (.vreg JoltISA.amoOldVReg) (.xreg rs1) (0 : BitVec 12)) <|
    .instr (binop (.vreg JoltISA.amoNewVReg)
      (.vreg JoltISA.amoOldVReg) (.xreg rs2)) <|
    .instr (.SD (.xreg rs1) (.vreg JoltISA.amoNewVReg) (0 : BitVec 12)) <|
    .instr (.ADDI (.xreg rd) (.vreg JoltISA.amoOldVReg) (0 : BitVec 12)) <|
    .done RETIRE_SUCCESS
  let e := (Virtaddr addr, ExceptionType.E_SAMO_Addr_Align ())
  have hassert :
      (JoltISA.execInstr
        (.VirtualAssertDwordAlignment rs1 (0 : BitVec 12)
          (ExceptionType.E_SAMO_Addr_Align ()))).run js =
      .ok (ExecutionResult.Memory_Exception e) js := by
    exact amo_dword_virtual_assert_misaligned_run rs1 js addr hrs1 h_align
  unfold JoltISA.amoDoubleBinopProgram
  exact
    JoltISA.execProgram_instr_run_memory_exception
      (.VirtualAssertDwordAlignment rs1 (0 : BitVec 12)
        (ExceptionType.E_SAMO_Addr_Align ()))
      rest js js e hassert

/-- An 8-byte aligned virtual address satisfies Sail's aligned-address test. -/
theorem amo_dword_is_aligned_vaddr_true (addr : BitVec 64)
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
theorem amo_dword_is_aligned_paddr_true (addr : BitVec 64)
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
theorem amo_dword_read_ram_reserved_eq_loaded_dword
    (addr : BitVec 64) (s : SailState)
    (h_pop : ∀ a : Nat, s.mem.get? a ≠ none)
    (h_no_ovf : addr.toNat + 7 < 2 ^ 64) :
    LeanRV64D.Functions.read_ram read_kind.Read_RISCV_reserved
      (physaddr.Physaddr addr) 8 false s =
    .ok (loaded_dword_at s addr, default_meta) s := by
  change
    LeanRV64D.Functions.read_ram read_kind.Read_plain
      (physaddr.Physaddr addr) 8 false s =
    .ok (loaded_dword_at s addr, default_meta) s
  exact read_ram_eq_loaded_dword addr s h_pop h_no_ovf

/-- The checked AMO dword read reduces to the canonical loaded dword when PMP
and readable-MMIO checks say the access is ordinary RAM. -/
theorem amo_dword_checked_mem_read_eq_loaded_dword
    (op : amoop) (addr : BitVec 64) (s : SailState)
    (h_pop : ∀ a : Nat, s.mem.get? a ≠ none)
    (h_no_ovf : addr.toNat + 7 < 2 ^ 64)
    (hfm : FlatAtomicMem op addr 8 s) :
    checked_mem_read (Atomic (op, Data, Data)) Privilege.Machine
      (physaddr.Physaddr addr) 8 false false true false s =
    .ok (Ok (loaded_dword_at s addr, default_meta)) s := by
  unfold checked_mem_read
  simp only [bind, EStateM.bind, pure, EStateM.pure, hfm.pmp, hfm.readable,
    Bool.false_eq_true, if_false]
  unfold read_kind_of_flags
  simp only [pure, EStateM.pure]
  rw [amo_dword_read_ram_reserved_eq_loaded_dword addr s h_pop h_no_ovf]

/-- A full AMO dword memory read reduces through privilege, alignment, PMP, and
RAM checks to the canonical loaded dword. -/
theorem amo_dword_mem_read_eq_loaded_dword
    (op : amoop) (addr : BitVec 64) (s : SailState)
    (hcfg : JoltConfig s)
    (h_no_ovf : addr.toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (7 : BitVec 64) = 0)
    (hfm : FlatAtomicMem op addr 8 s) :
    mem_read (Atomic (op, Data, Data))
      (physaddr.Physaddr addr) 8 false false true s =
    .ok (Ok (loaded_dword_at s addr)) s := by
  obtain ⟨mval, h_ms_regs, h_mprv⟩ := hcfg.mstatus_ok
  have h_ms_read := readReg_eq Register.mstatus s mval h_ms_regs
  have h_priv := readReg_eq Register.cur_privilege s Privilege.Machine hcfg.machine_mode
  have h_paddr_aligned := amo_dword_is_aligned_paddr_true addr h_align
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
  rw [amo_dword_checked_mem_read_eq_loaded_dword
    op addr s hcfg.mem_populated h_no_ovf hfm]
  rfl

/-- The AMO dword write effective-address check succeeds for aligned physical
addresses. -/
theorem amo_dword_mem_write_ea_ok
    (addr : BitVec 64) (s : SailState)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    mem_write_ea (physaddr.Physaddr addr) 8 false false true s =
      .ok (Ok ()) s := by
  have h_paddr_aligned := amo_dword_is_aligned_paddr_true addr h_align
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

/-- Sail's conditional AMO dword RAM write is the canonical direct hashmap
dword store. -/
theorem amo_dword_write_ram_conditional_eq_state_after_dword_store
    (addr data : BitVec 64) (s : SailState) :
    LeanRV64D.Functions.write_ram write_kind.Write_RISCV_conditional
      (physaddr.Physaddr addr) 8 data default_meta s =
    .ok true (state_after_dword_store s addr data) := by
  simp only [LeanRV64D.Functions.write_ram,
    Sail.ConcurrencyInterfaceV1.sail_mem_write,
    PreSail.ConcurrencyInterfaceV1.sail_mem_write,
    PreSail.writeBytes,
    PreSail.writeByte,
    state_after_dword_store,
    dword_byte]
  rfl

/-- A full AMO dword memory-value write reduces through privilege, alignment,
PMP, and RAM checks to the canonical dword store. -/
theorem amo_dword_mem_write_value_eq_state_after_dword_store
    (op : amoop) (addr data : BitVec 64) (s : SailState)
    (hcfg : JoltConfig s)
    (h_align : addr &&& (7 : BitVec 64) = 0)
    (hfm : FlatAtomicMem op addr 8 s) :
    mem_write_value (physaddr.Physaddr addr) 8 data
      (Atomic (op, Data, Data)) false false true s =
    .ok (Ok true) (state_after_dword_store s addr data) := by
  obtain ⟨mval, h_ms_regs, h_mprv⟩ := hcfg.mstatus_ok
  have h_ms_read := readReg_eq Register.mstatus s mval h_ms_regs
  have h_priv := readReg_eq Register.cur_privilege s Privilege.Machine hcfg.machine_mode
  have h_paddr_aligned := amo_dword_is_aligned_paddr_true addr h_align
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
  rw [amo_dword_write_ram_conditional_eq_state_after_dword_store addr data s]

/-- The final AMO writeback state exists and is exactly the canonical dword AMO
final state. -/
theorem amo_dword_writeback_old_shape
    (rd : regidx) (s : SailState) (addr result : BitVec 64) :
    ∃ writebackState : SailState,
      wX_bits rd (loaded_dword_at s addr)
        (state_after_dword_store s addr result) =
        .ok () writebackState ∧
      writebackState = amoDwordFinalSailState rd s addr result := by
  obtain ⟨writebackState, hwriteback⟩ :=
    wX_shape rd (loaded_dword_at s addr)
      (state_after_dword_store s addr result)
  refine ⟨writebackState, hwriteback, ?_⟩
  exact
    wX_bits_eq_stateAfterWrite rd (loaded_dword_at s addr)
      (state_after_dword_store s addr result) writebackState hwriteback

/-- The old dword writeback is unaffected by the generated 64-bit width casts. -/
theorem amo_dword_writeback_loaded_direct
    (rd : regidx) (s writebackState : SailState) (addr result : BitVec 64)
    (hwriteback :
      wX_bits rd (loaded_dword_at s addr)
        (state_after_dword_store s addr result) =
        .ok () writebackState) :
    wX_bits rd
      (sign_extend (m := 64)
        (BitVec.setWidth (8 * 8) (loaded_dword_at s addr)))
      (state_after_dword_store s addr result) =
      .ok () writebackState := by
  rw [amo_dword_setWidth_8x8_eq_self]
  rw [amo_dword_sign_extend_64_eq_self]
  exact hwriteback

/-- The result expression generated by Sail's 64-bit non-CAS AMO executor after
the dword load and `rs2` read have reduced. -/
abbrev amoDwordSailResult
    (op : amoop) (rs2Val loaded : BitVec 64) : BitVec 64 :=
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

/-- The Sail AMO write of the computed dword result reduces to the canonical
hashmap dword store. -/
theorem amo_dword_mem_write_value_sail_result
    (op : amoop) (addr rs2Val result : BitVec 64) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (h_mem : AmoMemoryAssumptions op 8 addr addr js.sail)
    (h_align : addr &&& (7 : BitVec 64) = 0)
    (hresult :
      amoDwordSailResult op
        (show BitVec (8 * 8) from
          trunc (m := (((8 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
        (BitVec.setWidth (8 * 8) (loaded_dword_at js.sail addr)) =
      result) :
    mem_write_value (physaddr.Physaddr addr) 8
      (sign_extend (m := ((8 : Int) * ((8 : Nat) : Int)).toNat)
        (amoDwordSailResult op
          (show BitVec (8 * 8) from
            trunc (m := (((8 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
          (BitVec.setWidth (8 * 8) (loaded_dword_at js.sail addr))))
      (Atomic (op, Data, Data)) false false true js.sail =
    .ok (Ok true) (state_after_dword_store js.sail addr result) := by
  rw [hresult]
  change
    mem_write_value (physaddr.Physaddr addr) 8
      (sign_extend (m := 8 * 8) result)
      (Atomic (op, Data, Data)) false false true js.sail =
    .ok (Ok true) (state_after_dword_store js.sail addr result)
  rw [amo_dword_sign_extend_8x8_eq_self]
  exact
    amo_dword_mem_write_value_eq_state_after_dword_store
      op addr result js.sail hcfg h_align h_mem.sail_atomic_mem

/-- Once the aligned AMO setup facts have been reduced, the generated Sail
executor follows the concrete non-CAS write path and retires successfully. -/
theorem execute_AMO_dword_non_cas_aligned_core
    (op : amoop) (rs2 rs1 rd : regidx) (js : SailJoltState)
    (addr rs2Val result rdVal : BitVec 64)
    (writebackState : SailState)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd_read : rX_bits rd js.sail = .ok rdVal js.sail)
    (hnot_cas : (op == amoop.AMOCAS) = false)
    (h_vaddr_aligned : is_aligned_vaddr (Virtaddr addr) 8 = true)
    (htranslate :
      translateAddr (Virtaddr addr) (Atomic (op, Data, Data)) js.sail =
        .ok (Ok (physaddr.Physaddr addr, init_ext_ptw)) js.sail)
    (hea :
      mem_write_ea (physaddr.Physaddr addr) 8 false false true js.sail =
        .ok (Ok ()) js.sail)
    (hread :
      mem_read (Atomic (op, Data, Data))
        (physaddr.Physaddr addr) 8 false false true js.sail =
        .ok (Ok (loaded_dword_at js.sail addr)) js.sail)
    (hwrite_value :
      mem_write_value (physaddr.Physaddr addr) 8
        (sign_extend (m := ((8 : Int) * ((8 : Nat) : Int)).toNat)
          (amoDwordSailResult op
            (show BitVec (8 * 8) from
              trunc (m := (((8 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
            (BitVec.setWidth (8 * 8) (loaded_dword_at js.sail addr))))
        (Atomic (op, Data, Data)) false false true js.sail =
        .ok (Ok true) (state_after_dword_store js.sail addr result))
    (hwriteback_loaded_direct :
      wX_bits rd
        (sign_extend (m := 64)
          (BitVec.setWidth (8 * 8) (loaded_dword_at js.sail addr)))
        (state_after_dword_store js.sail addr result) =
        .ok () writebackState)
    (hwriteback_state :
      writebackState = amoDwordFinalSailState rd js.sail addr result) :
    (execute_AMO op false false rs2 rs1 8 rd).run js.sail =
      .ok RETIRE_SUCCESS (amoDwordFinalSailState rd js.sail addr result) := by
  have haddr0 := amo_dword_zero_sail_addr addr
  cases hop : op
  case AMOCAS =>
    rw [hop] at hnot_cas
    cases hnot_cas
  all_goals
    have hcas_check : decide (op.ctorIdx = amoop.AMOCAS.ctorIdx) = false := by
      rw [hop]
      decide
    rw [hop] at htranslate hread hcas_check hwrite_value
    simp only [amoDwordSailResult] at hwrite_value
    unfold execute_AMO
    simp only [bind, pure]
    unfold Sail.assert LeanRV64D.Functions.xlen_bytes
    simp only [amo_dword_width_assert_true, PreSail.assert, pure, EStateM.run, if_true]
    unfold SailME.run PreSail.PreSailME.run
    simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
      ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
      ExceptT.pure, ExceptT.lift, MonadLift.monadLift, liftM, monadLift,
      Functor.map, SailME.throw, PreSail.PreSailME.throw,
      MonadExceptOf.throw, ext_data_get_addr, hrs1, haddr0,
      h_vaddr_aligned, LeanRV64D.Functions.not, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, htranslate, amo_dword_width8_true, hrs2,
      hea, hread, hrd_read, hcas_check, Bool.false_and,
      instBEqAmoop.beq, BEq.beq]
    rw [hwrite_value]
    simp only [EStateM.bind, EStateM.map, ExceptT.bindCont, EStateM.pure,
      hwriteback_loaded_direct, hwriteback_state]

/-- Shared Sail-side aligned reduction for 64-bit non-CAS AMOs.

The generated Sail code reads `rd` while evaluating the AMOCAS guard, even when
`op` is later shown not to be AMOCAS. Callers therefore supply `hrd`. -/
theorem execute_AMO_dword_non_cas_aligned
    (op : amoop) (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val result : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryAssumptions op 8 addr addr js.sail)
    (h_align : addr &&& (7 : BitVec 64) = 0)
    (hnot_cas : (op == amoop.AMOCAS) = false)
    (hresult :
      amoDwordSailResult op
        (show BitVec (8 * 8) from
          trunc (m := (((8 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
        (BitVec.setWidth (8 * 8) (loaded_dword_at js.sail addr)) =
      result) :
    (execute_AMO op false false rs2 rs1 8 rd).run js.sail =
      .ok RETIRE_SUCCESS (amoDwordFinalSailState rd js.sail addr result) := by
  obtain ⟨rdVal, hrd_read⟩ := hrd
  obtain ⟨writebackState, hwriteback, hwriteback_state⟩ :=
    amo_dword_writeback_old_shape rd js.sail addr result
  exact
    execute_AMO_dword_non_cas_aligned_core
      op rs2 rs1 rd js addr rs2Val result rdVal writebackState
      hrs1 hrs2 hrd_read hnot_cas
      (amo_dword_is_aligned_vaddr_true addr h_align)
      (translateAddr_atomic_data_of_joltConfig op addr js.sail hcfg)
      (amo_dword_mem_write_ea_ok addr js.sail h_align)
      (amo_dword_mem_read_eq_loaded_dword op addr js.sail hcfg
        (amo_dword_aligned_no_ovf addr h_align) h_align h_mem.sail_atomic_mem)
      (amo_dword_mem_write_value_sail_result
        op addr rs2Val result js hcfg h_mem h_align hresult)
      (amo_dword_writeback_loaded_direct
        rd js.sail writebackState addr result hwriteback)
      hwriteback_state

/-- Shared aligned public branch for dword AMO double-binop expansions.

Callers provide only the pure middle-step proof and the Sail result bridge.
The common assert/load/store/writeback Jolt execution and native Sail AMO
reduction are discharged here. -/
theorem amo_dword_double_binop_program_eq_sail_aligned
    (op : amoop) (binop : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val result : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryAssumptions op 8 addr addr js.sail)
    (h_align : addr &&& (7 : BitVec 64) = 0)
    (hnot_cas : (op == amoop.AMOCAS) = false)
    (hmiddle :
      ∀ js_afterLoad : SailJoltState,
        js_afterLoad.sail = js.sail →
        js_afterLoad.vregs JoltISA.amoOldVReg =
          loaded_dword_at js.sail addr →
        ∃ js_afterMiddle : SailJoltState,
          AmoDwordMiddleStep
            (binop (.vreg JoltISA.amoNewVReg)
              (.vreg JoltISA.amoOldVReg) (.xreg rs2))
            (loaded_dword_at js.sail addr) result
            js_afterLoad js_afterMiddle)
    (hresult :
      amoDwordSailResult op
        (show BitVec (8 * 8) from
          trunc (m := (((8 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
        (BitVec.setWidth (8 * 8) (loaded_dword_at js.sail addr)) =
      result) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoDoubleBinopProgram binop rs2 rs1 rd)).run js) =
      (execute_AMO op false false rs2 rs1 8 rd).run js.sail := by
  rcases amo_dword_double_binop_program_concrete_aligned
      op binop rs2 rs1 rd js hcfg addr result hrs1 h_mem h_align hmiddle with
    ⟨jsf, hjolt, hjolt_sail⟩
  have hsail :=
    execute_AMO_dword_non_cas_aligned
      op rs2 rs1 rd js hcfg addr rs2Val result
      hrs1 hrs2 hrd h_mem h_align hnot_cas hresult
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail, hsail]

/-- Shared Sail-side misaligned reduction for native 64-bit AMOs. -/
theorem execute_AMO_dword_misaligned
    (op : amoop) (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_align : addr &&& (7 : BitVec 64) ≠ 0) :
    (execute_AMO op false false rs2 rs1 8 rd).run js.sail =
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

/-- Shared misaligned public branch for dword AMO double-binop expansions. -/
theorem amo_dword_double_binop_program_eq_sail_misaligned
    (op : amoop) (binop : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_align : addr &&& (7 : BitVec 64) ≠ 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoDoubleBinopProgram binop rs2 rs1 rd)).run js) =
      (execute_AMO op false false rs2 rs1 8 rd).run js.sail := by
  have hjolt :=
    amo_dword_double_binop_program_concrete_misaligned
      binop rs2 rs1 rd js addr hrs1 h_align
  have hsail :=
    execute_AMO_dword_misaligned
      op rs2 rs1 rd js hcfg addr rs2Val hrs1 hrs2 h_align
  rw [hjolt]
  simp only [projectResult, project]
  symm
  exact hsail

/-- Shared full theorem for dword AMO double-binop expansions.

The theorem exposes no alignment hypothesis. It follows the exact leading
dword alignment predicate used by both the Jolt expansion and native Sail AMO
execution, then delegates to the shared aligned or misaligned branch. -/
theorem amo_dword_double_binop_program_eq_sail
    (op : amoop) (binop : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val result : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryAssumptions op 8 addr addr js.sail)
    (hnot_cas : (op == amoop.AMOCAS) = false)
    (hmiddle :
      ∀ js_afterLoad : SailJoltState,
        js_afterLoad.sail = js.sail →
        js_afterLoad.vregs JoltISA.amoOldVReg =
          loaded_dword_at js.sail addr →
        ∃ js_afterMiddle : SailJoltState,
          AmoDwordMiddleStep
            (binop (.vreg JoltISA.amoNewVReg)
              (.vreg JoltISA.amoOldVReg) (.xreg rs2))
            (loaded_dword_at js.sail addr) result
            js_afterLoad js_afterMiddle)
    (hresult :
      amoDwordSailResult op
        (show BitVec (8 * 8) from
          trunc (m := (((8 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
        (BitVec.setWidth (8 * 8) (loaded_dword_at js.sail addr)) =
      result) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoDoubleBinopProgram binop rs2 rs1 rd)).run js) =
      (execute_AMO op false false rs2 rs1 8 rd).run js.sail := by
  by_cases h_align : addr &&& (7 : BitVec 64) = 0
  · exact
      amo_dword_double_binop_program_eq_sail_aligned
        op binop rs2 rs1 rd js hcfg addr rs2Val result
        hrs1 hrs2 hrd h_mem h_align hnot_cas hmiddle hresult
  · exact
      amo_dword_double_binop_program_eq_sail_misaligned
        op binop rs2 rs1 rd js hcfg addr rs2Val hrs1 hrs2 h_align

/-- Shared aligned concrete execution for `amoDoubleSelectProgram`.

The select form uses the same assert/load/store/writeback shell as dword
double-binops, with a phased comparison-plus-select middle block. -/
theorem amo_dword_double_select_program_concrete_aligned
    (op : amoop)
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src)
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr result : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (h_mem : AmoMemoryAssumptions op 8 addr addr js.sail)
    (h_align : addr &&& (7 : BitVec 64) = 0)
    (hmiddle :
      ∀ js_afterLoad : SailJoltState,
        js_afterLoad.sail = js.sail →
        js_afterLoad.vregs JoltISA.amoOldVReg =
          loaded_dword_at js.sail addr →
        ∃ js_afterMiddle : SailJoltState,
          AmoDwordSelectMiddleStep cmpInstr cmpLhs cmpRhs rs2
            (loaded_dword_at js.sail addr) result
            js_afterLoad js_afterMiddle) :
    ∃ jsf : SailJoltState,
      (JoltISA.execProgram
        (JoltISA.amoDoubleSelectProgram cmpInstr cmpLhs cmpRhs rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail = amoDwordFinalSailState rd js.sail addr result := by
  have hassert :=
    amo_dword_virtual_assert_aligned_run rs1 js addr hrs1 h_align
  obtain ⟨js_afterLoad, hld, hld_sail, hld_old⟩ :=
    amo_dword_load_old_aligned_run rs1 js hcfg addr hrs1 h_mem h_align
  obtain ⟨js_afterMiddle, hmiddle_step⟩ :=
    hmiddle js_afterLoad hld_sail hld_old
  have hmiddle_sail : js_afterMiddle.sail = js.sail := by
    rw [hmiddle_step.sail, hld_sail]
  obtain ⟨js_afterStore, hsd, hsd_sail, hsd_vregs⟩ :=
    amo_dword_store_vreg_result_after_middle_aligned_run
      rs1 js js_afterMiddle hcfg addr result hrs1 h_mem h_align
      hmiddle_sail hmiddle_step.result_vreg
  obtain ⟨js_afterWrite, haddi, haddi_sail, _haddi_vregs⟩ :=
    amo_dword_writeback_after_store_run rd js_afterMiddle js_afterStore addr
      (loaded_dword_at js.sail addr) hsd_vregs hmiddle_step.old_vreg
  let tail : JoltISA.Program :=
    .instr (.SD (.xreg rs1) (.vreg JoltISA.amoNewVReg) (0 : BitVec 12)) <|
    .instr (.ADDI (.xreg rd) (.vreg JoltISA.amoOldVReg) (0 : BitVec 12)) <|
    .done RETIRE_SUCCESS
  have hmiddle_run := hmiddle_step.run tail
  unfold amoDwordSelectMiddleProgram amoDwordSelectComparePhase
    amoDwordSelectTailPhase at hmiddle_run
  change (JoltISA.execProgram
      (.instr (cmpInstr (.vreg JoltISA.amoNewVReg) cmpLhs cmpRhs) <|
       .instr (.SUB (.vreg JoltISA.amoTmpVReg)
         (.xreg rs2) (.vreg JoltISA.amoOldVReg)) <|
       .instr (.MUL (.vreg JoltISA.amoTmpVReg)
         (.vreg JoltISA.amoTmpVReg) (.vreg JoltISA.amoNewVReg)) <|
       .instr (.ADD (.vreg JoltISA.amoNewVReg)
         (.vreg JoltISA.amoOldVReg) (.vreg JoltISA.amoTmpVReg)) <|
       tail)).run js_afterLoad =
      (JoltISA.execProgram tail).run js_afterMiddle at hmiddle_run
  refine ⟨js_afterWrite, ?_, ?_⟩
  · unfold JoltISA.amoDoubleSelectProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js hassert]
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterLoad hld]
    rw [hmiddle_run]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterMiddle js_afterStore hsd]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterStore js_afterWrite haddi]
    rfl
  · rw [haddi_sail, hsd_sail, hmiddle_sail]

/-- Shared misaligned concrete execution for `amoDoubleSelectProgram`. -/
theorem amo_dword_double_select_program_concrete_misaligned
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src)
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (addr : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (h_align : addr &&& (7 : BitVec 64) ≠ 0) :
    (JoltISA.execProgram
      (JoltISA.amoDoubleSelectProgram cmpInstr cmpLhs cmpRhs rs2 rs1 rd)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr addr, ExceptionType.E_SAMO_Addr_Align ())) js := by
  let rest : JoltISA.Program :=
    .instr (.LD (.vreg JoltISA.amoOldVReg) (.xreg rs1) (0 : BitVec 12)) <|
    .instr (cmpInstr (.vreg JoltISA.amoNewVReg) cmpLhs cmpRhs) <|
    .instr (.SUB (.vreg JoltISA.amoTmpVReg)
      (.xreg rs2) (.vreg JoltISA.amoOldVReg)) <|
    .instr (.MUL (.vreg JoltISA.amoTmpVReg)
      (.vreg JoltISA.amoTmpVReg) (.vreg JoltISA.amoNewVReg)) <|
    .instr (.ADD (.vreg JoltISA.amoNewVReg)
      (.vreg JoltISA.amoOldVReg) (.vreg JoltISA.amoTmpVReg)) <|
    .instr (.SD (.xreg rs1) (.vreg JoltISA.amoNewVReg) (0 : BitVec 12)) <|
    .instr (.ADDI (.xreg rd) (.vreg JoltISA.amoOldVReg) (0 : BitVec 12)) <|
    .done RETIRE_SUCCESS
  let e := (Virtaddr addr, ExceptionType.E_SAMO_Addr_Align ())
  have hassert :
      (JoltISA.execInstr
        (.VirtualAssertDwordAlignment rs1 (0 : BitVec 12)
          (ExceptionType.E_SAMO_Addr_Align ()))).run js =
      .ok (ExecutionResult.Memory_Exception e) js := by
    exact amo_dword_virtual_assert_misaligned_run rs1 js addr hrs1 h_align
  unfold JoltISA.amoDoubleSelectProgram
  exact
    JoltISA.execProgram_instr_run_memory_exception
      (.VirtualAssertDwordAlignment rs1 (0 : BitVec 12)
        (ExceptionType.E_SAMO_Addr_Align ()))
      rest js js e hassert

/-- Shared aligned public branch for dword AMO double-select expansions. -/
theorem amo_dword_double_select_program_eq_sail_aligned
    (op : amoop)
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src)
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val result : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryAssumptions op 8 addr addr js.sail)
    (h_align : addr &&& (7 : BitVec 64) = 0)
    (hnot_cas : (op == amoop.AMOCAS) = false)
    (hmiddle :
      ∀ js_afterLoad : SailJoltState,
        js_afterLoad.sail = js.sail →
        js_afterLoad.vregs JoltISA.amoOldVReg =
          loaded_dword_at js.sail addr →
        ∃ js_afterMiddle : SailJoltState,
          AmoDwordSelectMiddleStep cmpInstr cmpLhs cmpRhs rs2
            (loaded_dword_at js.sail addr) result
            js_afterLoad js_afterMiddle)
    (hresult :
      amoDwordSailResult op
        (show BitVec (8 * 8) from
          trunc (m := (((8 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
        (BitVec.setWidth (8 * 8) (loaded_dword_at js.sail addr)) =
      result) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoDoubleSelectProgram cmpInstr cmpLhs cmpRhs rs2 rs1 rd)).run js) =
      (execute_AMO op false false rs2 rs1 8 rd).run js.sail := by
  rcases amo_dword_double_select_program_concrete_aligned
      op cmpInstr cmpLhs cmpRhs rs2 rs1 rd js hcfg addr result
      hrs1 h_mem h_align hmiddle with
    ⟨jsf, hjolt, hjolt_sail⟩
  have hsail :=
    execute_AMO_dword_non_cas_aligned
      op rs2 rs1 rd js hcfg addr rs2Val result
      hrs1 hrs2 hrd h_mem h_align hnot_cas hresult
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail, hsail]

/-- Shared misaligned public branch for dword AMO double-select expansions. -/
theorem amo_dword_double_select_program_eq_sail_misaligned
    (op : amoop)
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src)
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_align : addr &&& (7 : BitVec 64) ≠ 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoDoubleSelectProgram cmpInstr cmpLhs cmpRhs rs2 rs1 rd)).run js) =
      (execute_AMO op false false rs2 rs1 8 rd).run js.sail := by
  have hjolt :=
    amo_dword_double_select_program_concrete_misaligned
      cmpInstr cmpLhs cmpRhs rs2 rs1 rd js addr hrs1 h_align
  have hsail :=
    execute_AMO_dword_misaligned
      op rs2 rs1 rd js hcfg addr rs2Val hrs1 hrs2 h_align
  rw [hjolt]
  simp only [projectResult, project]
  symm
  exact hsail

/-- Shared full theorem for dword AMO double-select expansions. -/
theorem amo_dword_double_select_program_eq_sail
    (op : amoop)
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src)
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val result : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hrd : ∃ rdVal, rX_bits rd js.sail = .ok rdVal js.sail)
    (h_mem : AmoMemoryAssumptions op 8 addr addr js.sail)
    (hnot_cas : (op == amoop.AMOCAS) = false)
    (hmiddle :
      ∀ js_afterLoad : SailJoltState,
        js_afterLoad.sail = js.sail →
        js_afterLoad.vregs JoltISA.amoOldVReg =
          loaded_dword_at js.sail addr →
        ∃ js_afterMiddle : SailJoltState,
          AmoDwordSelectMiddleStep cmpInstr cmpLhs cmpRhs rs2
            (loaded_dword_at js.sail addr) result
            js_afterLoad js_afterMiddle)
    (hresult :
      amoDwordSailResult op
        (show BitVec (8 * 8) from
          trunc (m := (((8 : Nat) : Int) * (8 : Int)).toNat) rs2Val)
        (BitVec.setWidth (8 * 8) (loaded_dword_at js.sail addr)) =
      result) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoDoubleSelectProgram cmpInstr cmpLhs cmpRhs rs2 rs1 rd)).run js) =
      (execute_AMO op false false rs2 rs1 8 rd).run js.sail := by
  by_cases h_align : addr &&& (7 : BitVec 64) = 0
  · exact
      amo_dword_double_select_program_eq_sail_aligned
        op cmpInstr cmpLhs cmpRhs rs2 rs1 rd js hcfg addr rs2Val result
        hrs1 hrs2 hrd h_mem h_align hnot_cas hmiddle hresult
  · exact
      amo_dword_double_select_program_eq_sail_misaligned
        op cmpInstr cmpLhs cmpRhs rs2 rs1 rd js hcfg addr rs2Val
        hrs1 hrs2 h_align

end AtomicFamily

end
