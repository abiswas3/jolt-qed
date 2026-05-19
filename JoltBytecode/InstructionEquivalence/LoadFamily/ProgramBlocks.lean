import JoltBytecode.JoltISA.Semantics.Instructions
import JoltBytecode.InstructionEquivalence.LoadDefUtils
import JoltBytecode.InstructionEquivalence.ProofSupport

/-!
# Program blocks for load-family Jolt-ISA proofs

The load-family Rust expansions all have the same control-flow skeleton:

* compute the effective address in virtual register `v0`;
* align that address down and load the enclosing dword into virtual register
  `v1`;
* run a small virtual-register extraction program; and
* write the extracted value back to the architectural destination register.

This file proves those skeleton pieces once, at the level of
`JoltISA.execProgram`.  The instruction files (`LB_main`, `LWU_main`, …) should
then state their public theorems over the handwritten-for-now `JoltISA.Program`
objects and compose these blocks with their instruction-specific pure
bit-vector bridge lemmas.

The statements are intentionally tail-parametric: a block theorem says "after
this prefix retires, execution continues with `rest` from the boundary state."
That is the structured-program version of Ari's three-block proof style, and
it scales to generated programs because the theorem follows the interpreter
rather than an ad hoc do-block.
-/

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace LoadProgramBlocks

/-- The common dword setup block for load expansions with no leading alignment
assertion.

The prefix

`ADDI v0, rs1, imm; ANDI v1, v0, -8; LD v1, v1, 0`

computes the effective address `ea`, computes the enclosing 8-byte-aligned
dword address, reads that dword, and then continues with the supplied tail.
The resulting boundary facts are the only facts later extraction/writeback
blocks should need: `v0 = ea`, `v1 = loaded_dword_at daddr`, and the Sail state
has not changed. -/
theorem setupBlock (rest : JoltISA.Program)
    (imm : BitVec 12) (rs1 : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail) :
    ∃ js_load : SailJoltState,
      (JoltISA.execProgram
        (.instr (.ADDI (.vreg 0) (.xreg rs1) imm) <|
         .instr (.ANDI (.vreg 1) (.vreg 0) (-8 : BitVec 12)) <|
         .instr (.LD 1 1 0) rest)).run js =
        (JoltISA.execProgram rest).run js_load ∧
      js_load.sail = js.sail ∧
      js_load.vregs 0 = load_effective_address val imm ∧
      js_load.vregs 1 =
        loaded_dword_at js.sail (compute_aligned_dword_base_address val imm) := by
  let ea := load_effective_address val imm
  let daddr := compute_aligned_dword_base_address val imm
  let dword := loaded_dword_at js.sail daddr
  let js0 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (0 : JoltISA.VReg) then ea else js.vregs r }
  let js1 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (1 : JoltISA.VReg) then daddr else js0.vregs r }
  let js_load : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (1 : JoltISA.VReg) then dword else js1.vregs r }
  have haddi :
      (JoltISA.execInstr (.ADDI (.vreg 0) (.xreg rs1) imm)).run js =
        .ok RETIRE_SUCCESS js0 := by
    simpa [js0, ea, load_effective_address] using
      (JoltISA.addi_run_vreg_xreg (0 : JoltISA.VReg) rs1 imm js val hrx)
  have h8 : sign_extend (m := 64) (-8 : BitVec 12) = (-8 : BitVec 64) := by decide
  have handi :
      (JoltISA.execInstr (.ANDI (.vreg 1) (.vreg 0) (-8 : BitVec 12))).run js0 =
        .ok RETIRE_SUCCESS js1 := by
    simpa [js0, js1, ea, daddr, compute_aligned_dword_base_address,
      load_effective_address, h8] using
      (JoltISA.andi_run_vreg_vreg (1 : JoltISA.VReg) (0 : JoltISA.VReg)
        (-8 : BitVec 12) js0)
  have h_daddr_aligned : AlignedDwordAccess daddr := by
    simpa [daddr, compute_aligned_dword_base_address, load_effective_address,
      aligned_dword_addr_eq] using
      (aligned_dword_addr_is_aligned_dword_access val imm)
  have hd : DwordLoadAssumptions daddr js.sail :=
    { aligned := h_daddr_aligned
      translate := by simpa [daddr] using h_dword_translate
      phys := by simpa [daddr] using h_dword_phys }
  have hld_read :
      vmem_read_addr (Virtaddr (js1.vregs 1 + sign_extend (m := 64) (0 : BitVec 12))) 0 8
        (Load Data) false false false js1.sail =
        .ok (Ok dword) js1.sail := by
    have h0 : sign_extend (m := 64) (0 : BitVec 12) = (0 : BitVec 64) := by decide
    have haddr0 : daddr + sign_extend (m := 64) (0 : BitVec 12) = daddr := by
      rw [h0]
      bv_decide
    have hread := aligned_dword_vmem_read_reduces daddr js.sail hcfg hd
    rw [show js1.sail = js.sail by rfl]
    have hv1 : js1.vregs 1 = daddr := by
      simp [js1]
    rw [hv1, haddr0]
    simpa [dword] using hread
  have hld :
      (JoltISA.execInstr (.LD 1 1 0)).run js1 =
        .ok RETIRE_SUCCESS js_load := by
    simpa [js_load, dword] using
      (JoltISA.ld_run_vreg_vreg_from_memory_read (1 : JoltISA.VReg) (1 : JoltISA.VReg)
        (0 : BitVec 12) js1 dword hld_read)
  refine ⟨js_load, ?_, rfl, ?_, ?_⟩
  · rw [JoltISA.execProgram_instr_run_retire _ _ js js0 haddi]
    rw [JoltISA.execProgram_instr_run_retire _ _ js0 js1 handi]
    rw [JoltISA.execProgram_instr_run_retire _ _ js1 js_load hld]
  · simp [js_load, js1, js0, ea]
  · simp [js_load, dword, daddr]

/-- The setup block with a successful leading load-alignment assertion.

Halfword and word loads have an explicit virtual assertion before the common
dword setup block.  On the aligned path the assertion retires without changing
state, so the proof immediately reuses `setupBlock`.  The `mask` parameter is
`1` for halfword loads and `3` for word loads. -/
theorem assertSetupBlockAligned (rest : JoltISA.Program)
    (mask : BitVec 64) (imm : BitVec 12) (rs1 : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (halign : load_effective_address val imm &&& mask = 0)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail) :
    ∃ js_load : SailJoltState,
      (JoltISA.execProgram
        (.instr (.VirtualAssertLoadAlignment rs1 imm mask) <|
         .instr (.ADDI (.vreg 0) (.xreg rs1) imm) <|
         .instr (.ANDI (.vreg 1) (.vreg 0) (-8 : BitVec 12)) <|
         .instr (.LD 1 1 0) rest)).run js =
        (JoltISA.execProgram rest).run js_load ∧
      js_load.sail = js.sail ∧
      js_load.vregs 0 = load_effective_address val imm ∧
      js_load.vregs 1 =
        loaded_dword_at js.sail (compute_aligned_dword_base_address val imm) := by
  have hassert :
      (JoltISA.execInstr (.VirtualAssertLoadAlignment rs1 imm mask)).run js =
        .ok RETIRE_SUCCESS js := by
    exact JoltISA.execInstr_VirtualAssertLoadAlignment_run_aligned rs1 imm mask
      js val hrx (by simpa [load_effective_address] using halign)
  rcases setupBlock rest imm rs1 js hcfg val hrx h_dword_translate h_dword_phys with
    ⟨js_load, hrun, hsail, hv0, hv1⟩
  refine ⟨js_load, ?_, hsail, hv0, hv1⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js js hassert]
  exact hrun

/-- A failed leading load-alignment assertion stops the structured program.

This is the generic early-exit fact for halfword/word program theorems.  When
the masked low bits are nonzero, `VirtualAssertLoadAlignment` returns the Sail-compatible
load-address-alignment exception, and `execProgram` does not run the tail. -/
theorem assertBlockMisaligned (tail : JoltISA.Program)
    (mask : BitVec 64) (imm : BitVec 12) (rs1 : regidx)
    (js : SailJoltState)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (hmis : load_effective_address val imm &&& mask ≠ 0) :
    (JoltISA.execProgram (.instr (.VirtualAssertLoadAlignment rs1 imm mask) tail)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (load_effective_address val imm), ExceptionType.E_Load_Addr_Align ())) js := by
  let e :=
    (Virtaddr (load_effective_address val imm), ExceptionType.E_Load_Addr_Align ())
  have hassert :
      (JoltISA.execInstr (.VirtualAssertLoadAlignment rs1 imm mask)).run js =
        .ok (ExecutionResult.Memory_Exception e) js := by
    simpa [e, load_effective_address] using
      (JoltISA.execInstr_VirtualAssertLoadAlignment_run_misaligned rs1 imm mask
        js val hrx (by simpa [load_effective_address] using hmis))
  simpa [e] using
    (JoltISA.execProgram_instr_run_memory_exception
      (.VirtualAssertLoadAlignment rs1 imm mask) tail js js e hassert)

/-- Common virtual extraction block for `LB`, `LBU`, `LH`, `LHU`, and `LWU`.

Starting from the setup boundary (`v0 = ea`, `v1 = dword`), the prefix

`XORI v0, v0, xorImm; SLLI v0, v0, 3; SLL v1, v1, v0`

moves the requested byte/halfword/word lane to the top of the dword.  The
signedness is not handled here; the final `SRAI` or `SRLI` block decides
whether the top lane is sign-extended or zero-extended into the real
destination. -/
theorem xoriSlliSllBlock (rest : JoltISA.Program)
    (imm xorImm : BitVec 12)
    (js js_load : SailJoltState) (val : BitVec 64)
    (hload_sail : js_load.sail = js.sail)
    (hload_v0 : js_load.vregs 0 = load_effective_address val imm)
    (hload_v1 : js_load.vregs 1 =
      loaded_dword_at js.sail (compute_aligned_dword_base_address val imm)) :
    ∃ js_shift : SailJoltState,
      (JoltISA.execProgram
        (.instr (.XORI (.vreg 0) (.vreg 0) xorImm) <|
         .instr (.SLLI (.vreg 0) (.vreg 0) (3 : BitVec 6)) <|
         .instr (.SLL (.vreg 1) (.vreg 1) (.vreg 0)) rest)).run js_load =
        (JoltISA.execProgram rest).run js_shift ∧
      js_shift.sail = js.sail ∧
      js_shift.vregs 0 =
        shift_bits_left
          (load_effective_address val imm ^^^ sign_extend (m := 64) xorImm)
          (3 : BitVec 6) ∧
      js_shift.vregs 1 =
        shift_bits_left
          (loaded_dword_at js.sail (compute_aligned_dword_base_address val imm))
          (Sail.BitVec.extractLsb
            (shift_bits_left
              (load_effective_address val imm ^^^ sign_extend (m := 64) xorImm)
              (3 : BitVec 6)) 5 0) := by
  let xorValue := load_effective_address val imm ^^^ sign_extend (m := 64) xorImm
  let shiftValue := shift_bits_left xorValue (3 : BitVec 6)
  let shiftedDword :=
    shift_bits_left
      (loaded_dword_at js.sail (compute_aligned_dword_base_address val imm))
      (Sail.BitVec.extractLsb shiftValue 5 0)
  let js_xor : SailJoltState :=
    { sail := js_load.sail
      vregs := fun r => if r = (0 : JoltISA.VReg) then js_load.vregs 0 ^^^ sign_extend (m := 64) xorImm else js_load.vregs r }
  let js_slli : SailJoltState :=
    { sail := js_xor.sail
      vregs := fun r =>
        if r = (0 : JoltISA.VReg) then
          shift_bits_left (js_xor.vregs 0) (3 : BitVec 6)
        else js_xor.vregs r }
  let js_shift : SailJoltState :=
    { sail := js_slli.sail
      vregs := fun r =>
        if r = (1 : JoltISA.VReg) then
          shift_bits_left (js_slli.vregs 1) (Sail.BitVec.extractLsb (js_slli.vregs 0) 5 0)
        else js_slli.vregs r }
  have hxori :
      (JoltISA.execInstr (.XORI (.vreg 0) (.vreg 0) xorImm)).run js_load =
        .ok RETIRE_SUCCESS js_xor := by
    simpa [js_xor] using
      (JoltISA.execInstr_xori_vreg_vreg_run (0 : JoltISA.VReg) (0 : JoltISA.VReg)
        xorImm js_load)
  have hxv0 : js_xor.vregs 0 = xorValue := by
    change js_load.vregs (0 : JoltISA.VReg) ^^^ sign_extend (m := 64) xorImm =
      load_effective_address val imm ^^^ sign_extend (m := 64) xorImm
    rw [hload_v0]
  have hslli :
      (JoltISA.execInstr (.SLLI (.vreg 0) (.vreg 0) (3 : BitVec 6))).run js_xor =
        .ok RETIRE_SUCCESS js_slli := by
    simpa [js_slli] using
      (JoltISA.slli_run_vreg_vreg (0 : JoltISA.VReg) (0 : JoltISA.VReg)
        (3 : BitVec 6) js_xor)
  have hsv0 : js_slli.vregs 0 = shiftValue := by
    change shift_bits_left (js_xor.vregs (0 : JoltISA.VReg)) (3 : BitVec 6) =
      shift_bits_left xorValue (3 : BitVec 6)
    rw [hxv0]
  have hsv1 :
      js_slli.vregs 1 =
        loaded_dword_at js.sail (compute_aligned_dword_base_address val imm) := by
    change js_xor.vregs (1 : JoltISA.VReg) =
      loaded_dword_at js.sail (compute_aligned_dword_base_address val imm)
    change js_load.vregs (1 : JoltISA.VReg) =
      loaded_dword_at js.sail (compute_aligned_dword_base_address val imm)
    exact hload_v1
  have hsll :
      (JoltISA.execInstr (.SLL (.vreg 1) (.vreg 1) (.vreg 0))).run js_slli =
        .ok RETIRE_SUCCESS js_shift := by
    simpa [js_shift] using
      (JoltISA.execInstr_sll_vreg_vreg_vreg_run (1 : JoltISA.VReg) (1 : JoltISA.VReg)
        (0 : JoltISA.VReg) js_slli)
  refine ⟨js_shift, ?_, ?_, ?_, ?_⟩
  · rw [JoltISA.execProgram_instr_run_retire _ _ js_load js_xor hxori]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_xor js_slli hslli]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_slli js_shift hsll]
  · simp [js_shift, js_slli, js_xor, hload_sail]
  · change js_slli.vregs (0 : JoltISA.VReg) = shiftValue
    exact hsv0
  · change shift_bits_left (js_slli.vregs (1 : JoltISA.VReg))
      (Sail.BitVec.extractLsb (js_slli.vregs (0 : JoltISA.VReg)) 5 0) =
      shiftedDword
    rw [hsv1, hsv0]

/-- Final signed extraction block for byte and halfword loads.

Given a boundary state whose `v1` already contains the dword shifted left so
the requested lane sits at the top, `SRAI rd, v1, shamt` writes the
sign-extended lane to the real destination and continues with `rest`. -/
theorem sraiWriteBlock (rest : JoltISA.Program)
    (rd : regidx) (shamt : BitVec 6)
    (js js_shift : SailJoltState) (shiftedValue : BitVec 64)
    (hshift_sail : js_shift.sail = js.sail)
    (hshift_v1 : js_shift.vregs 1 = shiftedValue) :
    ∃ js_write : SailJoltState,
      (JoltISA.execProgram
        (.instr (.SRAI (.xreg rd) (.vreg 1) shamt) rest)).run js_shift =
        (JoltISA.execProgram rest).run js_write ∧
      js_write.sail =
        stateAfterWrite js.sail rd (shift_bits_right_arith shiftedValue shamt) := by
  let finalValue := shift_bits_right_arith shiftedValue shamt
  obtain ⟨s_write, hw_write⟩ := wX_shape rd finalValue js.sail
  let js_write : SailJoltState := { sail := s_write, vregs := js_shift.vregs }
  have hsrai :
      (JoltISA.execInstr (.SRAI (.xreg rd) (.vreg 1) shamt)).run js_shift =
        .ok RETIRE_SUCCESS js_write := by
    have hw_write' :
        wX_bits rd (shift_bits_right_arith (js_shift.vregs 1) shamt) js_shift.sail =
          .ok () s_write := by
      rw [hshift_sail, hshift_v1]
      exact hw_write
    simpa [js_write] using
      (JoltISA.execInstr_srai_vreg_xreg_run rd (1 : JoltISA.VReg) shamt
        js_shift s_write hw_write')
  refine ⟨js_write, ?_, ?_⟩
  · rw [JoltISA.execProgram_instr_run_retire _ _ js_shift js_write hsrai]
  · exact wX_bits_eq_stateAfterWrite rd finalValue js.sail s_write hw_write

/-- Final unsigned extraction block for byte, halfword, and unsigned-word
loads.

This is the logical-right-shift sibling of `sraiWriteBlock`.  The input
boundary is the same shifted `v1`; the final instruction uses `SRLI`, so the
written value is zero-extended rather than sign-extended. -/
theorem srliWriteBlock (rest : JoltISA.Program)
    (rd : regidx) (shamt : BitVec 6)
    (js js_shift : SailJoltState) (shiftedValue : BitVec 64)
    (hshift_sail : js_shift.sail = js.sail)
    (hshift_v1 : js_shift.vregs 1 = shiftedValue) :
    ∃ js_write : SailJoltState,
      (JoltISA.execProgram
        (.instr (.SRLI (.xreg rd) (.vreg 1) shamt) rest)).run js_shift =
        (JoltISA.execProgram rest).run js_write ∧
      js_write.sail =
        stateAfterWrite js.sail rd (shift_bits_right shiftedValue shamt) := by
  let finalValue := shift_bits_right shiftedValue shamt
  obtain ⟨s_write, hw_write⟩ := wX_shape rd finalValue js.sail
  let js_write : SailJoltState := { sail := s_write, vregs := js_shift.vregs }
  have hsrli :
      (JoltISA.execInstr (.SRLI (.xreg rd) (.vreg 1) shamt)).run js_shift =
        .ok RETIRE_SUCCESS js_write := by
    have hw_write' :
        wX_bits rd (shift_bits_right (js_shift.vregs 1) shamt) js_shift.sail =
          .ok () s_write := by
      rw [hshift_sail, hshift_v1]
      exact hw_write
    simpa [js_write] using
      (JoltISA.execInstr_srli_vreg_xreg_run rd (1 : JoltISA.VReg) shamt
        js_shift s_write hw_write')
  refine ⟨js_write, ?_, ?_⟩
  · rw [JoltISA.execProgram_instr_run_retire _ _ js_shift js_write hsrli]
  · exact wX_bits_eq_stateAfterWrite rd finalValue js.sail s_write hw_write

/-- The signed-word (`LW`) extraction block.

`LW` is the odd member of the load family: after the common dword setup it
does not use the `XORI; SLL; SRAI/SRLI` lane-to-top shape.  Instead it shifts
the loaded dword right by `(ea * 8) & 63`, writes that intermediate value to
real `rd`, and leaves the final 32-to-64 sign extension to `VirtualSignExtendWord`. -/
theorem lwSrlBlock (rest : JoltISA.Program)
    (imm : BitVec 12) (rd : regidx)
    (js js_load : SailJoltState) (val : BitVec 64)
    (hload_sail : js_load.sail = js.sail)
    (hload_v0 : js_load.vregs 0 = load_effective_address val imm)
    (hload_v1 : js_load.vregs 1 =
      loaded_dword_at js.sail (compute_aligned_dword_base_address val imm)) :
    ∃ (js_logic : SailJoltState) (logic_val : BitVec 64),
      (JoltISA.execProgram
        (.instr (.SLLI (.vreg 0) (.vreg 0) (3 : BitVec 6)) <|
         .instr (.SRL (.xreg rd) (.vreg 1) (.vreg 0)) rest)).run js_load =
        (JoltISA.execProgram rest).run js_logic ∧
      logic_val =
        shift_bits_right
          (loaded_dword_at js.sail (compute_aligned_dword_base_address val imm))
          (Sail.BitVec.extractLsb
            (shift_bits_left (load_effective_address val imm) (3 : BitVec 6)) 5 0) ∧
      js_logic.sail = stateAfterWrite js.sail rd logic_val := by
  let logic_val :=
    shift_bits_right
      (loaded_dword_at js.sail (compute_aligned_dword_base_address val imm))
      (Sail.BitVec.extractLsb
        (shift_bits_left (load_effective_address val imm) (3 : BitVec 6)) 5 0)
  let js_shift : SailJoltState :=
    { sail := js_load.sail
      vregs := fun r =>
        if r = (0 : JoltISA.VReg) then shift_bits_left (js_load.vregs 0) (3 : BitVec 6)
        else js_load.vregs r }
  have hslli :
      (JoltISA.execInstr (.SLLI (.vreg 0) (.vreg 0) (3 : BitVec 6))).run js_load =
        .ok RETIRE_SUCCESS js_shift := by
    simpa [js_shift] using
      (JoltISA.slli_run_vreg_vreg (0 : JoltISA.VReg) (0 : JoltISA.VReg)
        (3 : BitVec 6) js_load)
  obtain ⟨s_shift, hw_shift⟩ := wX_shape rd logic_val js.sail
  let js_logic : SailJoltState := { sail := s_shift, vregs := js_shift.vregs }
  have hshift_sail : js_shift.sail = js.sail := by
    simp [js_shift, hload_sail]
  have hshift_v0 :
      js_shift.vregs 0 =
        shift_bits_left (load_effective_address val imm) (3 : BitVec 6) := by
    change shift_bits_left (js_load.vregs (0 : JoltISA.VReg)) (3 : BitVec 6) =
      shift_bits_left (load_effective_address val imm) (3 : BitVec 6)
    rw [hload_v0]
  have hshift_v1 :
      js_shift.vregs 1 =
        loaded_dword_at js.sail (compute_aligned_dword_base_address val imm) := by
    change js_load.vregs (1 : JoltISA.VReg) =
      loaded_dword_at js.sail (compute_aligned_dword_base_address val imm)
    exact hload_v1
  have hsrl :
      (JoltISA.execInstr (.SRL (.xreg rd) (.vreg 1) (.vreg 0))).run js_shift =
        .ok RETIRE_SUCCESS js_logic := by
    have hw_shift' :
        wX_bits rd
          (shift_bits_right (js_shift.vregs 1)
            (Sail.BitVec.extractLsb (js_shift.vregs 0) 5 0))
          js_shift.sail = .ok () s_shift := by
      rw [hshift_sail, hshift_v1, hshift_v0]
      exact hw_shift
    simpa [js_logic] using
      (JoltISA.execInstr_srl_vreg_vreg_xreg_run rd (1 : JoltISA.VReg)
        (0 : JoltISA.VReg) js_shift s_shift hw_shift')
  have hs_logic : js_logic.sail = stateAfterWrite js.sail rd logic_val := by
    exact wX_bits_eq_stateAfterWrite rd logic_val js.sail s_shift hw_shift
  refine ⟨js_logic, logic_val, ?_, rfl, hs_logic⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js_load js_shift hslli]
  rw [JoltISA.execProgram_instr_run_retire _ _ js_shift js_logic hsrl]

/-- Final `LW` sign-extension block.

At this boundary, the preceding `SRL` has already written the shifted word to
real `rd`.  `VirtualSignExtendWord rd, rd` reads it back, sign-extends the low 32 bits, and
writes the final architectural value. -/
theorem sextwWriteBlock
    (rd : regidx) (js js_logic : SailJoltState) (logic_val : BitVec 64)
    (hlogic_sail : js_logic.sail = stateAfterWrite js.sail rd logic_val) :
    ∃ js' : SailJoltState,
      (JoltISA.execProgram
        (.instr (.VirtualSignExtendWord (.xreg rd) (.xreg rd)) (.done RETIRE_SUCCESS))).run js_logic =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail =
        stateAfterWrite js.sail rd
          (sign_extend (m := 64) ((Sail.BitVec.extractLsb logic_val 31 0) : BitVec 32)) := by
  obtain ⟨js', hwrite_sail, hsextw⟩ :=
    JoltISA.exists_state_after_virtual_sign_extend_word_run_xreg_xreg_of_same_register_write
      rd js_logic js.sail logic_val hlogic_sail
  refine ⟨js', ?_, ?_⟩
  · rw [JoltISA.execProgram_instr_run_retire _ _ js_logic js' hsextw]
    rfl
  · exact hwrite_sail

end LoadProgramBlocks

end
