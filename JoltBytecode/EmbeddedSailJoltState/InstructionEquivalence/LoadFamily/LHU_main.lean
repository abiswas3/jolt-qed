import JoltBytecode.EmbeddedSailJoltState.Defs
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Expansions.Load
import JoltBytecode.EmbeddedSailJoltState.MemoryUtils
import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadDefUtils
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadFamily.PhaseHelpers
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadFamily.DwordArithmetic
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadFamily.ProgramBlocks
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadFamily.LB_decomposed
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadFamily.LH_decomposed
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadFamily.LHU_decomposed
import JoltBytecode.EmbeddedSailJoltState.RtypeW
import Mathlib.Tactic.IntervalCases

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace LHU_main

/-!
# LHU: Jolt load-halfword (unsigned) top-level equivalence

From `tracer/src/instruction/lhu.rs::inline_sequence_64`:

    VirtualAssertHalfwordAlignment rs1, imm
    ADDI  v0, rs1, imm
    ANDI  v1, v0, -8
    LD    v1, v1, 0
    XORI  v0, v0, 6
    SLLI  v0, v0, 3
    SLL   v1, v1, v0
    SRLI  rd, v1, 48

Identical to `LH_main` except the final `SRLI` (logical right shift —
zero-fill) replaces `SRAI` (arithmetic right shift — sign-fill), and
`execute_LOAD`'s signed/unsigned flag is `true` instead of `false`.
-/

/-- The original Jolt LHU program. Same fused `VirtualAssertHalfwordAlignment
    + ADDI v0, rs1, imm` trick as `jolt_lh`. Only the final line uses
    logical shift (SRLI) in place of arithmetic shift (SRAI). -/
def jolt_lhu (imm : BitVec 12) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  -- VirtualAssertHalfwordAlignment rs1, imm + ADDI v0, rs1, imm (fused)
  let base ← liftSail (rX_bits rs1)
  let ea := base + sign_extend (m := 64) imm
  if ea &&& 1 ≠ 0 then
    pure (ExecutionResult.Memory_Exception
      (Virtaddr ea, ExceptionType.E_Load_Addr_Align ()))
  else do
    writeVReg 0 ea                                        -- (ADDI v0, rs1, imm writes ea)
    let _ ← vreg_ANDI 1 0 (-8 : BitVec 12)                -- ANDI v1, v0, -8
    match ← vreg_LD 1 1 0 with                             -- LD   v1, v1, 0
    | .Retire_Success () =>
        let _ ← vreg_XORI 0 0 6                            -- XORI v0, v0, 6
        let _ ← vreg_SLLI 0 0 3                            -- SLLI v0, v0, 3
        let _ ← vreg_SLL 1 1 0                             -- SLL  v1, v1, v0
        vreg_SRLI_to_real rd 1 (48 : BitVec 6)             -- SRLI rd, v1, 48
    | other => pure other

/-- **Bridge lemma for LHU.** Logical sibling of `jolt_lh_bridge`: the
    Jolt logic-phase computation (XOR 6, SLL 3, SLL the dword, SRLI 48)
    equals the Sail-side direct halfword load zero-extended to 64 bits.
    Requires halfword alignment. -/
theorem jolt_lhu_bridge (s : SailState) (addr : BitVec 64)
    (halign : addr &&& 1 = 0) :
    (let dword     := loaded_dword_at s (addr &&& (-8 : BitVec 64))
     let xor_addr  := addr ^^^ (6 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6   := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted   := shift_bits_left dword shift_6
     shift_bits_right shifted (48 : BitVec 6))
    = zero_extend (m := 64) (loaded_halfword_at s addr) := by
  simp only [sll_srli_extracts_halfword _ _ halign, ← loaded_halfword_in_dword _ _ halign]

/-- `jolt_lhu` and `jolt_lhu_decomposed` produce the same final state on
    a halfword-aligned input. -/
theorem jolt_lhu_run_eq_decomposed (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState) (val : BitVec 64)
    (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (halign : (val + sign_extend (m := 64) imm) &&& 1 = 0)
    :
    (jolt_lhu imm rs1 rd).run js = (jolt_lhu_decomposed imm rs1 rd).run js := by
  have h8 : sign_extend (m := 64) (-8 : BitVec 12) = (-8 : BitVec 64) := by decide
  unfold jolt_lhu jolt_lhu_decomposed vreg_SRLI_to_real
    LB_main.jolt_lb_load_phase LH_main.jolt_lh_logic_phase jolt_lhu_write_phase vreg_ANDI
  simp only [liftSail, bind, EStateM.bind, pure, EStateM.pure, EStateM.run, h8]
  rw [hrx]
  simp only []
  rw [if_neg (by simpa using halign)]
  rfl

/-- Aligned case: `jolt_lhu` succeeds and leaves `rd` holding
    `zero_extend (loaded_halfword_at js.sail ea)`. Composes
    `jolt_lhu_decomposed_writes_logic_value` with `jolt_lhu_bridge`. -/
theorem jolt_lhu_concrete (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (halign : load_effective_address val imm &&& 1 = 0)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail) :
    ∃ js' : SailJoltState,
      (jolt_lhu imm rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (zero_extend (m := 64)
          (loaded_halfword_at js.sail (load_effective_address val imm))) := by
  have hrun_eq :
      (jolt_lhu imm rs1 rd).run js = (jolt_lhu_decomposed imm rs1 rd).run js := by
    simpa using jolt_lhu_run_eq_decomposed imm rs1 rd js val hrx
      (by simpa [load_effective_address] using halign)
  rcases jolt_lhu_decomposed_writes_logic_value imm rs1 rd js val
      hrd hcfg hrx h_dword_translate h_dword_phys with
    ⟨js', logic_val, hdecomp_run, hlogic_val, hwrite_sail⟩
  refine ⟨js', ?_, ?_⟩
  · rw [hrun_eq]
    exact hdecomp_run
  · rw [hwrite_sail, hlogic_val]
    exact congrArg (stateAfterWrite js.sail rd)
      (jolt_lhu_bridge js.sail (load_effective_address val imm) halign)

/-- Misaligned case. -/
theorem jolt_lhu_concrete_misaligned (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_align : load_effective_address val imm &&& 1 ≠ 0)
    :
    (jolt_lhu imm rs1 rd).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (load_effective_address val imm), ExceptionType.E_Load_Addr_Align ())) js := by
  unfold jolt_lhu
  simp only [liftSail, bind, EStateM.bind, pure, EStateM.run]
  rw [hrx]
  simp only []
  rw [if_pos h_align]
  rfl

/-- Sail-side `execute_LOAD … true 2` reduces to `stateAfterWrite rd
    (zero_extend (loaded_halfword_at ea))`. -/
theorem execute_LHU_reduces (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (hload : LoadReadAssumptions (load_effective_address val imm) 2 js.sail)
    (h_no_ovf : (load_effective_address val imm).toNat + 1 < 2 ^ 64) :
    (execute_LOAD imm rs1 rd true 2).run js.sail =
    .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd
        (zero_extend (m := 64)
          (loaded_halfword_at js.sail (load_effective_address val imm)))) := by
  unfold execute_LOAD
  simp only [bind, pure]
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  simp (config := { decide := true }) only []
  simp (config := { decide := true }) only [PreSail.assert, EStateM.bind, pure, EStateM.pure,
       EStateM.run, if_true]
  rw [vmem_read_halfword_reduces imm rs1 js.sail val hrx hload.aligned hload.translate
      (mem_read_2_eq_loaded_halfword _ js.sail hcfg h_no_ovf hload.phys)]
  simp only [extend_value, if_true, EStateM.bind, EStateM.pure]
  obtain ⟨s', hw⟩ := wX_shape rd
    (zero_extend (m := 64) (loaded_halfword_at js.sail (load_effective_address val imm)))
    js.sail
  rw [hw]
  simp only [RETIRE_SUCCESS]
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

/-- Aligned equivalence. -/
theorem jolt_lhu_eq_sail_aligned (imm : BitVec 12)
    (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail)
    (htranslate : BareTranslation (load_effective_address val imm) js.sail)
    (hphys : FlatPhysMem (load_effective_address val imm) 2 js.sail)
    (h_half_no_ovf : (load_effective_address val imm).toNat + 1 < 2 ^ 64)
    (h_align : load_effective_address val imm &&& 1 = 0)
    :
    projectResult ((jolt_lhu imm rs1 rd).run js) =
    (execute_LOAD imm rs1 rd true 2).run js.sail := by
  let ea := load_effective_address val imm
  have hload : LoadReadAssumptions (load_effective_address val imm) 2 js.sail := by
    refine
      { aligned := ?_
        translate := htranslate
        phys := hphys }
    refine
      { misalign := ?_
        split := ?_ }
    · simpa [ea] using access_misaligned_2_aligned_false ea h_align
    · simpa [ea] using split_misaligned_aligned_2 ea h_align
  have hjolt_aligned := jolt_lhu_concrete imm rs1 rd hrd js hcfg val hrx h_align h_dword_translate h_dword_phys
  have hsail_aligned := execute_LHU_reduces imm rs1 rd js hcfg val hrx hload h_half_no_ovf
  rcases hjolt_aligned with ⟨js', hjolt, hjolt_sail⟩
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail, hsail_aligned]

/-- Sail-side misaligned. -/
theorem execute_LHU_misaligned (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (htranslate : BareTranslation (load_effective_address val imm) js.sail)
    (hphys : FlatPhysMem (load_effective_address val imm) 2 js.sail)
    (h_no_ovf : (load_effective_address val imm).toNat + 1 < 2 ^ 64)
    (h_align : load_effective_address val imm &&& 1 ≠ 0)
    :
    (execute_LOAD imm rs1 rd true 2).run js.sail =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (load_effective_address val imm), ExceptionType.E_Load_Addr_Align ())) js.sail := by
  let ea := load_effective_address val imm
  unfold execute_LOAD
  simp only [bind, pure]
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  simp (config := { decide := true }) only []
  simp (config := { decide := true }) only [PreSail.assert, EStateM.bind, pure, EStateM.pure,
       EStateM.run, if_true]
  unfold vmem_read
  unfold SailME.run PreSail.PreSailME.run
  have hmis :
      access_causes_misaligned_exception (Virtaddr ea) 2 false = true := by
    simpa [ea] using access_misaligned_2_unaligned_true ea h_align
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
        ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
        ExceptT.pure, ExceptT.lift,
        MonadLift.monadLift, liftM, monadLift, Functor.map,
        ext_data_get_addr, hrx,
        vmem_read_addr, hmis, ea]
  rfl

/-- Misaligned equivalence. -/
theorem jolt_lhu_eq_sail_misaligned (imm : BitVec 12)
    (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail)
    (htranslate : BareTranslation (load_effective_address val imm) js.sail)
    (hphys : FlatPhysMem (load_effective_address val imm) 2 js.sail)
    (h_half_no_ovf : (load_effective_address val imm).toNat + 1 < 2 ^ 64)
    (h_align : load_effective_address val imm &&& 1 ≠ 0)
    :
    projectResult ((jolt_lhu imm rs1 rd).run js) =
    (execute_LOAD imm rs1 rd true 2).run js.sail := by
  let ea := load_effective_address val imm
  have hjolt_misaligned :
      (jolt_lhu imm rs1 rd).run js =
        .ok (ExecutionResult.Memory_Exception (Virtaddr ea, ExceptionType.E_Load_Addr_Align ())) js := by
    simpa [ea] using
      (jolt_lhu_concrete_misaligned imm rs1 rd hrd js hcfg val hrx h_align)
  have hsail_misaligned :
      (execute_LOAD imm rs1 rd true 2).run js.sail =
        .ok (ExecutionResult.Memory_Exception (Virtaddr ea, ExceptionType.E_Load_Addr_Align ())) js.sail := by
    simpa [ea] using
      (execute_LHU_misaligned imm rs1 rd js hcfg val hrx htranslate hphys h_half_no_ovf h_align)
  rw [hjolt_misaligned]
  simp only [projectResult, project]
  symm
  exact hsail_misaligned

/-- **Main theorem.** `jolt_lhu = execute_LOAD … true 2` on every input. -/
theorem jolt_lhu_eq_sail (imm : BitVec 12)
    (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail)
    (htranslate : BareTranslation (load_effective_address val imm) js.sail)
    (hphys : FlatPhysMem (load_effective_address val imm) 2 js.sail)
    (h_half_no_ovf : (load_effective_address val imm).toNat + 1 < 2 ^ 64)
    :
    projectResult ((jolt_lhu imm rs1 rd).run js) =
    (execute_LOAD imm rs1 rd true 2).run js.sail := by
  let ea := load_effective_address val imm
  by_cases h_align : ea &&& 1 = 0
  · exact jolt_lhu_eq_sail_aligned imm rs1 rd hrd js hcfg val hrx h_dword_translate h_dword_phys htranslate hphys h_half_no_ovf h_align
  · exact jolt_lhu_eq_sail_misaligned imm rs1 rd hrd js hcfg val hrx h_dword_translate h_dword_phys htranslate hphys h_half_no_ovf h_align

/-!
## Program-level LHU theorem

This is the unsigned halfword sibling of the program-level `LH` theorem.  The
front of the proof is identical; only the final write block and pure bridge
use logical right shift / zero extension.
-/

/-- Program-level aligned execution for LHU.

The theorem is intentionally phrased in the same boundary language as `LH`:
alignment plus setup, lane positioning, unsigned writeback, then the pure
bridge to Sail's direct halfword load. -/
theorem lhuProgram_concrete_aligned (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (halign : load_effective_address val imm &&& 1 = 0)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail) :
    ∃ js' : SailJoltState,
      (JoltISA.execProgram (JoltISA.lhuProgram imm rs1 rd)).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (zero_extend (m := 64)
          (loaded_halfword_at js.sail (load_effective_address val imm))) := by
  let writeTail : JoltISA.Program :=
    .instr (.SRLI (.xreg rd) (.vreg 1) (48 : BitVec 6)) (.done RETIRE_SUCCESS)
  let logicTail : JoltISA.Program :=
    .instr (.XORI (.vreg 0) (.vreg 0) (6 : BitVec 12)) <|
    .instr (.SLLI (.vreg 0) (.vreg 0) (3 : BitVec 6)) <|
    .instr (.SLL (.vreg 1) (.vreg 1) (.vreg 0)) writeTail
  rcases LoadProgramBlocks.assertSetupBlockAligned logicTail (1 : BitVec 64)
      imm rs1 js hcfg val hrx halign h_dword_translate h_dword_phys with
    ⟨js_load, hload_run, hload_sail, hload_v0, hload_v1⟩
  rcases LoadProgramBlocks.xoriSlliSllBlock writeTail imm (6 : BitVec 12)
      js js_load val hload_sail hload_v0 hload_v1 with
    ⟨js_shift, hlogic_run, hshift_sail, _hshift_v0, hshift_v1⟩
  let shiftedValue :=
    shift_bits_left
      (loaded_dword_at js.sail (compute_aligned_dword_base_address val imm))
      (Sail.BitVec.extractLsb
        (shift_bits_left
          (load_effective_address val imm ^^^ sign_extend (m := 64) (6 : BitVec 12))
          (3 : BitVec 6)) 5 0)
  have hshifted : js_shift.vregs 1 = shiftedValue := by
    simpa [shiftedValue] using hshift_v1
  rcases LoadProgramBlocks.srliWriteBlock (.done RETIRE_SUCCESS)
      rd (48 : BitVec 6) js js_shift shiftedValue hshift_sail hshifted with
    ⟨js', hwrite_run, hwrite_sail⟩
  refine ⟨js', ?_, ?_⟩
  · unfold JoltISA.lhuProgram
    change (JoltISA.execProgram
      (.instr (.VirtualAssertLoadAlignment rs1 imm (1 : BitVec 64)) <|
       .instr (.ADDI (.vreg 0) (.xreg rs1) imm) <|
       .instr (.ANDI (.vreg 1) (.vreg 0) (-8 : BitVec 12)) <|
       .instr (.LD 1 1 0) logicTail)).run js = .ok RETIRE_SUCCESS js'
    rw [hload_run, hlogic_run, hwrite_run]
    rfl
  · rw [hwrite_sail]
    exact congrArg (stateAfterWrite js.sail rd) (by
      have h6 : sign_extend (m := 64) (6 : BitVec 12) = (6 : BitVec 64) := by decide
      simpa [shiftedValue, compute_aligned_dword_base_address, h6] using
        (jolt_lhu_bridge js.sail (load_effective_address val imm) halign))

/-- Program-level misaligned execution for LHU. -/
theorem lhuProgram_concrete_misaligned (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_align : load_effective_address val imm &&& 1 ≠ 0) :
    (JoltISA.execProgram (JoltISA.lhuProgram imm rs1 rd)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (load_effective_address val imm), ExceptionType.E_Load_Addr_Align ())) js := by
  let e :=
    (Virtaddr (load_effective_address val imm), ExceptionType.E_Load_Addr_Align ())
  unfold JoltISA.lhuProgram
  simpa [e] using
    (LoadProgramBlocks.assertBlockMisaligned
      (.instr (.ADDI (.vreg 0) (.xreg rs1) imm) <|
       .instr (.ANDI (.vreg 1) (.vreg 0) (-8 : BitVec 12)) <|
       .instr (.LD 1 1 0) <|
       .instr (.XORI (.vreg 0) (.vreg 0) (6 : BitVec 12)) <|
       .instr (.SLLI (.vreg 0) (.vreg 0) (3 : BitVec 6)) <|
       .instr (.SLL (.vreg 1) (.vreg 1) (.vreg 0)) <|
       .instr (.SRLI (.xreg rd) (.vreg 1) (48 : BitVec 6)) <|
       .done RETIRE_SUCCESS)
      (1 : BitVec 64) imm rs1 js val hrx h_align)

/-- Aligned public program theorem for LHU. -/
theorem lhuProgram_eq_sail_aligned (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail)
    (htranslate : BareTranslation (load_effective_address val imm) js.sail)
    (hphys : FlatPhysMem (load_effective_address val imm) 2 js.sail)
    (h_half_no_ovf : (load_effective_address val imm).toNat + 1 < 2 ^ 64)
    (h_align : load_effective_address val imm &&& 1 = 0) :
    projectResult ((JoltISA.execProgram (JoltISA.lhuProgram imm rs1 rd)).run js) =
    (execute_LOAD imm rs1 rd true 2).run js.sail := by
  let ea := load_effective_address val imm
  have hload : LoadReadAssumptions (load_effective_address val imm) 2 js.sail := by
    refine
      { aligned := ?_
        translate := htranslate
        phys := hphys }
    refine
      { misalign := ?_
        split := ?_ }
    · simpa [ea] using access_misaligned_2_aligned_false ea h_align
    · simpa [ea] using split_misaligned_aligned_2 ea h_align
  rcases lhuProgram_concrete_aligned imm rs1 rd js hcfg val hrx h_align
      h_dword_translate h_dword_phys with
    ⟨js', hjolt, hjolt_sail⟩
  have hsail := execute_LHU_reduces imm rs1 rd js hcfg val hrx hload h_half_no_ovf
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail, hsail]

/-- Misaligned public program theorem for LHU. -/
theorem lhuProgram_eq_sail_misaligned (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (htranslate : BareTranslation (load_effective_address val imm) js.sail)
    (hphys : FlatPhysMem (load_effective_address val imm) 2 js.sail)
    (h_half_no_ovf : (load_effective_address val imm).toNat + 1 < 2 ^ 64)
    (h_align : load_effective_address val imm &&& 1 ≠ 0) :
    projectResult ((JoltISA.execProgram (JoltISA.lhuProgram imm rs1 rd)).run js) =
    (execute_LOAD imm rs1 rd true 2).run js.sail := by
  let ea := load_effective_address val imm
  have hjolt :
      (JoltISA.execProgram (JoltISA.lhuProgram imm rs1 rd)).run js =
        .ok (ExecutionResult.Memory_Exception
          (Virtaddr ea, ExceptionType.E_Load_Addr_Align ())) js := by
    simpa [ea] using lhuProgram_concrete_misaligned imm rs1 rd js val hrx h_align
  have hsail :
      (execute_LOAD imm rs1 rd true 2).run js.sail =
        .ok (ExecutionResult.Memory_Exception
          (Virtaddr ea, ExceptionType.E_Load_Addr_Align ())) js.sail := by
    simpa [ea] using
      (execute_LHU_misaligned imm rs1 rd js hcfg val hrx htranslate hphys
        h_half_no_ovf h_align)
  rw [hjolt]
  simp only [projectResult, project]
  symm
  exact hsail

/-- **Main program theorem for LHU.**  The structured Jolt-ISA expansion
`lhuProgram`, interpreted by `execProgram`, agrees with Sail's unsigned
halfword-load execution. -/
theorem lhuProgram_eq_sail (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail)
    (htranslate : BareTranslation (load_effective_address val imm) js.sail)
    (hphys : FlatPhysMem (load_effective_address val imm) 2 js.sail)
    (h_half_no_ovf : (load_effective_address val imm).toNat + 1 < 2 ^ 64) :
    projectResult ((JoltISA.execProgram (JoltISA.lhuProgram imm rs1 rd)).run js) =
    (execute_LOAD imm rs1 rd true 2).run js.sail := by
  let ea := load_effective_address val imm
  by_cases h_align : ea &&& 1 = 0
  · exact lhuProgram_eq_sail_aligned imm rs1 rd js hcfg val hrx
      h_dword_translate h_dword_phys htranslate hphys h_half_no_ovf h_align
  · exact lhuProgram_eq_sail_misaligned imm rs1 rd js hcfg val hrx
      htranslate hphys h_half_no_ovf h_align

end LHU_main
