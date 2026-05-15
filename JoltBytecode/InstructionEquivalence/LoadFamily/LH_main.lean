import JoltBytecode.JoltISA.Environment
import JoltBytecode.JoltISA.Expansions.Load
import JoltBytecode.InstructionEquivalence.Memory.Utils
import JoltBytecode.InstructionEquivalence.LoadDefUtils
import JoltBytecode.InstructionEquivalence.LoadFamily.PhaseHelpers
import JoltBytecode.InstructionEquivalence.LoadFamily.DwordArithmetic
import JoltBytecode.InstructionEquivalence.LoadFamily.ProgramBlocks
import JoltBytecode.InstructionEquivalence.ProofSupport
import Mathlib.Tactic.IntervalCases

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace LH_main

/-!
# LH: Jolt load-halfword (signed) top-level equivalence

From `tracer/src/instruction/lh.rs::inline_sequence_64`:

    VirtualAssertHalfwordAlignment rs1, imm
    ADDI  v0, rs1, imm
    ANDI  v1, v0, -8
    LD    v1, v1, 0
    XORI  v0, v0, 6
    SLLI  v0, v0, 3
    SLL   v1, v1, v0
    SRAI  rd, v1, 48

LH is a hybrid of LW and LB:
* **Has an alignment check** (`addr & 1 = 0`) like LW — so the program
  uses the same "fuse `VirtualAssert…Alignment` with the initial ADDI"
  trick as `jolt_lw`, opening with an explicit
  `let base ← liftSail (rX_bits rs1); if ea & 1 ≠ 0 then … else …`.
* **Writes via SLL+SRAI** like LB — so after the alignment passes, the
  remaining lines use `vreg_ANDI / vreg_LD / vreg_XORI / vreg_SLLI /
  vreg_SLL / vreg_SRAI_to_real`, one Lean line per bytecode line, with
  `XORI v0, v0, 6` and `SRAI rd, v1, 48` in place of LB's `7` / `56`.

## Proof architecture

The Jolt side is the structured `JoltISA.lhProgram`.  The proof composes
program-level helper blocks and uses the pure bridge lemma below to identify
the extracted Jolt value with Sail's direct halfword load.
-/

/-- **Bridge lemma for LH.** The Jolt logic-phase computation (XOR with 6,
    SLL by 3, SLL the dword, arith-shift-right by 48) equals the Sail-
    side direct halfword load sign-extended to 64 bits. Requires halfword
    alignment `halign : addr & 1 = 0`. Pure bit-vector algebra — combines
    `sll_srai_extracts_halfword` with `loaded_halfword_in_dword`,
    mirroring `jolt_lw_bridge`'s shape. -/
theorem jolt_lh_bridge (s : SailState) (addr : BitVec 64)
    (halign : addr &&& 1 = 0) :
    (let dword     := loaded_dword_at s (addr &&& (-8 : BitVec 64))
     let xor_addr  := addr ^^^ (6 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6   := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted   := shift_bits_left dword shift_6
     shift_bits_right_arith shifted (48 : BitVec 6))
    = sign_extend (m := 64) (loaded_halfword_at s addr) := by
  simp only [sll_srai_extracts_halfword _ _ halign, ← loaded_halfword_in_dword _ _ halign]

/-- Sail-side `execute_LOAD imm rs1 rd false 2` reduces to
    `stateAfterWrite rd (sign_extend (loaded_halfword_at ea))` under the
    aligned + translate + phys + no-overflow assumptions. Width-2
    analogue of `execute_LW_reduces`. -/
theorem execute_LH_reduces (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (hload : LoadReadAssumptions (load_effective_address val imm) 2 js.sail)
    (h_no_ovf : (load_effective_address val imm).toNat + 1 < 2 ^ 64) :
    (execute_LOAD imm rs1 rd false 2).run js.sail =
    .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (loaded_halfword_at js.sail (load_effective_address val imm)))) := by
  unfold execute_LOAD
  simp only [bind, pure]
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  simp (config := { decide := true }) only []
  simp (config := { decide := true }) only [PreSail.assert, EStateM.bind, pure, EStateM.pure,
       EStateM.run, if_true]
  rw [vmem_read_halfword_reduces imm rs1 js.sail val hrx hload.aligned hload.translate
      (mem_read_2_eq_loaded_halfword _ js.sail hcfg h_no_ovf hload.phys)]
  simp only [extend_value, Bool.false_eq_true, if_false, EStateM.bind, EStateM.pure]
  obtain ⟨s', hw⟩ := wX_shape rd
    (sign_extend (m := 64) (loaded_halfword_at js.sail (load_effective_address val imm)))
    js.sail
  rw [hw]
  simp only [RETIRE_SUCCESS]
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

/-- Sail-side `execute_LOAD` on a misaligned input returns the same
    memory-alignment exception as Jolt. Width-2 variant of
    `execute_LW_misaligned`, using `access_misaligned_2_unaligned_true`. -/
theorem execute_LH_misaligned (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (htranslate : BareTranslation (load_effective_address val imm) js.sail)
    (hphys : FlatPhysMem (load_effective_address val imm) 2 js.sail)
    (h_no_ovf : (load_effective_address val imm).toNat + 1 < 2 ^ 64)
    (h_align : load_effective_address val imm &&& 1 ≠ 0)
    :
    (execute_LOAD imm rs1 rd false 2).run js.sail =
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

/-!
## Program-level LH theorem

The structured program theorem follows the same architecture as `LB`, with one
additional reusable block at the front: the halfword alignment assertion.
-/

/-- Program-level aligned execution for LH.

The proof is a direct composition of four named facts: successful
`VirtualAssertLoadAlignment` plus dword setup, common lane positioning, signed writeback,
and the pure halfword bridge. -/
theorem lhProgram_concrete_aligned (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (halign : load_effective_address val imm &&& 1 = 0)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail) :
    ∃ js' : SailJoltState,
      (JoltISA.execProgram (JoltISA.lhProgram imm rs1 rd)).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (loaded_halfword_at js.sail (load_effective_address val imm))) := by
  let writeTail : JoltISA.Program :=
    .instr (.SRAI (.xreg rd) (.vreg 1) (48 : BitVec 6)) (.done RETIRE_SUCCESS)
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
  rcases LoadProgramBlocks.sraiWriteBlock (.done RETIRE_SUCCESS)
      rd (48 : BitVec 6) js js_shift shiftedValue hshift_sail hshifted with
    ⟨js', hwrite_run, hwrite_sail⟩
  refine ⟨js', ?_, ?_⟩
  · unfold JoltISA.lhProgram
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
        (jolt_lh_bridge js.sail (load_effective_address val imm) halign))

/-- Program-level misaligned execution for LH.

The first instruction is the alignment assertion, so the Jolt program returns
the load-address-alignment exception before the dword setup or writeback code
can run. -/
theorem lhProgram_concrete_misaligned (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_align : load_effective_address val imm &&& 1 ≠ 0) :
    (JoltISA.execProgram (JoltISA.lhProgram imm rs1 rd)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (load_effective_address val imm), ExceptionType.E_Load_Addr_Align ())) js := by
  let e :=
    (Virtaddr (load_effective_address val imm), ExceptionType.E_Load_Addr_Align ())
  unfold JoltISA.lhProgram
  simpa [e] using
    (LoadProgramBlocks.assertBlockMisaligned
      (.instr (.ADDI (.vreg 0) (.xreg rs1) imm) <|
       .instr (.ANDI (.vreg 1) (.vreg 0) (-8 : BitVec 12)) <|
       .instr (.LD 1 1 0) <|
       .instr (.XORI (.vreg 0) (.vreg 0) (6 : BitVec 12)) <|
       .instr (.SLLI (.vreg 0) (.vreg 0) (3 : BitVec 6)) <|
       .instr (.SLL (.vreg 1) (.vreg 1) (.vreg 0)) <|
       .instr (.SRAI (.xreg rd) (.vreg 1) (48 : BitVec 6)) <|
       .done RETIRE_SUCCESS)
      (1 : BitVec 64) imm rs1 js val hrx h_align)

/-- Aligned public program theorem for LH. -/
theorem lhProgram_eq_sail_aligned (imm : BitVec 12)
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
    projectResult ((JoltISA.execProgram (JoltISA.lhProgram imm rs1 rd)).run js) =
    (execute_LOAD imm rs1 rd false 2).run js.sail := by
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
  rcases lhProgram_concrete_aligned imm rs1 rd js hcfg val hrx h_align
      h_dword_translate h_dword_phys with
    ⟨js', hjolt, hjolt_sail⟩
  have hsail := execute_LH_reduces imm rs1 rd js hcfg val hrx hload h_half_no_ovf
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail, hsail]

/-- Misaligned public program theorem for LH. -/
theorem lhProgram_eq_sail_misaligned (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (htranslate : BareTranslation (load_effective_address val imm) js.sail)
    (hphys : FlatPhysMem (load_effective_address val imm) 2 js.sail)
    (h_half_no_ovf : (load_effective_address val imm).toNat + 1 < 2 ^ 64)
    (h_align : load_effective_address val imm &&& 1 ≠ 0) :
    projectResult ((JoltISA.execProgram (JoltISA.lhProgram imm rs1 rd)).run js) =
    (execute_LOAD imm rs1 rd false 2).run js.sail := by
  let ea := load_effective_address val imm
  have hjolt :
      (JoltISA.execProgram (JoltISA.lhProgram imm rs1 rd)).run js =
        .ok (ExecutionResult.Memory_Exception
          (Virtaddr ea, ExceptionType.E_Load_Addr_Align ())) js := by
    simpa [ea] using lhProgram_concrete_misaligned imm rs1 rd js val hrx h_align
  have hsail :
      (execute_LOAD imm rs1 rd false 2).run js.sail =
        .ok (ExecutionResult.Memory_Exception
          (Virtaddr ea, ExceptionType.E_Load_Addr_Align ())) js.sail := by
    simpa [ea] using
      (execute_LH_misaligned imm rs1 rd js hcfg val hrx htranslate hphys
        h_half_no_ovf h_align)
  rw [hjolt]
  simp only [projectResult, project]
  symm
  exact hsail

/-- **Main program theorem for LH.**  The structured Jolt-ISA expansion
`lhProgram`, interpreted by `execProgram`, agrees with Sail's signed halfword
load execution. -/
theorem lhProgram_eq_sail (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail)
    (htranslate : BareTranslation (load_effective_address val imm) js.sail)
    (hphys : FlatPhysMem (load_effective_address val imm) 2 js.sail)
    (h_half_no_ovf : (load_effective_address val imm).toNat + 1 < 2 ^ 64) :
    projectResult ((JoltISA.execProgram (JoltISA.lhProgram imm rs1 rd)).run js) =
    (execute_LOAD imm rs1 rd false 2).run js.sail := by
  let ea := load_effective_address val imm
  by_cases h_align : ea &&& 1 = 0
  · exact lhProgram_eq_sail_aligned imm rs1 rd js hcfg val hrx
      h_dword_translate h_dword_phys htranslate hphys h_half_no_ovf h_align
  · exact lhProgram_eq_sail_misaligned imm rs1 rd js hcfg val hrx
      htranslate hphys h_half_no_ovf h_align

end LH_main
