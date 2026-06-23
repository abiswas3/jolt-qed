import JoltBytecode.InstructionEquivalence.ProofSupport.BundleLemmas
import JoltBytecode.JoltISA.Expansions.Load
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Read
import JoltBytecode.InstructionEquivalence.Instructions.LoadFamily.DwordArithmetic
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Windows
import JoltBytecode.InstructionEquivalence.Instructions.LoadFamily.ProgramBlocks
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import Mathlib.Tactic.IntervalCases

set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace LBU_main

/-!
# LBU: Jolt load-byte (unsigned) top-level equivalence

From `tracer/src/instruction/lbu.rs::inline_sequence_64`:

    ADDI  v0, rs1, imm
    ANDI  v1, v0, -8
    LD    v1, v1, 0
    XORI  v0, v0, 7
    SLLI  v0, v0, 3
    SLL   v1, v1, v0
    SRLI  rd, v1, 56

This is identical to `LB` (see `LB_main.lean`) except the final step is
`SRLI` (logical right shift) instead of `SRAI` (arithmetic right shift).
Logical shift zero-fills the upper 56 bits; arithmetic shift replicates the
sign bit. Accordingly:

* The write phase uses `shift_bits_right` in place of
  `shift_bits_right_arith`.
* The bridge's RHS and the final `rd` value use `zero_extend` in place of
  `sign_extend`.
* `execute_LOAD`'s signed/unsigned flag is `true` (unsigned) instead of
  `false`.

## What lives here (by role)

* `jolt_lbu_bridge` — specialisation: Jolt's logic-phase expression equals
  `zero_extend (loaded_byte_at …)`.
* `lbuProgram_concrete` — the program-level Jolt execution fact.
* `execute_LBU_reduces` — the Sail-side `execute_LOAD … true 1` reduction.
* `lbuProgram_eq_sail` — the main equivalence theorem.
-/

/-- **Bridge lemma for LBU.** The Jolt logic-phase computation (XOR with 7,
    SLL by 3, SLL the dword, logical-shift-right by 56) equals the
    Sail-side direct byte load zero-extended to 64 bits. Pure bit-vector
    algebra — combines `sll_srli_extracts_byte` with
    `loaded_byte_in_dword`, mirroring `jolt_lb_bridge` modulo
    sign→zero-extend. -/
theorem jolt_lbu_bridge (s : SailState) (addr : BitVec 64)
    (hbytes_base : MemBytesPresentAt s (addr &&& (-8 : BitVec 64)) 8)
    (h_no_ovf_base : (addr &&& (-8 : BitVec 64)).toNat + 7 < 2 ^ 64)
    (hpresent : MemBytePresentAt s addr.toNat) :
    (let dword     := loaded_dword_at s (addr &&& (-8 : BitVec 64))
        hbytes_base h_no_ovf_base
     let xor_addr  := addr ^^^ (7 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6   := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted   := shift_bits_left dword shift_6
     shift_bits_right shifted (56 : BitVec 6))
    = zero_extend (m := 64) (loaded_byte_at s addr hpresent) := by
  simp only [sll_srli_extracts_byte,
    ← loaded_byte_in_dword s addr hbytes_base h_no_ovf_base hpresent]

-- ============================================================================
-- Top-level LBU ↔ Sail equivalence theorems
-- ============================================================================

/-- Sail-side `execute_LOAD imm rs1 rd true 1` reduces to
    `stateAfterWrite rd (zero_extend (loaded_byte_at ea))`. The `true`
    flag selects the unsigned branch in Sail's `extend_value`.

    Structurally identical to `execute_LB_reduces` in `LB_main.lean`; the
    only differences from the LB version are marked `-- DIFF:` below. -/
theorem execute_LBU_reduces (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (hbytes : MemBytesPresentAt js.sail (load_effective_address val imm) 1)
    (hload_pmp : Assumptions.LoadPmpOk (load_effective_address val imm) 1 js.sail)
    (hread_mmio : Assumptions.NotReadableMmio (load_effective_address val imm) 1 js.sail) :
    -- DIFF: `execute_LOAD` is called with `true` (unsigned) not `false`.
    (execute_LOAD imm rs1 rd true 1).run js.sail =
    .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd
        -- DIFF: `zero_extend` not `sign_extend`.
        (zero_extend (m := 64)
          (loaded_byte_at js.sail (load_effective_address val imm)
            (by simpa using hbytes 0 (by omega))))) := by
  unfold execute_LOAD
  simp only [bind, pure]
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  simp (config := { decide := true }) only []
  simp (config := { decide := true }) only [PreSail.assert, EStateM.bind, pure, EStateM.pure,
       EStateM.run, if_true]
  rw [vmem_read_byte_reduces imm rs1 js.sail hpriv hmprv val hrx
      (aligned_access_1 (load_effective_address val imm))
      (loaded_byte_at js.sail (load_effective_address val imm)
        (by simpa using hbytes 0 (by omega)))
      (mem_read_1_eq_loaded_byte _ js.sail hpriv hmprv hbytes hload_pmp
        hread_mmio)]
  -- DIFF: `if_true` instead of `Bool.false_eq_true, if_false` — the unsigned
  --       branch in `extend_value` is gated on the `true` signed flag, so the
  --       opposite branch fires compared to LB.
  simp only [extend_value, if_true, EStateM.bind, EStateM.pure]
  obtain ⟨s', hw⟩ := wX_shape rd
    -- DIFF: `zero_extend` not `sign_extend`, as in the goal.
    (zero_extend (m := 64)
      (loaded_byte_at js.sail (load_effective_address val imm)
        (by simpa using hbytes 0 (by omega))))
    js.sail
  rw [hw]
  simp only [RETIRE_SUCCESS]
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

/-!
## Program-level LBU theorem

The Jolt side is now the structured `JoltISA.lbuProgram`.  This is identical
to the program-level `LB` proof except for the final unsigned `SRLI` writeback
and the pure bridge theorem's `zero_extend` result.
-/

/-- Program-level execution for LBU.

The common setup and lane-positioning facts are shared with `LB`; the final
write block is the logical-right-shift version, which zero-fills the result
before writing the architectural destination. -/
theorem lbuProgram_concrete (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (hbytes_base :
      MemBytesPresentAt js.sail (compute_aligned_dword_base_address val imm) 8)
    (hload_pmp_base :
      Assumptions.LoadPmpOk (compute_aligned_dword_base_address val imm) 8 js.sail)
    (hread_mmio_base :
      Assumptions.NotReadableMmio (compute_aligned_dword_base_address val imm) 8 js.sail)
    (hbytes_byte : MemBytesPresentAt js.sail (load_effective_address val imm) 1) :
    ∃ js' : SailJoltState,
      (JoltISA.execProgram (JoltISA.lbuProgram imm rs1 rd)).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (zero_extend (m := 64)
          (loaded_byte_at js.sail (load_effective_address val imm)
            (by simpa using hbytes_byte 0 (by omega)))) := by
  let writeTail : JoltISA.Program :=
    .instr (.VirtualSRLI (.xreg rd) (.vreg JoltISA.inlineTmp1) (JoltISA.srliBitmask (56 : BitVec 6)))
      (.done RETIRE_SUCCESS)
  let logicTail : JoltISA.Program :=
    .instr (.XORI (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp0) (7 : BitVec 12)) <|
    JoltISA.slliBlock (.vreg JoltISA.inlineTmp0) (.vreg JoltISA.inlineTmp0) (3 : BitVec 6) <|
    JoltISA.sllBlock (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp0) JoltISA.inlineTmp2 writeTail
  rcases LoadProgramBlocks.setupBlock logicTail imm rs1 js hpriv hmprv val hrx
      hbytes_base hload_pmp_base hread_mmio_base with
    ⟨js_load, hload_run, hload_sail, hload_v0, hload_v1⟩
  let dword := loaded_dword_at js.sail (compute_aligned_dword_base_address val imm)
    hbytes_base (aligned_dword_addr_is_aligned_dword_access val imm).no_ovf
  rcases LoadProgramBlocks.xoriSlliSllBlock writeTail imm (7 : BitVec 12)
      js js_load val dword hload_sail hload_v0 hload_v1 with
    ⟨js_shift, hlogic_run, hshift_sail, _hshift_v0, hshift_v1⟩
  let shiftedValue :=
    shift_bits_left
      dword
      (Sail.BitVec.extractLsb
        (shift_bits_left
          (load_effective_address val imm ^^^ sign_extend (m := 64) (7 : BitVec 12))
          (3 : BitVec 6)) 5 0)
  have hshifted : js_shift.vregs JoltISA.inlineTmp1 = shiftedValue := by
    simpa [shiftedValue] using hshift_v1
  rcases LoadProgramBlocks.srliWriteBlock (.done RETIRE_SUCCESS)
      rd (56 : BitVec 6) js js_shift shiftedValue hshift_sail hshifted with
    ⟨js', hwrite_run, hwrite_sail⟩
  refine ⟨js', ?_, ?_⟩
  · unfold JoltISA.lbuProgram
    change (JoltISA.execProgram
      (.instr (.ADDI (.vreg JoltISA.inlineTmp0) (.xreg rs1) imm) <|
       .instr (.ANDI (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp0) (-8 : BitVec 12)) <|
       .instr (.LD (.vreg JoltISA.inlineTmp1) (.vreg JoltISA.inlineTmp1) 0) logicTail)).run js = .ok RETIRE_SUCCESS js'
    rw [hload_run, hlogic_run, hwrite_run]
    rfl
  · rw [hwrite_sail]
    exact congrArg (stateAfterWrite js.sail rd) (by
      have h7 : sign_extend (m := 64) (7 : BitVec 12) = (7 : BitVec 64) := by decide
      simpa [shiftedValue, compute_aligned_dword_base_address, h7] using
        (jolt_lbu_bridge js.sail (load_effective_address val imm)
          (by simpa [compute_aligned_dword_base_address] using hbytes_base)
          (by
            simpa [compute_aligned_dword_base_address] using
              (aligned_dword_addr_is_aligned_dword_access val imm).no_ovf)
          (by simpa using hbytes_byte 0 (by omega))))

/-- Successful `LBU` expansions do not modify the persistent CSR virtual
registers materialized by `systemProject`. -/
theorem lbuProgram_preserves_projected_vregs
    (imm : BitVec 12) (rs1 rd : regidx)
    {js js' : SailJoltState} {result : ExecutionResult}
    (hrun : (JoltISA.execProgram (JoltISA.lbuProgram imm rs1 rd)).run js =
      .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe : JoltISA.ProgramWritesNoProtectedVReg
      (JoltISA.lbuProgram imm rs1 rd) := by
    unfold JoltISA.lbuProgram JoltISA.slliBlock JoltISA.sllBlock
    simp [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg,
      JoltISA.DstWritesNoProtectedVReg,
      JoltISA.loadV0, JoltISA.loadV1, JoltISA.loadInlineTmp]
  exact Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    hsafe hrun

/-- **Main program theorem for LBU.**  The structured Jolt-ISA expansion
matches Sail after materializing Jolt's persistent CSR virtual registers. -/
def lbuProgramEqSailStatement (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (_h : LoadProgramEqSailAssumptions imm rs1 js) : Prop :=
    System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.lbuProgram imm rs1 rd)).run js) =
    (execute_LOAD imm rs1 rd true 1).run js.sail

/-- **Main program theorem for LBU.**  The structured Jolt-ISA expansion
matches Sail after materializing Jolt's persistent CSR virtual registers. -/
theorem lbuProgram_eq_sail (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    lbuProgramEqSailStatement imm rs1 rd js h := by
  unfold lbuProgramEqSailStatement
  let ea := load_effective_address h.rs1_val imm
  let base := compute_aligned_dword_base_address h.rs1_val imm
  let offset := (ea &&& (7 : BitVec 64)).toNat
  have h_base_aligned : AlignedDwordAccess base := by
    simpa [base, compute_aligned_dword_base_address, aligned_dword_addr_eq,
      load_effective_address] using
      aligned_dword_addr_is_aligned_dword_access h.rs1_val imm
  have hbytes_base : MemBytesPresentAt js.sail base 8 := by
    simpa [base] using h.dword_present.memBytesPresentAt
  have hload_pmp_base : Assumptions.LoadPmpOk base 8 js.sail := by
    simpa [base] using h.load_pmp.subaccess (offset := 0) (accessWidth := 8) (by omega)
  have hread_mmio_base : Assumptions.NotReadableMmio base 8 js.sail := by
    simpa [base] using h.not_readable_mmio.subaccess
      (offset := 0) (accessWidth := 8) (by omega)
  have hoff : offset + 1 ≤ 8 := by
    have hlt : offset < 8 := by
      simpa only [offset] using addr_and_seven_lt_eight ea
    omega
  have haddr : base + BitVec.ofNat 64 offset = ea := by
    simpa [base, ea, offset, compute_aligned_dword_base_address] using
      addr_split_aligned_offset ea
  have hbytes_byte : MemBytesPresentAt js.sail ea 1 := by
    have hsub : MemBytesPresentAt js.sail (base + BitVec.ofNat 64 offset) 1 :=
      memBytesPresentAt_subaccess (s := js.sail) (base := base) (baseWidth := 8)
        (offset := offset) (accessWidth := 1) hbytes_base hoff (by
          have hbase_no_ovf := h_base_aligned.no_ovf
          omega)
    simpa [haddr] using hsub
  have hload_pmp_byte : Assumptions.LoadPmpOk ea 1 js.sail := by
    have hsub : Assumptions.LoadPmpOk (base + BitVec.ofNat 64 offset) 1 js.sail :=
      h.load_pmp.subaccess (offset := offset) (accessWidth := 1) hoff
    simpa [base, haddr] using hsub
  have hread_mmio_byte : Assumptions.NotReadableMmio ea 1 js.sail := by
    have hsub : Assumptions.NotReadableMmio (base + BitVec.ofNat 64 offset) 1 js.sail :=
      h.not_readable_mmio.subaccess (offset := offset) (accessWidth := 1) hoff
    simpa [base, haddr] using hsub
  rcases lbuProgram_concrete imm rs1 rd js h.cur_privilege h.mstatus_mprv h.rs1_val
      h.rs1_read
      (by simpa [base] using hbytes_base)
      (by simpa [base] using hload_pmp_base)
      (by simpa [base] using hread_mmio_base)
      (by simpa [ea] using hbytes_byte) with
    ⟨js', hjolt, hjolt_sail⟩
  have hsail := execute_LBU_reduces imm rs1 rd js h.cur_privilege
    h.mstatus_mprv h.rs1_val h.rs1_read
    (by simpa [ea] using hbytes_byte)
    (by simpa [ea] using hload_pmp_byte)
    (by simpa [ea] using hread_mmio_byte)
  have h_project_initial : System.systemProject js = js.sail :=
    Projection.systemProject_eq_sail_of_compatible js h.linkedCSRs
  have h_projected_vregs : Projection.ProjectedVRegsPreserved js js' :=
    lbuProgram_preserves_projected_vregs imm rs1 rd hjolt
  rw [hjolt, hsail]
  simp only [System.systemProjectResult]
  congr 1
  rw [Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved
    js js' rd
    (zero_extend (m := 64)
      (loaded_byte_at js.sail (load_effective_address h.rs1_val imm)
        (by simpa [ea] using hbytes_byte 0 (by omega))))
    hjolt_sail h_projected_vregs]
  rw [h_project_initial]

end LBU_main
