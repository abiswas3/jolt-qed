import JoltBytecode.InstructionEquivalence.System.Common

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace System

/-!
# CSRRW system expansion

Rust's CSRRW expansion treats the supported ZeroOS machine CSRs as persistent
virtual registers:

* `rd = x0`: `ADDI csr_vr, rs1, 0`
* `rd != x0`, `rd = rs1`: preserve `rs1` in scratch, read old CSR into `rd`,
  then restore the preserved value into the CSR virtual register
* `rd != x0`, `rd != rs1`: read old CSR into `rd`, then write `rs1` into the
  CSR virtual register

The raw Sail path goes through `execute_CSRReg` and `doCSR`: it checks CSR
permissions, reads the architectural CSR unless this is write-only `csrw`,
legalizes/writes the architectural CSR, runs a callback, and writes the old CSR
value to `rd`.  The theorem below keeps those generated CSR/legalizer facts
explicit instead of silently assuming all CSR writes are raw writes.
-/

/-- Final state for the write-only `csrw csr, rs1` case. -/
def csrrwAfterCsrWrite
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rs1Val : BitVec 64) :
    SailJoltState :=
  joltSetVReg js (JoltISA.SystemCSR.vreg csr) rs1Val

/-- Final state for the ordinary read/write case after `rd` receives the old
CSR value and the virtual CSR receives `rs1`. -/
def csrrwAfterReadWrite
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rd : regidx)
    (oldCsr rs1Val : BitVec 64) : SailJoltState :=
  joltSetVReg { js with sail := stateAfterWrite js.sail rd oldCsr }
    (JoltISA.SystemCSR.vreg csr) rs1Val

/-- Final state for the `rd = rs1` clobber case.  The scratch write is kept in
the concrete state because it is a real emitted row, though `systemProject`
ignores it. -/
def csrrwAfterSameReg
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rd : regidx)
    (oldCsr rs1Val : BitVec 64) : SailJoltState :=
  joltSetVReg
    { joltSetVReg js JoltISA.systemScratchVReg rs1Val with
      sail := stateAfterWrite js.sail rd oldCsr }
    (JoltISA.SystemCSR.vreg csr) rs1Val

/-- The concrete final Jolt state selected by Rust's CSRRW expansion branches. -/
def csrrwJoltFinal
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rs1 rd : regidx)
    (rs1Val : BitVec 64) : SailJoltState :=
  if JoltISA.isX0 rd then
    csrrwAfterCsrWrite js csr rs1Val
  else if JoltISA.sameXReg rd rs1 then
    csrrwAfterSameReg js csr rd (js.vregs (JoltISA.SystemCSR.vreg csr)) rs1Val
  else
    csrrwAfterReadWrite js csr rd (js.vregs (JoltISA.SystemCSR.vreg csr)) rs1Val

/-- A zero-immediate ADDI copies its source value unchanged. -/
theorem csrrw_addi_zero (x : BitVec 64) :
    x + sign_extend (m := 64) (0 : BitVec 12) = x :=
  addi_zero_value x

/-- The Rust-allocated system scratch virtual register is distinct from every
supported virtual CSR register. -/
theorem systemScratch_ne_systemCSR_vreg
    (csr : JoltISA.SystemCSR) :
    JoltISA.systemScratchVReg ≠ JoltISA.SystemCSR.vreg csr := by
  cases csr <;> native_decide

/-- Conversely, every supported virtual CSR register is distinct from the
instruction-local system scratch register. -/
theorem systemCSR_vreg_ne_systemScratch
    (csr : JoltISA.SystemCSR) :
    JoltISA.SystemCSR.vreg csr ≠ JoltISA.systemScratchVReg := by
  intro h
  exact systemScratch_ne_systemCSR_vreg csr h.symm

/-- If the Boolean `isX0` branch is taken, the generated register index is the
architectural zero register. -/
theorem regidx_eq_zero_of_isX0_eq_true
    {rd : regidx} (h : JoltISA.isX0 rd = true) :
    rd = regidx.Regidx 0 := by
  cases rd with
  | Regidx bits =>
      unfold JoltISA.isX0 at h
      have hbits : bits.toNat = 0 := of_decide_eq_true h
      congr
      apply BitVec.eq_of_toNat_eq
      simpa using hbits

/-- In the `rd = x0` Rust branch, Sail's `rd == zreg` test takes the same
write-only branch. -/
theorem beq_zreg_eq_true_of_isX0_eq_true
    {rd : regidx} (h : JoltISA.isX0 rd = true) :
    (rd == zreg) = true := by
  rw [regidx_eq_zero_of_isX0_eq_true h]
  unfold zreg
  native_decide

/-- Writing architectural `x0` is a no-op, phrased from the Jolt `isX0`
guard so the main proof does not rewrite through indexed assumptions. -/
theorem wX_bits_noop_of_isX0_eq_true
    {rd : regidx} (h : JoltISA.isX0 rd = true)
    (v : BitVec 64) (s : SailState) :
    wX_bits rd v s = .ok () s := by
  rw [regidx_eq_zero_of_isX0_eq_true h]
  exact wX_bits_regidx_zero v s

/-- In the `rd != x0` Rust branches, Sail's `rd == zreg` test takes the
read/write branch. -/
theorem beq_zreg_eq_false_of_isX0_eq_false
    {rd : regidx} (h : JoltISA.isX0 rd = false) :
    (rd == zreg) = false := by
  cases rd with
  | Regidx bits =>
      unfold JoltISA.isX0 at h
      have hbits_ne : bits.toNat ≠ 0 := by
        exact of_decide_eq_false h
      have hbits : bits ≠ (0#5 : BitVec 5) := by
        intro hzero
        apply hbits_ne
        rw [hzero]
        rfl
      unfold zreg
      change (bits == (0#5 : BitVec 5)) = false
      exact beq_false_of_ne hbits

/-- Boolean case helper used when branching on generated Boolean guards. -/
theorem bool_eq_false_of_ne_true {b : Bool} (h : b ≠ true) :
    b = false := by
  cases b <;> simp_all

/-- Copy `rs1` into the CSR virtual register for the `rd = x0` branch. -/
theorem csrrw_write_only_row_run
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rs1 : regidx)
    (rs1Val : BitVec 64)
    (h_rs1 : rX_bits rs1 js.sail = .ok rs1Val js.sail) :
    (JoltISA.execInstr
      (.ADDI (.vreg (JoltISA.SystemCSR.vreg csr)) (.xreg rs1)
        (0 : BitVec 12))).run js =
      .ok RETIRE_SUCCESS (csrrwAfterCsrWrite js csr rs1Val) := by
  have hRun :=
    JoltISA.addi_run_vreg_xreg (JoltISA.SystemCSR.vreg csr) rs1
      (0 : BitVec 12) js rs1Val h_rs1
  rw [csrrw_addi_zero rs1Val] at hRun
  simpa [csrrwAfterCsrWrite, joltSetVReg, vregWrite] using hRun

/-- Read the old CSR virtual register into architectural `rd`. -/
theorem csrrw_read_old_row_run
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rd : regidx)
    (oldCsr : BitVec 64) :
    oldCsr = js.vregs (JoltISA.SystemCSR.vreg csr) →
    (JoltISA.execInstr
      (.ADDI (.xreg rd) (.vreg (JoltISA.SystemCSR.vreg csr))
        (0 : BitVec 12))).run js =
      .ok RETIRE_SUCCESS
        { js with sail := stateAfterWrite js.sail rd oldCsr } := by
  intro h_old
  obtain ⟨s', hw⟩ := wX_shape rd
    (js.vregs (JoltISA.SystemCSR.vreg csr) +
      sign_extend (m := 64) (0 : BitVec 12)) js.sail
  have hs' :
      s' = stateAfterWrite js.sail rd oldCsr := by
    have hw' :
        wX_bits rd oldCsr js.sail = .ok () s' := by
      rw [csrrw_addi_zero (js.vregs (JoltISA.SystemCSR.vreg csr))] at hw
      simpa [h_old] using hw
    exact wX_bits_eq_stateAfterWrite rd oldCsr js.sail s' hw'
  have hRun :=
    JoltISA.addi_run_xreg_vreg rd (JoltISA.SystemCSR.vreg csr)
      (0 : BitVec 12) js s' hw
  rw [hs'] at hRun
  exact hRun

/-- Preserve `rs1` in the system scratch virtual register for the `rd = rs1`
clobber branch. -/
theorem csrrw_preserve_rs1_row_run
    (js : SailJoltState) (rs1 : regidx) (rs1Val : BitVec 64)
    (h_rs1 : rX_bits rs1 js.sail = .ok rs1Val js.sail) :
    (JoltISA.execInstr
      (.ADDI (.vreg JoltISA.systemScratchVReg) (.xreg rs1)
        (0 : BitVec 12))).run js =
      .ok RETIRE_SUCCESS (joltSetVReg js JoltISA.systemScratchVReg rs1Val) := by
  have hRun :=
    JoltISA.addi_run_vreg_xreg JoltISA.systemScratchVReg rs1
      (0 : BitVec 12) js rs1Val h_rs1
  rw [csrrw_addi_zero rs1Val] at hRun
  simpa [joltSetVReg, vregWrite] using hRun

/-- Restore the preserved source value from scratch into the CSR virtual
register. -/
theorem csrrw_restore_csr_from_scratch_row_run
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rd : regidx)
    (oldCsr rs1Val : BitVec 64) :
    (JoltISA.execInstr
      (.ADDI (.vreg (JoltISA.SystemCSR.vreg csr))
        (.vreg JoltISA.systemScratchVReg) (0 : BitVec 12))).run
        { joltSetVReg js JoltISA.systemScratchVReg rs1Val with
          sail := stateAfterWrite js.sail rd oldCsr } =
      .ok RETIRE_SUCCESS (csrrwAfterSameReg js csr rd oldCsr rs1Val) := by
  unfold JoltISA.execInstr JoltISA.readSrc JoltISA.writeDst readVReg writeVReg
  unfold csrrwAfterSameReg joltSetVReg vregWrite
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    csrrw_addi_zero]
  simp only [if_true]

/-- Rust's full CSRRW Jolt program reaches the branch-selected concrete final
state.  The `rd != rs1` branch needs the ordinary register-file fact that
writing `rd` does not change a later read from distinct `rs1`; this is exposed
as a hypothesis here so the top-level theorem records the exact proof pressure. -/
theorem csrrwProgram_run
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rs1 rd : regidx)
    (rs1Val : BitVec 64)
    (h_rs1 : rX_bits rs1 js.sail = .ok rs1Val js.sail)
    (h_rs1_after_rd :
      ∀ oldCsr : BitVec 64,
        JoltISA.isX0 rd = false →
        JoltISA.sameXReg rd rs1 = false →
        rX_bits rs1 (stateAfterWrite js.sail rd oldCsr) =
          .ok rs1Val (stateAfterWrite js.sail rd oldCsr)) :
    (JoltISA.execProgram (JoltISA.csrrwProgram csr rs1 rd)).run js =
      .ok RETIRE_SUCCESS (csrrwJoltFinal js csr rs1 rd rs1Val) := by
  unfold JoltISA.csrrwProgram csrrwJoltFinal
  by_cases h_x0 : JoltISA.isX0 rd = true
  · rw [h_x0]
    simp only [if_true]
    rw [JoltISA.execProgram_instr_run_retire _ _ js
      (csrrwAfterCsrWrite js csr rs1Val)
      (csrrw_write_only_row_run js csr rs1 rs1Val h_rs1)]
    simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure]
  · have h_x0_false : JoltISA.isX0 rd = false := bool_eq_false_of_ne_true h_x0
    rw [h_x0_false]
    simp only [Bool.false_eq_true, if_false]
    by_cases h_same : JoltISA.sameXReg rd rs1 = true
    · rw [h_same]
      simp only [if_true]
      let js_preserved := joltSetVReg js JoltISA.systemScratchVReg rs1Val
      let js_read :
          SailJoltState :=
        { js_preserved with
          sail := stateAfterWrite js.sail rd
            (js.vregs (JoltISA.SystemCSR.vreg csr)) }
      have hPreserve :
          (JoltISA.execInstr
            (.ADDI (.vreg JoltISA.systemScratchVReg) (.xreg rs1)
              (0 : BitVec 12))).run js =
            .ok RETIRE_SUCCESS js_preserved := by
        simpa [js_preserved] using
          csrrw_preserve_rs1_row_run js rs1 rs1Val h_rs1
      have hRead :
          (JoltISA.execInstr
            (.ADDI (.xreg rd) (.vreg (JoltISA.SystemCSR.vreg csr))
              (0 : BitVec 12))).run js_preserved =
            .ok RETIRE_SUCCESS js_read := by
        have hOld :
            js.vregs (JoltISA.SystemCSR.vreg csr) =
              js_preserved.vregs (JoltISA.SystemCSR.vreg csr) := by
          simp [js_preserved, joltSetVReg, vregWrite,
            systemCSR_vreg_ne_systemScratch csr]
        have hRow :=
          csrrw_read_old_row_run js_preserved csr rd
            (js.vregs (JoltISA.SystemCSR.vreg csr)) hOld
        simpa [js_preserved, js_read] using hRow
      have hRestore :
          (JoltISA.execInstr
            (.ADDI (.vreg (JoltISA.SystemCSR.vreg csr))
              (.vreg JoltISA.systemScratchVReg) (0 : BitVec 12))).run js_read =
            .ok RETIRE_SUCCESS
              (csrrwAfterSameReg js csr rd
                (js.vregs (JoltISA.SystemCSR.vreg csr)) rs1Val) := by
        simpa [js_preserved, js_read] using
          csrrw_restore_csr_from_scratch_row_run js csr rd
            (js.vregs (JoltISA.SystemCSR.vreg csr)) rs1Val
      rw [JoltISA.execProgram_instr_run_retire _ _ js js_preserved hPreserve]
      rw [JoltISA.execProgram_instr_run_retire _ _ js_preserved js_read hRead]
      rw [JoltISA.execProgram_instr_run_retire _ _ js_read
        (csrrwAfterSameReg js csr rd
          (js.vregs (JoltISA.SystemCSR.vreg csr)) rs1Val) hRestore]
      simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure]
    · have h_same_false :
          JoltISA.sameXReg rd rs1 = false := bool_eq_false_of_ne_true h_same
      rw [h_same_false]
      simp only [Bool.false_eq_true, if_false]
      let js_read : SailJoltState :=
        { js with
          sail := stateAfterWrite js.sail rd
            (js.vregs (JoltISA.SystemCSR.vreg csr)) }
      have hRead :
          (JoltISA.execInstr
            (.ADDI (.xreg rd) (.vreg (JoltISA.SystemCSR.vreg csr))
              (0 : BitVec 12))).run js =
            .ok RETIRE_SUCCESS js_read := by
        simpa [js_read] using
          csrrw_read_old_row_run js csr rd
            (js.vregs (JoltISA.SystemCSR.vreg csr)) rfl
      have hWrite :
          (JoltISA.execInstr
            (.ADDI (.vreg (JoltISA.SystemCSR.vreg csr)) (.xreg rs1)
              (0 : BitVec 12))).run js_read =
            .ok RETIRE_SUCCESS
              (csrrwAfterReadWrite js csr rd
                (js.vregs (JoltISA.SystemCSR.vreg csr)) rs1Val) := by
        have hReadRs1 := h_rs1_after_rd
          (js.vregs (JoltISA.SystemCSR.vreg csr)) h_x0_false h_same_false
        have hRow :=
          csrrw_write_only_row_run js_read csr rs1 rs1Val hReadRs1
        simpa [js_read, csrrwAfterCsrWrite, csrrwAfterReadWrite] using hRow
      rw [JoltISA.execProgram_instr_run_retire _ _ js js_read hRead]
      rw [JoltISA.execProgram_instr_run_retire _ _ js_read
        (csrrwAfterReadWrite js csr rd
          (js.vregs (JoltISA.SystemCSR.vreg csr)) rs1Val) hWrite]
      simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure]

/-- Explicit assumptions forced by comparing Rust/Jolt CSRRW to raw generated
Sail `execute_CSRReg`.

The CSR read/write fields are intentionally at the generated Sail CSR boundary:
for `mstatus`, `mtvec`, and `mepc` they are where Sail legalizes or aligns
values while Rust stores raw virtual-register values.  Later proofs should
discharge these fields from concrete ZeroOS invariants such as "`mepc` is
already xepc-legal" or "`mstatus` is already fixed by `legalize_mstatus`",
rather than weakening the theorem. -/
structure CsrrwSystemAssumptions
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rs1 rd : regidx) :
    Type where
  rs1_val : BitVec 64
  source_read_jolt :
    rX_bits rs1 js.sail = .ok rs1_val js.sail
  source_read_after_rd_write :
    ∀ oldCsr : BitVec 64,
      JoltISA.isX0 rd = false →
      JoltISA.sameXReg rd rs1 = false →
      rX_bits rs1 (stateAfterWrite js.sail rd oldCsr) =
        .ok rs1_val (stateAfterWrite js.sail rd oldCsr)
  cur_privilege_machine :
    (systemProject js).regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege)
  csr_check_succeeds :
    check_CSR (JoltISA.SystemCSR.address csr) Privilege.Machine
        (csr_access_type csrop.CSRRW (rd == zreg) (rs1 == zreg))
        (systemProject js) =
      .ok true (systemProject js)
  csr_read_matches :
    JoltISA.isX0 rd = false →
      read_CSR (JoltISA.SystemCSR.address csr) (systemProject js) =
        .ok (js.vregs (JoltISA.SystemCSR.vreg csr)) (systemProject js)
  csr_write_matches :
    write_CSR (JoltISA.SystemCSR.address csr) rs1_val (systemProject js) =
      .ok (Result.Ok rs1_val)
        (systemProject (csrrwAfterCsrWrite js csr rs1_val))
  rd_write_projects :
    ∀ oldCsr : BitVec 64,
      JoltISA.isX0 rd = false →
        wX_bits rd oldCsr
            (systemProject (csrrwAfterCsrWrite js csr rs1_val)) =
          .ok ()
            (systemProject
              (csrrwJoltFinal js csr rs1 rd rs1_val))

/-- The generated CSR-id write callback is state-neutral for the supported
system CSR whitelist. -/
theorem csr_id_write_callback_systemCSR_run
    (s : SailState) (csr : JoltISA.SystemCSR) (value : BitVec 64) :
    csr_id_write_callback (JoltISA.SystemCSR.address csr) value s =
      .ok () s := by
  cases csr <;>
    unfold csr_id_write_callback csr_full_write_callback
      JoltISA.SystemCSR.address <;>
    rfl

/-- Sail's raw CSRRW execution reaches the projected Jolt final state under the
explicit CSR/legalizer and architectural-register obligations. -/
theorem execute_CSRReg_csrrw_system_run
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rs1 rd : regidx)
    (h_sys : CsrrwSystemAssumptions js csr rs1 rd) :
    (execute_CSRReg (JoltISA.SystemCSR.address csr) rs1 rd csrop.CSRRW).run
        (systemProject js) =
      .ok RETIRE_SUCCESS
        (systemProject
          (csrrwJoltFinal js csr rs1 rd h_sys.rs1_val)) := by
  have hSourceSail :
      rX_bits rs1 (systemProject js) =
        .ok h_sys.rs1_val (systemProject js) :=
    systemProject_rX_bits js rs1 h_sys.rs1_val h_sys.source_read_jolt
  by_cases h_x0 : JoltISA.isX0 rd = true
  · have h_beq := beq_zreg_eq_true_of_isX0_eq_true h_x0
    have hCheck :
        check_CSR (JoltISA.SystemCSR.address csr) Privilege.Machine
            CSRAccessType.CSRWrite (systemProject js) =
          .ok true (systemProject js) := by
      simpa [csr_access_type, h_beq] using h_sys.csr_check_succeeds
    have hExtCheck :
        ext_check_CSR (JoltISA.SystemCSR.address csr) Privilege.Machine
          CSRAccessType.CSRWrite = true := by
      unfold ext_check_CSR
      rfl
    have hAccessWriteWrite :
        instBEqCSRAccessType.beq CSRAccessType.CSRWrite
            CSRAccessType.CSRWrite = true := by
      native_decide
    have hAccessWriteRead :
        instBEqCSRAccessType.beq CSRAccessType.CSRWrite
            CSRAccessType.CSRRead = false := by
      native_decide
    have hCallback :=
      csr_id_write_callback_systemCSR_run
        (systemProject (csrrwAfterCsrWrite js csr h_sys.rs1_val))
        csr h_sys.rs1_val
    unfold execute_CSRReg doCSR Sail.readReg PreSail.readReg
    simp only [hSourceSail, h_sys.cur_privilege_machine,
      csr_access_type, h_beq, bind, EStateM.bind, pure, EStateM.pure,
      EStateM.run, get, getThe, MonadStateOf.get, EStateM.get]
    rw [hCheck]
    simp [LeanRV64D.Functions.not, h_sys.cur_privilege_machine,
      hExtCheck, bne, BEq.beq, EStateM.bind, EStateM.pure,
      EStateM.get, get, MonadStateOf.get, hAccessWriteWrite,
      hAccessWriteRead]
    rw [h_sys.csr_write_matches]
    simp only [EStateM.bind, EStateM.pure]
    rw [hCallback]
    simp only [EStateM.bind, EStateM.pure]
    have hw0 :
        wX_bits rd (zeros (n := 64))
            (systemProject (csrrwAfterCsrWrite js csr h_sys.rs1_val)) =
          .ok () (systemProject (csrrwAfterCsrWrite js csr h_sys.rs1_val)) := by
      exact wX_bits_noop_of_isX0_eq_true h_x0 (zeros (n := 64))
        (systemProject (csrrwAfterCsrWrite js csr h_sys.rs1_val))
    have hFinal :
        csrrwJoltFinal js csr rs1 rd h_sys.rs1_val =
          csrrwAfterCsrWrite js csr h_sys.rs1_val := by
      simp [csrrwJoltFinal, h_x0]
    rw [hw0, hFinal]
  · have h_x0_false : JoltISA.isX0 rd = false := bool_eq_false_of_ne_true h_x0
    have h_beq := beq_zreg_eq_false_of_isX0_eq_false h_x0_false
    have hCheck :
        check_CSR (JoltISA.SystemCSR.address csr) Privilege.Machine
            CSRAccessType.CSRReadWrite (systemProject js) =
          .ok true (systemProject js) := by
      simpa [csr_access_type, h_beq] using h_sys.csr_check_succeeds
    have hExtCheck :
        ext_check_CSR (JoltISA.SystemCSR.address csr) Privilege.Machine
          CSRAccessType.CSRReadWrite = true := by
      unfold ext_check_CSR
      rfl
    have hAccessReadWriteWrite :
        instBEqCSRAccessType.beq CSRAccessType.CSRReadWrite
            CSRAccessType.CSRWrite = false := by
      native_decide
    have hAccessReadWriteRead :
        instBEqCSRAccessType.beq CSRAccessType.CSRReadWrite
            CSRAccessType.CSRRead = false := by
      native_decide
    have hCallback :=
      csr_id_write_callback_systemCSR_run
        (systemProject (csrrwAfterCsrWrite js csr h_sys.rs1_val))
        csr h_sys.rs1_val
    unfold execute_CSRReg doCSR Sail.readReg PreSail.readReg
    simp only [hSourceSail, h_sys.cur_privilege_machine,
      csr_access_type, h_beq, bind, EStateM.bind, pure, EStateM.pure,
      EStateM.run, get, getThe, MonadStateOf.get, EStateM.get]
    rw [hCheck]
    simp [LeanRV64D.Functions.not, h_sys.cur_privilege_machine,
      hExtCheck, bne, BEq.beq, EStateM.bind, EStateM.pure,
      EStateM.get, get, MonadStateOf.get, hAccessReadWriteWrite,
      hAccessReadWriteRead]
    rw [h_sys.csr_read_matches h_x0_false]
    simp only [EStateM.bind, EStateM.pure]
    rw [h_sys.csr_write_matches]
    simp only [EStateM.bind, EStateM.pure]
    rw [hCallback]
    simp only [EStateM.bind, EStateM.pure]
    rw [h_sys.rd_write_projects
      (js.vregs (JoltISA.SystemCSR.vreg csr)) h_x0_false]

/-- CSRRW equivalence under the system CSR projection.

The proof is intentionally top-down: the Jolt side is the Rust inline sequence,
and the Sail side is raw generated `execute_CSRReg`.  All nontrivial mismatch
points are named in `CsrrwSystemAssumptions` rather than hidden in the theorem. -/
theorem csrrwProgram_eq_sail
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rs1 rd : regidx)
    (h_sys : CsrrwSystemAssumptions js csr rs1 rd) :
    systemProjectResult
        ((JoltISA.execProgram (JoltISA.csrrwProgram csr rs1 rd)).run js) =
      (execute_CSRReg (JoltISA.SystemCSR.address csr) rs1 rd csrop.CSRRW).run
        (systemProject js) := by
  have hJolt :=
    csrrwProgram_run js csr rs1 rd h_sys.rs1_val
      h_sys.source_read_jolt h_sys.source_read_after_rd_write
  have hSail :=
    execute_CSRReg_csrrw_system_run js csr rs1 rd h_sys
  unfold systemProjectResult
  rw [hJolt]
  exact hSail.symm

end System

end
