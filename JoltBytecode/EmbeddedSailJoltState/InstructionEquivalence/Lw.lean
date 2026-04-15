import JoltBytecode.EmbeddedSailJoltState.Defs
import JoltBytecode.EmbeddedSailJoltState.MemoryUtils
import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadDefUtils
import JoltBytecode.EmbeddedSailJoltState.RtypeW

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

/-!
# LW: Jolt load-word (signed) decomposition

From `tracer/src/instruction/lw.rs::inline_sequence_64`:

    VirtualAssertWordAlignment rs1, imm
    ADDI  v0, rs1, imm
    ANDI  rd, v0, -8
    LD    rd, rd, 0
    SLLI  v0, v0, 3
    SRL   rd, rd, v0
    VirtualSignExtendWord rd, rd, 0
-/

def jolt_lw (imm : BitVec 12) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let base ← liftSail (rX_bits rs1)
  let ea := base + sign_extend (m := 64) imm
  if ea &&& 3 ≠ 0 then
    throw (Error.Assertion "LW: effective address not word-aligned")
  else do
    -- ADDI v0, rs1, imm
    writeVReg 0 ea
    -- ANDI rd, v0, -8  encoded via virtual register 1 for the dword address
    let v0 ← readVReg 0
    writeVReg 1 (v0 &&& (-8 : BitVec 64))
    -- LD rd, rd, 0  encoded as a dword load into virtual register 1
    match ← vreg_LD 1 1 0 with
    | .Retire_Success () =>
        -- SLLI v0, v0, 3
        let _ ← vreg_SLLI 0 0 3
        -- SRL rd, rd, v0
        let _ ← vreg_SRL 1 1 0
        -- VirtualSignExtendWord rd, rd, 0
        let v1 ← readVReg 1
        liftSail (wX_bits rd v1)
        jolt_virtual_sign_extend_word rd
        pure RETIRE_SUCCESS
    | other => pure other

-- Abbreviation for the aligned dword address used by Jolt's LW sequence.
-- ============================================================================
-- New LW-specific bridge layer
--
-- Everything below `vmem_read_addr_dword_reduces` / `vmem_read_*_reduces`
-- is reused from `MemoryUtils.lean`. The lemmas in this section are the
-- new pure bitvector facts specific to LW's "load dword, shift right, then
-- sign-extend the low 32 bits" strategy.
-- ============================================================================

/-- Extract the low 32 bits of `d >>> (8 * k)`. For LW we only care about the
    aligned cases `k = 0` or `k = 4`, corresponding to addresses whose low
    two bits are zero. -/
def word_of_dword (d : BitVec 64) (k : Nat) : BitVec 32 :=
  (d >>> (8 * k)).setWidth 32

/-- If `addr` is word-aligned, then the 32-bit word at `addr` is exactly the
    appropriate 32-bit slice of the enclosing aligned dword. -/
theorem loaded_word_in_dword (s : SailState) (addr : BitVec 64)
    (halign : addr &&& 3 = 0) :
    loaded_word_at s addr =
    word_of_dword
      (loaded_dword_at s (addr &&& (-8 : BitVec 64)))
      (addr &&& 7).toNat := by
  sorry

/-- Jolt's `SLLI addr 3; SRL dword addr; VirtualSignExtendWord` sequence
    extracts the signed word from the enclosing dword. Since LW is word-
    aligned, only the offsets 0 and 4 can occur. -/
theorem srl_sign_extend_word_extracts_word (d : BitVec 64) (addr : BitVec 64)
    (halign : addr &&& 3 = 0) :
    (let shifted := shift_bits_right d (Sail.BitVec.extractLsb (shift_bits_left addr (3 : BitVec 6)) 5 0)
     sign_extend (m := 64) ((Sail.BitVec.extractLsb shifted 31 0) : BitVec 32))
    = sign_extend (m := 64) (word_of_dword d (addr &&& 7).toNat) := by
  sorry

/-- Pure bridge: Jolt's dword-load-and-shift path computes exactly the
    sign-extended `loaded_word_at`. This is the LW analogue of
    `jolt_lb_bridge`. -/
theorem jolt_lw_bridge (s : SailState) (addr : BitVec 64)
    (halign : addr &&& 3 = 0) :
    (let dword := loaded_dword_at s (addr &&& (-8 : BitVec 64))
     let shift := Sail.BitVec.extractLsb (shift_bits_left addr (3 : BitVec 6)) 5 0
     let shifted := shift_bits_right dword shift
     sign_extend (m := 64) ((Sail.BitVec.extractLsb shifted 31 0) : BitVec 32))
    = sign_extend (m := 64) (loaded_word_at s addr) := by
  sorry

theorem execute_LW_reduces (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) (hcfg : JoltConfig js.sail)
    (v : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok v js.sail)
    (hwa : AlignedAccess (v + sign_extend (m := 64) imm) 4)
    (hwt : BareTranslation (v + sign_extend (m := 64) imm) js.sail)
    (hwp : FlatPhysMem (v + sign_extend (m := 64) imm) 4 js.sail)
    (h_no_ovf : (v + sign_extend (m := 64) imm).toNat + 3 < 2 ^ 64) :
    (execute_LOAD imm rs1 rd false 4).run js.sail =
    .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (loaded_word_at js.sail (v + sign_extend (m := 64) imm)))) := by
  unfold execute_LOAD
  simp only [bind, pure]
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  simp (config := { decide := true }) only []
  simp (config := { decide := true }) only [PreSail.assert, EStateM.bind, pure, EStateM.pure,
       EStateM.run, if_true]
  rw [vmem_read_word_reduces imm rs1 js.sail v hrx hwa hwt
      (mem_read_4_eq_loaded_word _ js.sail hcfg h_no_ovf hwp)]
  simp only [extend_value, Bool.false_eq_true, if_false, EStateM.bind, EStateM.pure]
  obtain ⟨s', hw⟩ := wX_shape rd
    (sign_extend (m := 64) (loaded_word_at js.sail (v + sign_extend (m := 64) imm)))
    js.sail
  rw [hw]
  simp only [RETIRE_SUCCESS]
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

theorem jolt_lw_concrete (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) (hcfg : JoltConfig js.sail)
    (v : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok v js.sail)
    (halign : (v + sign_extend (m := 64) imm) &&& 3 = 0)
    (hda : AlignedDwordAccess (aligned_dword_addr v imm))
    (hdt : BareTranslation (aligned_dword_addr v imm) js.sail)
    (hdf : FlatPhysMem (aligned_dword_addr v imm) 8 js.sail) :
    ∃ js' : SailJoltState,
      (jolt_lw imm rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (loaded_word_at js.sail (v + sign_extend (m := 64) imm))) := by
  let ea := v + sign_extend (m := 64) imm
  let daddr := ea &&& (-8 : BitVec 64)
  let dword := loaded_dword_at js.sail daddr
  let shift := Sail.BitVec.extractLsb (shift_bits_left ea (3 : BitVec 6)) 5 0
  let shifted := shift_bits_right dword shift
  let js0 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = 0 then ea else js.vregs r }
  let js1 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = 1 then daddr else if r = 0 then ea else js.vregs r }
  let js2 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = 1 then dword else js1.vregs r }
  let js3 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = 0 then shift_bits_left ea (3 : BitVec 6) else js2.vregs r }
  let js4 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = 1 then shifted else js3.vregs r }
  have hw0 : writeVReg 0 ea js = .ok () js0 := by
    unfold writeVReg js0 ea
    simp [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  have hw1 : writeVReg 1 daddr js0 = .ok () js1 := by
    unfold writeVReg js0 js1 ea daddr
    simp [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  have h_addr_sum : (v + sign_extend (m := 64) imm &&& sign_extend (m := 64) (-8 : BitVec 12))
                      + sign_extend (m := 64) (0 : BitVec 12) =
                    daddr := by
    unfold daddr ea
    have h0 : sign_extend (m := 64) (0 : BitVec 12) = (0 : BitVec 64) := by decide
    have h8 : sign_extend (m := 64) (-8 : BitVec 12) = (-8 : BitVec 64) := by decide
    rw [h0, h8]
    bv_decide
  have h_lw_addr : aligned_dword_addr v imm = daddr := by
    unfold aligned_dword_addr
    exact h_addr_sum
  have hda' : AlignedDwordAccess daddr := by
    simpa [h_lw_addr] using hda
  have hdt' : BareTranslation daddr js.sail := by
    simpa [h_lw_addr] using hdt
  have hdf' : FlatPhysMem daddr 8 js.sail := by
    simpa [h_lw_addr] using hdf
  have hld :
      vreg_LD 1 1 0 js1 = .ok RETIRE_SUCCESS js2 := by
    have hread0 :
        vmem_read_addr (Virtaddr daddr) 0 8 (Load Data) false false false js.sail =
        .ok (Ok dword) js.sail := by
      simpa [dword] using (vmem_read_addr_dword_reduces daddr js.sail hcfg hda' hdt' hdf')
    have hread :
        vmem_read_addr (Virtaddr (js1.vregs 1 + sign_extend (m := 64) (0 : BitVec 12))) 0 8
          (Load Data) false false false js.sail =
        .ok (Ok dword) js.sail := by
      have h0 : sign_extend (m := 64) (0 : BitVec 12) = (0 : BitVec 64) := by decide
      have harg : js1.vregs 1 + sign_extend (m := 64) (0 : BitVec 12) = daddr := by
        rw [h0]
        simp [js1, daddr]
      rw [harg]
      exact hread0
    simpa [js2] using (vreg_LD_run_of_read 1 1 0 js1 dword hread)
  have hslli : vreg_SLLI 0 0 3 js2 = .ok RETIRE_SUCCESS js3 := by
    change vreg_SLLI 0 0 3 js2 = .ok RETIRE_SUCCESS
      { sail := js2.sail
        vregs := fun r => if r = 0 then shift_bits_left (js2.vregs 0) (3 : BitVec 6) else js2.vregs r }
    simpa [js2, js3, ea] using (vreg_SLLI_run 0 0 3 js2)
  have hsrl : vreg_SRL 1 1 0 js3 = .ok RETIRE_SUCCESS js4 := by
    change vreg_SRL 1 1 0 js3 = .ok RETIRE_SUCCESS
      { sail := js3.sail
        vregs := fun r =>
          if r = 1 then shift_bits_right (js3.vregs 1) (Sail.BitVec.extractLsb (js3.vregs 0) 5 0)
          else js3.vregs r }
    simpa [js3, js4, shifted, dword, shift] using (vreg_SRL_run 1 1 0 js3)
  obtain ⟨s5, hw5⟩ := wX_shape rd shifted js.sail
  let js5 : SailJoltState := { sail := s5, vregs := js4.vregs }
  have hwrite : liftSail (wX_bits rd shifted) js4 = .ok () js5 := by
    unfold liftSail js5
    rw [hw5]
  have hs5 : js5.sail = stateAfterWrite js.sail rd shifted := by
    exact wX_bits_eq_stateAfterWrite rd _ js.sail s5 hw5
  have hread_v0 : readVReg 0 js0 = .ok ea js0 := by
    simpa [js0] using (readVReg_run 0 js0)
  have hread_v1 : readVReg 1 js4 = .ok shifted js4 := by
    simpa [js4, js3, js2, js1, shifted] using (readVReg_run 1 js4)
  have hread_rd : rX_bits rd js5.sail = .ok shifted js5.sail := by
    rw [hs5]
    exact rX_after_stateAfterWrite rd shifted js.sail hrd
  obtain ⟨js6, hvsew, hvsew_sail⟩ :=
    jolt_virtual_sign_extend_word_concrete rd js5 shifted hrd hread_rd
  have hw0' : writeVReg 0 (v + sign_extend (m := 64) imm) js = .ok () js0 := by
    simpa [ea] using hw0
  have hw1' : writeVReg 1 (ea &&& (-8 : BitVec 64)) js0 = .ok () js1 := by
    simpa [daddr] using hw1
  refine ⟨js6, ?_, ?_⟩
  · simp only [jolt_lw, liftSail, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
    rw [hrx]
    simp only [bind, pure, EStateM.pure, EStateM.run]
    rw [if_neg (by simpa [ea] using halign)]
    simp only [EStateM.bind]
    rw [hw0']
    simp only [EStateM.bind, EStateM.pure]
    rw [hread_v0]
    simp only [EStateM.bind, EStateM.pure]
    rw [hw1']
    simp only [EStateM.bind, EStateM.pure]
    rw [hld]
    simp only [RETIRE_SUCCESS]
    simp only [EStateM.bind, hslli, EStateM.pure]
    simp only [EStateM.bind, hsrl, EStateM.pure]
    simp only [EStateM.bind, hread_v1, EStateM.pure]
    simp only [EStateM.bind, hwrite, EStateM.pure]
    cases hlast : jolt_virtual_sign_extend_word rd js5 with
    | ok a s =>
        have : s = js6 := by simpa [EStateM.run, hlast] using hvsew
        subst this
        simp [hlast]
    | error e s =>
        have : False := by simpa [EStateM.run, hlast] using hvsew
        exact False.elim this
  · rw [hvsew_sail, hs5, stateAfterWrite_stateAfterWrite]
    congr 1
    simpa [ea, daddr, dword, shift, shifted] using (jolt_lw_bridge js.sail ea halign)

-- ============================================================================
-- Main theorem: Jolt LW = Sail LW
-- ============================================================================

theorem jolt_lw_eq_sail (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) (hcfg : JoltConfig js.sail)
    (h_word_aligned : ∀ v : BitVec 64, (v + sign_extend (m := 64) imm) &&& 3 = 0)
    -- Dword load pipeline (LHS, width 8)
    (h_dw_access : ∀ v : BitVec 64, AlignedDwordAccess (aligned_dword_addr v imm))
    (h_dw_trans  : ∀ v : BitVec 64, BareTranslation (aligned_dword_addr v imm) js.sail)
    (h_dw_phys   : ∀ v : BitVec 64, FlatPhysMem (aligned_dword_addr v imm) 8 js.sail)
    -- Word load pipeline (RHS, width 4)
    (h_word_access : ∀ v : BitVec 64, AlignedAccess (v + sign_extend (m := 64) imm) 4)
    (h_word_trans  : ∀ v : BitVec 64, BareTranslation (v + sign_extend (m := 64) imm) js.sail)
    (h_word_phys   : ∀ v : BitVec 64, FlatPhysMem (v + sign_extend (m := 64) imm) 4 js.sail)
    (h_word_no_ovf : ∀ v : BitVec 64, (v + sign_extend (m := 64) imm).toNat + 3 < 2 ^ 64) :
    projectResult ((jolt_lw imm rs1 rd).run js) =
    (execute_LOAD imm rs1 rd false 4).run js.sail := by
  obtain ⟨v, hrx⟩ := hwf rs1
  have dwa := h_dw_access v
  have dwt := h_dw_trans v
  have dwp := h_dw_phys v
  have hwa0 := h_word_aligned v
  have wa := h_word_access v
  have wt := h_word_trans v
  have wp := h_word_phys v
  have hno := h_word_no_ovf v
  obtain ⟨js', hjolt, hjolt_sail⟩ :=
    jolt_lw_concrete imm rs1 rd hrd js hwf hcfg v hrx hwa0 dwa dwt dwp
  have hsail := execute_LW_reduces imm rs1 rd js hwf hcfg v hrx wa wt wp hno
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail, hsail]
