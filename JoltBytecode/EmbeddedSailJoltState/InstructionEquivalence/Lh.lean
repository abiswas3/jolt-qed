import JoltBytecode.EmbeddedSailJoltState.MemoryUtils
import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
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

/-!
# LH: Jolt load-halfword (signed) decomposition

From `tracer/src/instruction/lh.rs::inline_sequence_64`:

    VirtualAssertHalfwordAlignment rs1, imm
    ADDI  v0, rs1, imm
    ANDI  v1, v0, -8
    LD    v1, v1, 0
    XORI  v0, v0, 6
    SLLI  v0, v0, 3
    SLL   v1, v1, v0
    SRAI  rd, v1, 48
-/

def jolt_lh (imm : BitVec 12) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let base ← liftSail (rX_bits rs1)
  let ea := base + sign_extend (m := 64) imm
  if ea &&& 1 ≠ 0 then
    throw (Error.Assertion "LH: effective address not halfword-aligned")
  else do
    writeVReg 0 ea
    let _ ← vreg_ANDI 1 0 (-8 : BitVec 12)
    match ← vreg_LD 1 1 0 with
    | .Retire_Success () =>
        let _ ← vreg_XORI 0 0 6
        let _ ← vreg_SLLI 0 0 3
        let _ ← vreg_SLL 1 1 0
        let v1 ← readVReg 1
        liftSail (wX_bits rd (shift_bits_right_arith v1 (48 : BitVec 6)))
        pure RETIRE_SUCCESS
    | other => pure other

private abbrev lh_dword_addr (v : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  (v + sign_extend (m := 64) imm &&& sign_extend (m := 64) (-8 : BitVec 12))
    + sign_extend (m := 64) (0 : BitVec 12)

def halfword_of_dword (d : BitVec 64) (k : Nat) : BitVec 16 :=
  (d >>> (8 * k)).setWidth 16

theorem loaded_halfword_in_dword (s : SailState) (addr : BitVec 64)
    (halign : addr &&& 1 = 0) :
    loaded_halfword_at s addr =
    halfword_of_dword
      (loaded_dword_at s (addr &&& (-8 : BitVec 64)))
      (addr &&& 7).toNat := by
  sorry

theorem sll_srai_extracts_halfword (d : BitVec 64) (addr : BitVec 64)
    (halign : addr &&& 1 = 0) :
    (let xor_addr := addr ^^^ (6 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted := shift_bits_left d shift_6
     shift_bits_right_arith shifted (48 : BitVec 6))
    = sign_extend (m := 64) (halfword_of_dword d (addr &&& 7).toNat) := by
  sorry

theorem jolt_lh_bridge (s : SailState) (addr : BitVec 64)
    (halign : addr &&& 1 = 0) :
    (let dword := loaded_dword_at s (addr &&& (-8 : BitVec 64))
     let xor_addr := addr ^^^ (6 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted := shift_bits_left dword shift_6
     shift_bits_right_arith shifted (48 : BitVec 6))
    = sign_extend (m := 64) (loaded_halfword_at s addr) := by
  sorry

theorem jolt_lh_concrete (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) (hcfg : JoltConfig js.sail)
    (v : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok v js.sail)
    (halign : (v + sign_extend (m := 64) imm) &&& 1 = 0)
    (hda : AlignedDwordAccess (lh_dword_addr v imm))
    (hdt : BareTranslation (lh_dword_addr v imm) js.sail)
    (hdf : FlatPhysMem (lh_dword_addr v imm) 8 js.sail) :
    ∃ js' : SailJoltState,
      (jolt_lh imm rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (loaded_halfword_at js.sail (v + sign_extend (m := 64) imm))) := by
  let ea := v + sign_extend (m := 64) imm
  let daddr := ea &&& (-8 : BitVec 64)
  let dword := loaded_dword_at js.sail daddr
  let xor_addr := ea ^^^ (6 : BitVec 64)
  let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
  let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
  let shifted := shift_bits_left dword shift_6
  let out := shift_bits_right_arith shifted (48 : BitVec 6)
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
      vregs := fun r => if r = 0 then xor_addr else js2.vregs r }
  let js4 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = 0 then shift_amt else js3.vregs r }
  let js5 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = 1 then shifted else js4.vregs r }
  have hw0 : writeVReg 0 ea js = .ok () js0 := by
    unfold writeVReg js0 ea
    simp [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  have h_addr_sum : (v + sign_extend (m := 64) imm &&& sign_extend (m := 64) (-8 : BitVec 12))
                      + sign_extend (m := 64) (0 : BitVec 12) =
                    daddr := by
    unfold daddr ea
    have h0 : sign_extend (m := 64) (0 : BitVec 12) = (0 : BitVec 64) := by decide
    have h8 : sign_extend (m := 64) (-8 : BitVec 12) = (-8 : BitVec 64) := by decide
    rw [h0, h8]
    bv_decide
  have h_lh_addr : lh_dword_addr v imm = daddr := by
    unfold lh_dword_addr
    exact h_addr_sum
  have hda' : AlignedDwordAccess daddr := by
    simpa [h_lh_addr] using hda
  have hdt' : BareTranslation daddr js.sail := by
    simpa [h_lh_addr] using hdt
  have hdf' : FlatPhysMem daddr 8 js.sail := by
    simpa [h_lh_addr] using hdf
  have hw1 : vreg_ANDI 1 0 (-8 : BitVec 12) js0 = .ok RETIRE_SUCCESS js1 := by
    have h8 : sign_extend (m := 64) (-8 : BitVec 12) = (-8 : BitVec 64) := by decide
    change vreg_ANDI 1 0 (-8 : BitVec 12) js0 = .ok RETIRE_SUCCESS
      { sail := js0.sail
        vregs := fun r => if r = 1 then js0.vregs 0 &&& sign_extend (m := 64) (-8 : BitVec 12) else js0.vregs r }
    simpa [js0, js1, daddr, ea, h8] using (vreg_ANDI_run 1 0 (-8 : BitVec 12) js0)
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
  have hxori : vreg_XORI 0 0 6 js2 = .ok RETIRE_SUCCESS js3 := by
    have h6 : sign_extend (m := 64) (6 : BitVec 12) = (6 : BitVec 64) := by decide
    change vreg_XORI 0 0 (6 : BitVec 12) js2 = .ok RETIRE_SUCCESS
      { sail := js2.sail
        vregs := fun r => if r = 0 then js2.vregs 0 ^^^ sign_extend (m := 64) (6 : BitVec 12) else js2.vregs r }
    simpa [js2, js3, xor_addr, ea, h6] using (vreg_XORI_run 0 0 (6 : BitVec 12) js2)
  have hslli : vreg_SLLI 0 0 3 js3 = .ok RETIRE_SUCCESS js4 := by
    change vreg_SLLI 0 0 3 js3 = .ok RETIRE_SUCCESS
      { sail := js3.sail
        vregs := fun r => if r = 0 then shift_bits_left (js3.vregs 0) (3 : BitVec 6) else js3.vregs r }
    simpa [js3, js4, shift_amt, xor_addr] using (vreg_SLLI_run 0 0 3 js3)
  have hsll : vreg_SLL 1 1 0 js4 = .ok RETIRE_SUCCESS js5 := by
    change vreg_SLL 1 1 0 js4 = .ok RETIRE_SUCCESS
      { sail := js4.sail
        vregs := fun r =>
          if r = 1 then shift_bits_left (js4.vregs 1) (Sail.BitVec.extractLsb (js4.vregs 0) 5 0)
          else js4.vregs r }
    simpa [js4, js5, shifted, dword, shift_6] using (vreg_SLL_run 1 1 0 js4)
  have hread_v1 : readVReg 1 js5 = .ok shifted js5 := by
    simpa [js5, js4, js3, js2, js1, shifted] using (readVReg_run 1 js5)
  obtain ⟨s', hw⟩ := wX_shape rd out js.sail
  let js6 : SailJoltState := { sail := s', vregs := js5.vregs }
  have hwrite : liftSail (wX_bits rd out) js5 = .ok () js6 := by
    unfold liftSail js6
    rw [hw]
  have hs6 : js6.sail = stateAfterWrite js.sail rd out := by
    exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw
  refine ⟨js6, ?_, ?_⟩
  · simp only [jolt_lh, liftSail, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
    rw [hrx]
    simp only [bind, pure, EStateM.pure, EStateM.run]
    rw [if_neg (by simpa [ea] using halign)]
    simp only [EStateM.bind]
    rw [hw0]
    simp only [EStateM.bind, EStateM.pure]
    rw [hw1]
    simp only [EStateM.bind, EStateM.pure]
    rw [hld]
    simp only [RETIRE_SUCCESS]
    simp only [EStateM.bind, hxori, EStateM.pure]
    simp only [EStateM.bind, hslli, EStateM.pure]
    simp only [EStateM.bind, hsll, EStateM.pure]
    simp only [EStateM.bind, hread_v1, EStateM.pure]
    rw [hwrite]
  · rw [hs6]
    apply congrArg (stateAfterWrite js.sail rd)
    simpa [ea, daddr, dword, xor_addr, shift_amt, shift_6, shifted, out] using
      (jolt_lh_bridge js.sail ea halign)

theorem execute_LH_reduces (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) (hcfg : JoltConfig js.sail)
    (v : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok v js.sail)
    (hha : AlignedAccess (v + sign_extend (m := 64) imm) 2)
    (hht : BareTranslation (v + sign_extend (m := 64) imm) js.sail)
    (hhp : FlatPhysMem (v + sign_extend (m := 64) imm) 2 js.sail)
    (h_no_ovf : (v + sign_extend (m := 64) imm).toNat + 1 < 2 ^ 64) :
    (execute_LOAD imm rs1 rd false 2).run js.sail =
    .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (loaded_halfword_at js.sail (v + sign_extend (m := 64) imm)))) := by
  unfold execute_LOAD
  simp only [bind, pure]
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  simp (config := { decide := true }) only []
  simp (config := { decide := true }) only [PreSail.assert, EStateM.bind, pure, EStateM.pure,
       EStateM.run, if_true]
  rw [vmem_read_halfword_reduces imm rs1 js.sail v hrx hha hht
      (mem_read_2_eq_loaded_halfword _ js.sail hcfg h_no_ovf hhp)]
  simp only [extend_value, Bool.false_eq_true, if_false, EStateM.bind, EStateM.pure]
  obtain ⟨s', hw⟩ := wX_shape rd
    (sign_extend (m := 64) (loaded_halfword_at js.sail (v + sign_extend (m := 64) imm)))
    js.sail
  rw [hw]
  simp only [RETIRE_SUCCESS]
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

theorem jolt_lh_eq_sail (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) (hcfg : JoltConfig js.sail)
    (h_half_aligned : ∀ v : BitVec 64, (v + sign_extend (m := 64) imm) &&& 1 = 0)
    (h_dw_access : ∀ v : BitVec 64, AlignedDwordAccess (lh_dword_addr v imm))
    (h_dw_trans  : ∀ v : BitVec 64, BareTranslation (lh_dword_addr v imm) js.sail)
    (h_dw_phys   : ∀ v : BitVec 64, FlatPhysMem (lh_dword_addr v imm) 8 js.sail)
    (h_half_access : ∀ v : BitVec 64, AlignedAccess (v + sign_extend (m := 64) imm) 2)
    (h_half_trans  : ∀ v : BitVec 64, BareTranslation (v + sign_extend (m := 64) imm) js.sail)
    (h_half_phys   : ∀ v : BitVec 64, FlatPhysMem (v + sign_extend (m := 64) imm) 2 js.sail)
    (h_half_no_ovf : ∀ v : BitVec 64, (v + sign_extend (m := 64) imm).toNat + 1 < 2 ^ 64) :
    projectResult ((jolt_lh imm rs1 rd).run js) =
    (execute_LOAD imm rs1 rd false 2).run js.sail := by
  obtain ⟨v, hrx⟩ := hwf rs1
  have dwa := h_dw_access v
  have dwt := h_dw_trans v
  have dwp := h_dw_phys v
  have hha0 := h_half_aligned v
  have ha := h_half_access v
  have ht := h_half_trans v
  have hp := h_half_phys v
  have hno := h_half_no_ovf v
  obtain ⟨js', hjolt, hjolt_sail⟩ :=
    jolt_lh_concrete imm rs1 rd hrd js hwf hcfg v hrx hha0 dwa dwt dwp
  have hsail := execute_LH_reduces imm rs1 rd js hwf hcfg v hrx ha ht hp hno
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail, hsail]
