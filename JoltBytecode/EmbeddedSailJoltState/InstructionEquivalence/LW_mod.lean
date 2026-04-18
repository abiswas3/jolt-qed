import JoltBytecode.EmbeddedSailJoltState.Defs
import JoltBytecode.EmbeddedSailJoltState.MemoryUtils
import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadDefUtils
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

namespace LW_mod

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
    pure (ExecutionResult.Memory_Exception
      (Virtaddr ea, ExceptionType.E_Load_Addr_Align ()))
  else do
    writeVReg 0 ea
    let v0 ← readVReg 0
    writeVReg 1 (v0 &&& (-8 : BitVec 64))
    match ← vreg_LD 1 1 0 with
    | .Retire_Success () =>
        let _ ← vreg_SLLI 0 0 3
        let _ ← vreg_SRL 1 1 0
        let v1 ← readVReg 1
        liftSail (wX_bits rd v1)
        jolt_virtual_sign_extend_word rd
        pure RETIRE_SUCCESS
    | other => pure other

def word_of_dword (d : BitVec 64) (k : Nat) : BitVec 32 :=
  (d >>> (8 * k)).setWidth 32

def byte_of_dword (d : BitVec 64) (k : Nat) : BitVec 8 :=
  (d >>> (8 * k)).setWidth 8

abbrev lw_effective_address (val : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  val + sign_extend (m := 64) imm

abbrev lw_aligned_dword_address (val : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  lw_effective_address val imm &&& (-8 : BitVec 64)

theorem loaded_dword_byte_k (s : SailState) (V : BitVec 64) (k : Nat)
    (hk : k < 8) :
    byte_of_dword (loaded_dword_at s V) k =
    loaded_byte_at s (V + BitVec.ofNat 64 k) := by
  unfold byte_of_dword loaded_dword_at
  interval_cases k <;> bv_decide

theorem word_of_dword_eq_bytes (d : BitVec 64) (k : Nat)
    (hk : k < 5) :
    word_of_dword d k =
    byte_of_dword d (k + 3) ++ byte_of_dword d (k + 2) ++
    byte_of_dword d (k + 1) ++ byte_of_dword d k := by
  unfold word_of_dword byte_of_dword
  interval_cases k <;> bv_decide

theorem loaded_dword_word_k (s : SailState) (V : BitVec 64) (k : Nat)
    (hk : k < 5) :
    ((loaded_dword_at s V) >>> (8 * k)).setWidth 32 =
    loaded_word_at s (V + BitVec.ofNat 64 k) := by
  change word_of_dword (loaded_dword_at s V) k =
    loaded_word_at s (V + BitVec.ofNat 64 k)
  rw [word_of_dword_eq_bytes (loaded_dword_at s V) k hk]
  unfold loaded_word_at
  rw [loaded_dword_byte_k s V (k + 3) (by omega)]
  rw [loaded_dword_byte_k s V (k + 2) (by omega)]
  rw [loaded_dword_byte_k s V (k + 1) (by omega)]
  rw [loaded_dword_byte_k s V k (by omega)]
  have h3 : V + BitVec.ofNat 64 (k + 3) = (3 : BitVec 64) + (V + BitVec.ofNat 64 k) := by
    interval_cases k <;> bv_decide
  have h2 : V + BitVec.ofNat 64 (k + 2) = (2 : BitVec 64) + (V + BitVec.ofNat 64 k) := by
    interval_cases k <;> bv_decide
  have h1 : V + BitVec.ofNat 64 (k + 1) = (1 : BitVec 64) + (V + BitVec.ofNat 64 k) := by
    interval_cases k <;> bv_decide
  rw [h3, h2, h1]
  have h3' : (3 : BitVec 64) + (V + BitVec.ofNat 64 k) = V + BitVec.ofNat 64 k + 3 := by
    interval_cases k <;> bv_decide
  have h2' : (2 : BitVec 64) + (V + BitVec.ofNat 64 k) = V + BitVec.ofNat 64 k + 2 := by
    interval_cases k <;> bv_decide
  have h1' : (1 : BitVec 64) + (V + BitVec.ofNat 64 k) = V + BitVec.ofNat 64 k + 1 := by
    interval_cases k <;> bv_decide
  rw [h3', h2', h1']

theorem addr_split_aligned_offset (addr : BitVec 64) :
    (addr &&& (-8 : BitVec 64)) + BitVec.ofNat 64 (addr &&& 7).toNat = addr := by
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  bv_decide

theorem access_misaligned_4_aligned_false (addr : BitVec 64)
    (halign : addr &&& 3 = 0) :
    access_causes_misaligned_exception (Virtaddr addr) 4 false = false := by
  unfold access_causes_misaligned_exception is_aligned_vaddr Sail.BitVec.toNatInt
  have h_mod : addr.toNat % 4 = 0 := by
    have h := congrArg BitVec.toNat halign
    rw [BitVec.toNat_and] at h
    have h3 : (3 : BitVec 64).toNat = 3 := by decide
    have h0 : (0 : BitVec 64).toNat = 0 := by decide
    rw [h3, h0,
        show (3 : Nat) = 2^2 - 1 from by norm_num,
        Nat.and_two_pow_sub_one_eq_mod] at h
    exact h
  simp [Int.tmod, h_mod, LeanRV64D.Functions.not]

theorem split_misaligned_aligned_4 (addr : BitVec 64)
    (halign : addr &&& 3 = 0) :
    split_misaligned (Virtaddr addr) 4 = (pure (1, 4) : SailM (Int × Int)) := by
  funext s
  unfold split_misaligned is_aligned_vaddr Sail.BitVec.toNatInt
  have h_mod : addr.toNat % 4 = 0 := by
    have h := congrArg BitVec.toNat halign
    rw [BitVec.toNat_and] at h
    have h3 : (3 : BitVec 64).toNat = 3 := by decide
    have h0 : (0 : BitVec 64).toNat = 0 := by decide
    rw [h3, h0,
        show (3 : Nat) = 2^2 - 1 from by norm_num,
        Nat.and_two_pow_sub_one_eq_mod] at h
    exact h
  simp [Int.tmod, h_mod, pure, EStateM.pure]

theorem addr_and_seven_lt_eight (addr : BitVec 64) : (addr &&& 7).toNat < 8 := by
  rw [BitVec.toNat_and]
  exact Nat.and_lt_two_pow addr.toNat (by decide : (7 : BitVec 64).toNat < 2^3)

theorem addr_and_seven_word_lt_five (addr : BitVec 64)
    (halign : addr &&& 3 = 0) :
    (addr &&& 7).toNat < 5 := by
  have hk_mod8 : (addr &&& 7).toNat = addr.toNat % 8 := by
    rw [BitVec.toNat_and]
    have h7 : BitVec.toNat (7 : BitVec 64) = 7 := by decide
    rw [h7]
    rw [show (7 : Nat) = 2^3 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  have h_word_addr : addr.toNat % 4 = 0 := by
    have h := congrArg BitVec.toNat halign
    rw [BitVec.toNat_and] at h
    have h3 : BitVec.toNat (3 : BitVec 64) = 3 := by decide
    have h0 : BitVec.toNat (0 : BitVec 64) = 0 := by decide
    rw [h3, h0] at h
    rw [show (3 : Nat) = 2^2 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod] at h
    exact h
  have hk_mod4 : (addr &&& 7).toNat % 4 = 0 := by
    rw [hk_mod8]
    omega
  have hk_lt : (addr &&& 7).toNat < 8 := addr_and_seven_lt_eight addr
  omega

theorem word_offset_cases (addr : BitVec 64) (halign : addr &&& 3 = 0) :
    (addr &&& 7).toNat = 0 ∨ (addr &&& 7).toNat = 4 := by
  have hk_lt : (addr &&& 7).toNat < 5 := addr_and_seven_word_lt_five addr halign
  have hk_mod4 : (addr &&& 7).toNat % 4 = 0 := by
    have hk_mod8 : (addr &&& 7).toNat = addr.toNat % 8 := by
      rw [BitVec.toNat_and]
      have h7 : BitVec.toNat (7 : BitVec 64) = 7 := by decide
      rw [h7]
      rw [show (7 : Nat) = 2^3 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
    have h_word_addr : addr.toNat % 4 = 0 := by
      have h := congrArg BitVec.toNat halign
      rw [BitVec.toNat_and] at h
      have h3 : BitVec.toNat (3 : BitVec 64) = 3 := by decide
      have h0 : BitVec.toNat (0 : BitVec 64) = 0 := by decide
      rw [h3, h0] at h
      rw [show (3 : Nat) = 2^2 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod] at h
      exact h
    rw [hk_mod8]
    omega
  omega

theorem loaded_word_in_dword (s : SailState) (addr : BitVec 64)
    (halign : addr &&& 3 = 0) :
    loaded_word_at s addr =
    word_of_dword
      (loaded_dword_at s (addr &&& (-8 : BitVec 64)))
      (addr &&& 7).toNat := by
  unfold word_of_dword
  rw [loaded_dword_word_k s (addr &&& -8) (addr &&& 7).toNat
        (addr_and_seven_word_lt_five addr halign)]
  rw [addr_split_aligned_offset]

theorem srl_sign_extend_word_extracts_word (d : BitVec 64) (addr : BitVec 64)
    (halign : addr &&& 3 = 0) :
    (let shifted := shift_bits_right d (Sail.BitVec.extractLsb (shift_bits_left addr (3 : BitVec 6)) 5 0)
     sign_extend (m := 64) ((Sail.BitVec.extractLsb shifted 31 0) : BitVec 32))
    = sign_extend (m := 64) (word_of_dword d (addr &&& 7).toNat) := by
  rcases word_offset_cases addr halign with hk | hk
  · rw [hk]
    unfold shift_bits_left shift_bits_right sign_extend word_of_dword
      Sail.BitVec.signExtend Sail.BitVec.extractLsb
    have hk_eq : addr &&& 7 = BitVec.ofNat 64 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]
      omega
    bv_decide
  · rw [hk]
    unfold shift_bits_left shift_bits_right sign_extend word_of_dword
      Sail.BitVec.signExtend Sail.BitVec.extractLsb
    have hk_eq : addr &&& 7 = BitVec.ofNat 64 4 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]
      omega
    bv_decide

theorem jolt_lw_bridge (s : SailState) (addr : BitVec 64)
    (halign : addr &&& 3 = 0) :
    (let dword := loaded_dword_at s (addr &&& (-8 : BitVec 64))
     let shift := Sail.BitVec.extractLsb (shift_bits_left addr (3 : BitVec 6)) 5 0
     let shifted := shift_bits_right dword shift
     sign_extend (m := 64) ((Sail.BitVec.extractLsb shifted 31 0) : BitVec 32))
    = sign_extend (m := 64) (loaded_word_at s addr) := by
  simp only [srl_sign_extend_word_extracts_word _ _ halign, ← loaded_word_in_dword _ _ halign]

structure LWDwordReadAssumptions (val : BitVec 64) (imm : BitVec 12) (s : SailState) : Prop where
  translate : BareTranslation (aligned_dword_addr val imm) s
  phys : FlatPhysMem (aligned_dword_addr val imm) 8 s

theorem aligned_dword_addr_aligns (val : BitVec 64) (imm : BitVec 12) :
    aligned_dword_addr val imm &&& 7 = 0 := by
  rw [aligned_dword_addr_eq]
  bv_decide

theorem aligned_addr_no_ovf_of_align (addr : BitVec 64)
    (halign : addr &&& 7 = 0) :
    addr.toNat + 7 < 2 ^ 64 := by
  have h_mod : addr.toNat % 8 = 0 := by
    have h := congrArg BitVec.toNat halign
    rw [BitVec.toNat_and] at h
    have h7 : BitVec.toNat (7 : BitVec 64) = 7 := by decide
    have h0 : BitVec.toNat (0 : BitVec 64) = 0 := by decide
    rw [h7, h0] at h
    rw [show (7 : Nat) = 2^3 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod] at h
    exact h
  have hlt : addr.toNat < 2 ^ 64 := addr.isLt
  omega

theorem aligned_dword_addr_no_ovf (val : BitVec 64) (imm : BitVec 12) :
    (aligned_dword_addr val imm).toNat + 7 < 2 ^ 64 := by
  exact aligned_addr_no_ovf_of_align _ (aligned_dword_addr_aligns val imm)

theorem aligned_dword_addr_is_aligned_dword_access (val : BitVec 64) (imm : BitVec 12) :
    AlignedDwordAccess (aligned_dword_addr val imm) := by
  refine
    { misalign := access_misaligned_8_aligned_false _ (aligned_dword_addr_aligns val imm)
      split := split_misaligned_aligned_8 _ (aligned_dword_addr_aligns val imm)
      align := aligned_dword_addr_aligns val imm
      no_ovf := aligned_dword_addr_no_ovf val imm }

theorem lw_dword_load_assumptions_of_local
    (val : BitVec 64) (imm : BitVec 12) (s : SailState)
    (h : LWDwordReadAssumptions val imm s) :
    DwordLoadAssumptions (aligned_dword_addr val imm) s := by
  refine
    { aligned := aligned_dword_addr_is_aligned_dword_access val imm
      translate := h.translate
      phys := h.phys }


-- It is saying if ea = v + sext(imm); then ea & -8 satisfies LWDword assumptions as long as 
-- ea & -8 also is bare-translatable, and FlatPhysmen?
theorem lw_dword_read_assumptions_of_addr
    (val : BitVec 64) 
    (imm : BitVec 12) 
    (s : SailState)
    (htranslate : BareTranslation (lw_aligned_dword_address val imm) s)
    (hphys : FlatPhysMem (lw_aligned_dword_address val imm) 8 s) :
    LWDwordReadAssumptions val imm s := by
  have haddr : aligned_dword_addr val imm = lw_aligned_dword_address val imm := by
    simp [lw_aligned_dword_address, lw_effective_address, aligned_dword_addr_eq]
  refine
    { translate := ?_
      phys := ?_ }
  · simpa [haddr] using htranslate
  · simpa [haddr] using hphys

-- WARNING: Axiom assumption alert
axiom execute_LW_misaligned (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (htranslate : BareTranslation (lw_effective_address val imm) js.sail)
    (hphys : FlatPhysMem (lw_effective_address val imm) 4 js.sail)
    (h_no_ovf : (lw_effective_address val imm).toNat + 3 < 2 ^ 64)
    (h_align : lw_effective_address val imm &&& 3 ≠ 0)
    :
    (execute_LOAD imm rs1 rd false 4).run js.sail =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (lw_effective_address val imm), ExceptionType.E_Load_Addr_Align ())) js.sail

theorem execute_LW_reduces (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (hload : LoadReadAssumptions (lw_effective_address val imm) 4 js.sail)
    (h_no_ovf : (lw_effective_address val imm).toNat + 3 < 2 ^ 64) :
    (execute_LOAD imm rs1 rd false 4).run js.sail =
    .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (loaded_word_at js.sail (lw_effective_address val imm)))) := by
  unfold execute_LOAD
  simp only [bind, pure]
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  simp (config := { decide := true }) only []
  simp (config := { decide := true }) only [PreSail.assert, EStateM.bind, pure, EStateM.pure,
       EStateM.run, if_true]
  rw [vmem_read_word_reduces imm rs1 js.sail val hrx hload.aligned hload.translate
      (mem_read_4_eq_loaded_word _ js.sail hcfg h_no_ovf hload.phys)]
  simp only [extend_value, Bool.false_eq_true, if_false, EStateM.bind, EStateM.pure]
  obtain ⟨s', hw⟩ := wX_shape rd
    (sign_extend (m := 64) (loaded_word_at js.sail (lw_effective_address val imm)))
    js.sail
  rw [hw]
  simp only [RETIRE_SUCCESS]
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

theorem jolt_lw_concrete (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (halign : lw_effective_address val imm &&& 3 = 0)
    (h_dword_translate : BareTranslation (lw_aligned_dword_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (lw_aligned_dword_address val imm) 8 js.sail) :
    ∃ js' : SailJoltState,
      (jolt_lw imm rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (loaded_word_at js.sail (lw_effective_address val imm))) := by
  let ea := lw_effective_address val imm
  let daddr := lw_aligned_dword_address val imm
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
  have h_daddr_aligned : AlignedDwordAccess daddr := by
    simpa [daddr, lw_aligned_dword_address, ea, lw_effective_address, aligned_dword_addr_eq] using
      (aligned_dword_addr_is_aligned_dword_access val imm)
  have hdw' : DwordLoadAssumptions daddr js.sail := by
    refine
      { aligned := h_daddr_aligned
        translate := ?_
        phys := ?_ }
    · simpa [daddr, lw_aligned_dword_address, ea, lw_effective_address] using h_dword_translate
    · simpa [daddr, lw_aligned_dword_address, ea, lw_effective_address] using h_dword_phys
  have hld : vreg_LD 1 1 0 js1 = .ok RETIRE_SUCCESS js2 := by
    have hvs1 : js1.vregs 1 = daddr := by simp [js1, daddr]
    simp [js2, dword] at *
    exact vreg_LD_run_of_dword_assumptions 1 1 js1 daddr hvs1 hcfg hdw'
  have hslli : vreg_SLLI 0 0 3 js2 = .ok RETIRE_SUCCESS js3 := by
    change vreg_SLLI 0 0 3 js2 = .ok RETIRE_SUCCESS
      { sail := js2.sail
        vregs := fun r => if r = 0 then shift_bits_left (js2.vregs 0) (3 : BitVec 6) else js2.vregs r }
    simpa [js2] using (vreg_SLLI_run 0 0 3 js2)
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
  refine ⟨js6, ?_, ?_⟩
  · simp only [jolt_lw, liftSail, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
    rw [hrx]
    simp only [bind, pure, EStateM.pure, EStateM.run]
    rw [if_neg (by simpa [ea] using halign)]
    simp only [EStateM.bind]
    rw [hw0]
    simp only [EStateM.bind, EStateM.pure]
    rw [hread_v0]
    simp only [EStateM.bind, EStateM.pure]
    rw [hw1]
    simp only [EStateM.bind, EStateM.pure]
    rw [hld]
    simp only [RETIRE_SUCCESS]
    simp only [EStateM.bind, hslli, EStateM.pure]
    simp only [EStateM.bind, hsrl, EStateM.pure]
    simp only [EStateM.bind, hread_v1, EStateM.pure]
    simp only [EStateM.bind, hwrite, EStateM.pure]
    cases hlast : jolt_virtual_sign_extend_word rd js5 with
    | ok a s =>
        have hs : s = js6 := by
          simp [EStateM.run, hlast] at hvsew
          exact hvsew
        subst hs
        simp
    | error e s =>
        have : False := by
          simp [EStateM.run, hlast] at hvsew
        exact False.elim this
  · rw [hvsew_sail, hs5, stateAfterWrite_stateAfterWrite]
    congr 1
    simpa [ea, daddr, dword, shift, shifted] using (jolt_lw_bridge js.sail ea halign)

theorem jolt_lw_concrete_misaligned (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_align : lw_effective_address val imm &&& 3 ≠ 0)
    :
    (jolt_lw imm rs1 rd).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (lw_effective_address val imm), ExceptionType.E_Load_Addr_Align ())) js := by
  unfold jolt_lw
  simp only [liftSail, bind, EStateM.bind, pure,  EStateM.run]
  rw [hrx]
  simp only []
  rw [if_pos h_align]
  rfl

theorem jolt_lw_eq_sail_aligned (imm : BitVec 12)
    (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_dword_translate : BareTranslation (lw_aligned_dword_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (lw_aligned_dword_address val imm) 8 js.sail)
    (htranslate : BareTranslation (lw_effective_address val imm) js.sail)
    (hphys : FlatPhysMem (lw_effective_address val imm) 4 js.sail)
    (h_word_no_ovf : (lw_effective_address val imm).toNat + 3 < 2 ^ 64)
    (h_align : lw_effective_address val imm &&& 3 = 0)
    :
    projectResult ((jolt_lw imm rs1 rd).run js) =
    (execute_LOAD imm rs1 rd false 4).run js.sail := by
  let ea := lw_effective_address val imm
  have hload : LoadReadAssumptions (lw_effective_address val imm) 4 js.sail := by
    refine
      { aligned := ?_
        translate := htranslate
        phys := hphys }
    refine
      { misalign := ?_
        split := ?_ }
    · simpa [ea] using access_misaligned_4_aligned_false ea h_align
    · simpa [ea] using split_misaligned_aligned_4 ea h_align
  have hjolt_aligned := jolt_lw_concrete imm rs1 rd hrd js hcfg val hrx h_align h_dword_translate h_dword_phys
  have hsail_aligned := execute_LW_reduces imm rs1 rd js hcfg val hrx hload h_word_no_ovf
  rcases hjolt_aligned with ⟨js', hjolt, hjolt_sail⟩
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail, hsail_aligned]

theorem jolt_lw_eq_sail_misaligned (imm : BitVec 12)
    (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_dword_translate : BareTranslation (lw_aligned_dword_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (lw_aligned_dword_address val imm) 8 js.sail)
    (htranslate : BareTranslation (lw_effective_address val imm) js.sail)
    (hphys : FlatPhysMem (lw_effective_address val imm) 4 js.sail)
    (h_word_no_ovf : (lw_effective_address val imm).toNat + 3 < 2 ^ 64)
    (h_align : lw_effective_address val imm &&& 3 ≠ 0)
    :
    projectResult ((jolt_lw imm rs1 rd).run js) =
    (execute_LOAD imm rs1 rd false 4).run js.sail := by
  let ea := lw_effective_address val imm
  
  -- Jolt immediately takes the misaligned-address error branch.
  have hjolt_misaligned :
      (jolt_lw imm rs1 rd).run js =
        .ok (ExecutionResult.Memory_Exception (Virtaddr ea, ExceptionType.E_Load_Addr_Align ())) js := by
    simpa [ea] using
      (jolt_lw_concrete_misaligned imm rs1 rd hrd js hcfg val hrx h_align)
    
  -- Sail's execute_LOAD returns the same misaligned-address exception.
  -- WARNING: For now this axiomatised.
  have hsail_misaligned :
      (execute_LOAD imm rs1 rd false 4).run js.sail =
        .ok (ExecutionResult.Memory_Exception (Virtaddr ea, ExceptionType.E_Load_Addr_Align ())) js.sail := by
    -- This is the key-lemma that reduces the SAIL side
    simpa [ea] using
      (execute_LW_misaligned imm rs1 rd js hcfg val hrx htranslate hphys h_word_no_ovf h_align)

  -- The rest is just mechanical rewriting.
  rw [hjolt_misaligned]
  simp only [projectResult, project]
  symm
  exact hsail_misaligned

theorem jolt_lw_eq_sail (imm : BitVec 12) 
    (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_dword_translate : BareTranslation (lw_aligned_dword_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (lw_aligned_dword_address val imm) 8 js.sail)
    (htranslate : BareTranslation (lw_effective_address val imm) js.sail)
    (hphys : FlatPhysMem (lw_effective_address val imm) 4 js.sail)
    (h_word_no_ovf : (lw_effective_address val imm).toNat + 3 < 2 ^ 64)  -- TODO: check where this is needed (i should be able to prove this with have) 
    :
    projectResult ((jolt_lw imm rs1 rd).run js) =
    (execute_LOAD imm rs1 rd false 4).run js.sail := by
  let ea := lw_effective_address val imm
  by_cases h_align : ea &&& 3 = 0
  · exact jolt_lw_eq_sail_aligned imm rs1 rd hrd js hcfg val hrx h_dword_translate h_dword_phys htranslate hphys h_word_no_ovf h_align
  · exact jolt_lw_eq_sail_misaligned imm rs1 rd hrd js hcfg val hrx h_dword_translate h_dword_phys htranslate hphys h_word_no_ovf h_align

end LW_mod
