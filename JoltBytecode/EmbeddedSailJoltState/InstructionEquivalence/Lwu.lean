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

/-!
# LWU: Jolt load-word unsigned decomposition

From `tracer/src/instruction/lwu.rs::inline_sequence_64`:

    VirtualAssertWordAlignment rs1, imm
    ADDI  v0, rs1, imm
    ANDI  v1, v0, -8
    LD    v1, v1, 0
    XORI  v0, v0, 4
    SLLI  v0, v0, 3
    SLL   v1, v1, v0
    SRLI  rd, v1, 32
-/

def jolt_lwu (imm : BitVec 12) (rs1 rd : regidx) : JoltMonad ExecutionResult :=
  jolt_word_unsigned_family imm rs1 rd

def word_of_dword (d : BitVec 64) (k : Nat) : BitVec 32 :=
  (d >>> (8 * k)).setWidth 32

def byte_of_dword (d : BitVec 64) (k : Nat) : BitVec 8 :=
  (d >>> (8 * k)).setWidth 8

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

theorem addr_and_seven_lt_eight (addr : BitVec 64) : (addr &&& 7).toNat < 8 := by
  rw [BitVec.toNat_and]
  exact Nat.and_lt_two_pow addr.toNat (by decide : (7 : BitVec 64).toNat < 2^3)

theorem addr_and_seven_word_lt_five (addr : BitVec 64)
    (halign : addr &&& 3 = 0) :
    (addr &&& 7).toNat < 5 := by
  have hk_lt : (addr &&& 7).toNat < 8 := addr_and_seven_lt_eight addr
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

private lemma sll_srli_extracts_word_k0 (d addr : BitVec 64)
    (hk : (addr &&& 7).toNat = 0) :
    (let xor_addr := addr ^^^ (4 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted := shift_bits_left d shift_6
     shift_bits_right shifted (32 : BitVec 6))
    = zero_extend (m := 64) (word_of_dword d 0) := by
  unfold word_of_dword shift_bits_left shift_bits_right zero_extend
    Sail.BitVec.zeroExtend Sail.BitVec.extractLsb
  have hk_eq : addr &&& 7 = BitVec.ofNat 64 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    omega
  bv_decide

private lemma sll_srli_extracts_word_k4 (d addr : BitVec 64)
    (hk : (addr &&& 7).toNat = 4) :
    (let xor_addr := addr ^^^ (4 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted := shift_bits_left d shift_6
     shift_bits_right shifted (32 : BitVec 6))
    = zero_extend (m := 64) (word_of_dword d 4) := by
  unfold word_of_dword shift_bits_left shift_bits_right zero_extend
    Sail.BitVec.zeroExtend Sail.BitVec.extractLsb
  have hk_eq : addr &&& 7 = BitVec.ofNat 64 4 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    omega
  bv_decide

theorem sll_srli_extracts_word (d : BitVec 64) (addr : BitVec 64)
    (halign : addr &&& 3 = 0) :
    (let xor_addr := addr ^^^ (4 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted := shift_bits_left d shift_6
     shift_bits_right shifted (32 : BitVec 6))
    = zero_extend (m := 64) (word_of_dword d (addr &&& 7).toNat) := by
  rcases word_offset_cases addr halign with hk | hk
  · rw [hk]
    simpa using sll_srli_extracts_word_k0 d addr hk
  · rw [hk]
    simpa using sll_srli_extracts_word_k4 d addr hk

theorem jolt_lwu_bridge (s : SailState) (addr : BitVec 64)
    (halign : addr &&& 3 = 0) :
    (let dword := loaded_dword_at s (addr &&& (-8 : BitVec 64))
     let xor_addr := addr ^^^ (4 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted := shift_bits_left dword shift_6
     shift_bits_right shifted (32 : BitVec 6))
    = zero_extend (m := 64) (loaded_word_at s addr) := by
  simp only [sll_srli_extracts_word _ _ halign, ← loaded_word_in_dword _ _ halign]

theorem jolt_lwu_concrete (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) (hcfg : JoltConfig js.sail)
    (v : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok v js.sail)
    (halign : (v + sign_extend (m := 64) imm) &&& 3 = 0)
    (hdw : DwordLoadAssumptions (aligned_dword_addr v imm) js.sail) :
    ∃ js' : SailJoltState,
      (jolt_lwu imm rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (zero_extend (m := 64)
          (loaded_word_at js.sail (v + sign_extend (m := 64) imm))) := by
  let ea := v + sign_extend (m := 64) imm
  let daddr := ea &&& (-8 : BitVec 64)
  let dword := loaded_dword_at js.sail daddr
  let xor_addr := ea ^^^ (4 : BitVec 64)
  let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
  let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
  let shifted := shift_bits_left dword shift_6
  let out := shift_bits_right shifted (32 : BitVec 6)
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
  have h_lwu_addr : aligned_dword_addr v imm = daddr := by
    simp [daddr, ea, aligned_dword_addr_eq]
  have hdw' : DwordLoadAssumptions daddr js.sail :=
    DwordLoadAssumptions.of_eq h_lwu_addr hdw
  have hw1 : vreg_ANDI 1 0 (-8 : BitVec 12) js0 = .ok RETIRE_SUCCESS js1 := by
    have h8 : sign_extend (m := 64) (-8 : BitVec 12) = (-8 : BitVec 64) := by decide
    change vreg_ANDI 1 0 (-8 : BitVec 12) js0 = .ok RETIRE_SUCCESS
      { sail := js0.sail
        vregs := fun r =>
          if r = 1 then js0.vregs 0 &&& sign_extend (m := 64) (-8 : BitVec 12)
          else js0.vregs r }
    simpa [js0, ea, h8] using (vreg_ANDI_run 1 0 (-8 : BitVec 12) js0)
  have hld : vreg_LD 1 1 0 js1 = .ok RETIRE_SUCCESS js2 := by
    have hvs1 : js1.vregs 1 = daddr := by simp [js1, daddr]
    simpa [js2, dword] using
      (vreg_LD_run_of_dword_assumptions 1 1 js1 daddr hvs1 hcfg hdw')
  have hxori : vreg_XORI 0 0 4 js2 = .ok RETIRE_SUCCESS js3 := by
    have h4 : sign_extend (m := 64) (4 : BitVec 12) = (4 : BitVec 64) := by decide
    change vreg_XORI 0 0 (4 : BitVec 12) js2 = .ok RETIRE_SUCCESS
      { sail := js2.sail
        vregs := fun r =>
          if r = 0 then js2.vregs 0 ^^^ sign_extend (m := 64) (4 : BitVec 12)
          else js2.vregs r }
    simpa [js2, js3, xor_addr, ea, h4] using (vreg_XORI_run 0 0 (4 : BitVec 12) js2)
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
  · simp only [jolt_lwu, jolt_word_unsigned_family, liftSail, bind, EStateM.bind,
      pure, EStateM.pure, EStateM.run, hrx]
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
      (jolt_lwu_bridge js.sail ea halign)

theorem execute_LWU_reduces (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) (hcfg : JoltConfig js.sail)
    (v : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok v js.sail)
    (hload : LoadReadAssumptions (v + sign_extend (m := 64) imm) 4 js.sail)
    (h_no_ovf : (v + sign_extend (m := 64) imm).toNat + 3 < 2 ^ 64) :
    (execute_LOAD imm rs1 rd true 4).run js.sail =
    .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd
        (zero_extend (m := 64)
          (loaded_word_at js.sail (v + sign_extend (m := 64) imm)))) := by
  unfold execute_LOAD
  simp only [bind, pure]
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  simp (config := { decide := true }) only []
  simp (config := { decide := true }) only [PreSail.assert, EStateM.bind, pure, EStateM.pure,
       EStateM.run, if_true]
  rw [vmem_read_word_reduces imm rs1 js.sail v hrx hload.aligned hload.translate
      (mem_read_4_eq_loaded_word _ js.sail hcfg h_no_ovf hload.phys)]
  simp only [extend_value, if_true, EStateM.bind, EStateM.pure]
  obtain ⟨s', hw⟩ := wX_shape rd
    (zero_extend (m := 64) (loaded_word_at js.sail (v + sign_extend (m := 64) imm)))
    js.sail
  rw [hw]
  simp only [RETIRE_SUCCESS]
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

theorem jolt_lwu_eq_sail (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) (hcfg : JoltConfig js.sail)
    (h_word_aligned : ∀ v : BitVec 64, (v + sign_extend (m := 64) imm) &&& 3 = 0)
    (h_dw : ∀ v : BitVec 64, DwordLoadAssumptions (aligned_dword_addr v imm) js.sail)
    (h_word : ∀ v : BitVec 64, LoadReadAssumptions (v + sign_extend (m := 64) imm) 4 js.sail)
    (h_word_no_ovf : ∀ v : BitVec 64, (v + sign_extend (m := 64) imm).toNat + 3 < 2 ^ 64) :
    projectResult ((jolt_lwu imm rs1 rd).run js) =
    (execute_LOAD imm rs1 rd true 4).run js.sail := by
  obtain ⟨v, hrx⟩ := hwf rs1
  have hwa0 := h_word_aligned v
  have hno := h_word_no_ovf v
  obtain ⟨js', hjolt, hjolt_sail⟩ :=
    jolt_lwu_concrete imm rs1 rd hrd js hwf hcfg v hrx hwa0 (h_dw v)
  have hsail := execute_LWU_reduces imm rs1 rd js hwf hcfg v hrx (h_word v) hno
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail, hsail]
