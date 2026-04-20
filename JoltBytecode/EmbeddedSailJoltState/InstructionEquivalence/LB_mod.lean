import JoltBytecode.EmbeddedSailJoltState.Defs
import JoltBytecode.EmbeddedSailJoltState.MemoryUtils
import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadDefUtils
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LD_helpers
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Load_Write_helpers
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

namespace LB_mod

/-!
# LB: Jolt load-byte (signed) decomposition

From `tracer/src/instruction/lb.rs::inline_sequence_64`:

    ADDI  v0, rs1, imm         -- real rs1 → virtual v0
    ANDI  v1, v0, -8           -- virtual → virtual
    LD    v1, v1, 0            -- virtual → virtual (memory load)
    XORI  v0, v0, 7            -- virtual → virtual
    SLLI  v0, v0, 3            -- virtual → virtual
    SLL   v1, v1, v0           -- virtual → virtual
    SRAI  rd, v1, 56           -- virtual v1 → real rd (arith-shift + sign-extend)
-/

def jolt_lb (imm : BitVec 12) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let rs1_val ← liftSail (rX_bits rs1)
  -- Load phase begins
  writeVReg 0 (rs1_val + sign_extend (m := 64) imm)   -- v0 = ea
  let _ ← vreg_ANDI 1 0 (-8 : BitVec 12)              -- v1 = ea &&& -8 (d_addr)
  match ← vreg_LD 1 1 0 with                           -- v1 = loaded double word
  -- Load phase ends
  | .Retire_Success () =>
      -- Logic phase begins
      let _ ← vreg_XORI 0 0 7                          -- v0 = ea XOR 7
      let _ ← vreg_SLLI 0 0 3                          -- v0 = (ea XOR 7) << 3
      let _ ← vreg_SLL 1 1 0                           -- v1 = dword << v0  (target byte now at top)
      -- Logic phase ends with the shifted dword in v1; sign-extended byte still to come
      let v1 ← readVReg 1
      liftSail (wX_bits rd (shift_bits_right_arith v1 (56 : BitVec 6)))
      -- SRAI by 56 pulls the top byte down to the low 8 bits and replicates
      -- the sign bit into the upper 56 bits.
      pure RETIRE_SUCCESS
  | other => pure other

-- NEXT: This should be moved to common
def jolt_lb_load_phase (ea : BitVec 64) : JoltMonad ExecutionResult := do
  writeVReg 0 ea
  let _ ← vreg_ANDI 1 0 (-8 : BitVec 12)
  vreg_LD 1 1 0

def jolt_lb_logic_phase : JoltMonad (BitVec 64) := do
  let _ ← vreg_XORI 0 0 7
  let _ ← vreg_SLLI 0 0 3
  let _ ← vreg_SLL 1 1 0
  readVReg 1

def jolt_lb_write_phase (rd : regidx) (v1 : BitVec 64) : JoltMonad ExecutionResult := do
  liftSail (wX_bits rd (shift_bits_right_arith v1 (56 : BitVec 6)))
  pure RETIRE_SUCCESS

def jolt_lb_decomposed (imm : BitVec 12) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let base ← liftSail (rX_bits rs1)
  let ea := base + sign_extend (m := 64) imm
  match ← jolt_lb_load_phase ea with
  | .Retire_Success () =>
      let v1 ← jolt_lb_logic_phase
      jolt_lb_write_phase rd v1
  | other => pure other

-- `jolt_lb` is just `jolt_lb_decomposed` with the phase calls inlined.
-- No alignment hypothesis is required: byte loads have no alignment check.
theorem jolt_lb_run_eq_decomposed (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState) (val : BitVec 64)
    (hrx : rX_bits rs1 js.sail = .ok val js.sail) :
    (jolt_lb imm rs1 rd).run js = (jolt_lb_decomposed imm rs1 rd).run js := by
  unfold jolt_lb jolt_lb_decomposed
  simp only [liftSail, bind, EStateM.bind, pure, EStateM.run]
  rw [hrx]
  rfl

-- Used by: `jolt_lb_logic_phase_concrete`.
-- Pure value-level identity: rewrites the symbolic vreg reads using the load
-- phase's postconditions, and bridges `sign_extend (m := 64) (7 : BitVec 12)`
-- to `(7 : BitVec 64)`.
theorem jolt_lb_logic_phase_value (imm : BitVec 12) (js : SailJoltState)
    (js_load : SailJoltState) (val : BitVec 64)
    (hload_v0 : js_load.vregs 0 = load_effective_address val imm)
    (hload_v1 : js_load.vregs 1 = loaded_dword_at js.sail (compute_aligned_dword_base_address val imm)) :
    shift_bits_left
      (js_load.vregs 1)
      (Sail.BitVec.extractLsb
        (shift_bits_left
          ((js_load.vregs 0) ^^^ (sign_extend (m := 64) (7 : BitVec 12)))
          (3 : BitVec 6)) 5 0) =
    shift_bits_left
      (loaded_dword_at js.sail (compute_aligned_dword_base_address val imm))
      (Sail.BitVec.extractLsb
        (shift_bits_left
          ((load_effective_address val imm) ^^^ (7 : BitVec 64))
          (3 : BitVec 6)) 5 0) := by
  have h7 : sign_extend (m := 64) (7 : BitVec 12) = (7 : BitVec 64) := by decide
  rw [hload_v0, hload_v1, h7]

-- Used by: `jolt_lb_logic_phase_concrete`.
-- Running the LB logic phase succeeds, leaves the shifted value in vreg 1,
-- and returns that same value from `readVReg 1`.
theorem jolt_lb_logic_phase_run (js_load : SailJoltState) :
    ∃ js_logic,
      (jolt_lb_logic_phase).run js_load = .ok (js_logic.vregs 1) js_logic ∧
      js_logic.sail = js_load.sail ∧
      js_logic.vregs 1 =
        shift_bits_left
          (js_load.vregs 1)
          (Sail.BitVec.extractLsb
            (shift_bits_left
              ((js_load.vregs 0) ^^^ (sign_extend (m := 64) (7 : BitVec 12)))
              (3 : BitVec 6)) 5 0) := by
  -- v0 after XORI:
  let js_xor : SailJoltState :=
    { sail := js_load.sail
      vregs := fun r =>
        if r = 0 then js_load.vregs 0 ^^^ sign_extend (m := 64) (7 : BitVec 12)
        else js_load.vregs r }
  -- v0 after SLLI:
  let js_shift0 : SailJoltState :=
    { sail := js_load.sail
      vregs := fun r =>
        if r = 0 then shift_bits_left (js_xor.vregs 0) (3 : BitVec 6)
        else js_xor.vregs r }
  -- v1 after SLL:
  let js_logic : SailJoltState :=
    { sail := js_load.sail
      vregs := fun r =>
        if r = 1 then
          shift_bits_left (js_shift0.vregs 1)
            (Sail.BitVec.extractLsb (js_shift0.vregs 0) 5 0)
        else js_shift0.vregs r }
  have hxori : vreg_XORI 0 0 (7 : BitVec 12) js_load = .ok RETIRE_SUCCESS js_xor := by
    change vreg_XORI 0 0 (7 : BitVec 12) js_load = .ok RETIRE_SUCCESS
      { sail := js_load.sail
        vregs := fun r =>
          if r = 0 then js_load.vregs 0 ^^^ sign_extend (m := 64) (7 : BitVec 12)
          else js_load.vregs r }
    simpa [js_xor] using (vreg_XORI_run 0 0 (7 : BitVec 12) js_load)
  have hslli : vreg_SLLI 0 0 3 js_xor = .ok RETIRE_SUCCESS js_shift0 := by
    change vreg_SLLI 0 0 3 js_xor = .ok RETIRE_SUCCESS
      { sail := js_xor.sail
        vregs := fun r =>
          if r = 0 then shift_bits_left (js_xor.vregs 0) (3 : BitVec 6)
          else js_xor.vregs r }
    simpa [js_xor, js_shift0] using (vreg_SLLI_run 0 0 3 js_xor)
  have hsll : vreg_SLL 1 1 0 js_shift0 = .ok RETIRE_SUCCESS js_logic := by
    change vreg_SLL 1 1 0 js_shift0 = .ok RETIRE_SUCCESS
      { sail := js_shift0.sail
        vregs := fun r =>
          if r = 1 then
            shift_bits_left (js_shift0.vregs 1) (Sail.BitVec.extractLsb (js_shift0.vregs 0) 5 0)
          else js_shift0.vregs r }
    simpa [js_shift0, js_logic] using (vreg_SLL_run 1 1 0 js_shift0)
  have hread_v1 : readVReg 1 js_logic = .ok (js_logic.vregs 1) js_logic := by
    simpa using (readVReg_run 1 js_logic)
  refine ⟨js_logic, ?_, rfl, ?_⟩
  · simp only [jolt_lb_logic_phase, bind, EStateM.bind, EStateM.run]
    rw [hxori]
    simp only [EStateM.bind, EStateM.pure]
    rw [hslli]
    simp only [EStateM.bind, EStateM.pure]
    rw [hsll]
    simp only [EStateM.bind, EStateM.pure]
    exact hread_v1
  · simp [js_logic, js_shift0, js_xor]

-- Used by: `jolt_lb_decomposed_writes_logic_value` (indirectly via
-- `jolt_lb_decomposed_from_phase_runs`).
-- Running the LB logic phase on the post-load state produces `logic_val` in
-- its long shift-left form, leaves the Sail state untouched, and stores
-- `logic_val` in vreg 1.
theorem jolt_lb_logic_phase_concrete (imm : BitVec 12) (js : SailJoltState)
    (js_load : SailJoltState) (val : BitVec 64)
    (hload_sail : js_load.sail = js.sail)
    (hload_v0 : js_load.vregs 0 = load_effective_address val imm)
    (hload_v1 : js_load.vregs 1 = loaded_dword_at js.sail (compute_aligned_dword_base_address val imm)) :
    ∃ js_logic logic_val,
      (jolt_lb_logic_phase).run js_load = .ok logic_val js_logic ∧
      js_logic.vregs 1 = logic_val ∧
      logic_val =
        shift_bits_left
          (loaded_dword_at js.sail (compute_aligned_dword_base_address val imm))
          (Sail.BitVec.extractLsb
            (shift_bits_left
              ((load_effective_address val imm) ^^^ (7 : BitVec 64))
              (3 : BitVec 6)) 5 0) ∧
      js_logic.sail = js.sail := by
  rcases jolt_lb_logic_phase_run js_load with ⟨js_logic, hrun, hsail, hv1⟩
  refine ⟨js_logic, js_logic.vregs 1, hrun, rfl, ?_, ?_⟩
  · rw [hv1]
    exact jolt_lb_logic_phase_value imm js js_load val hload_v0 hload_v1
  · simpa [hload_sail] using hsail

-- Used by: `jolt_lb_decomposed_writes_logic_value` (indirectly via
-- `jolt_lb_decomposed_from_phase_runs`).
-- The LB write phase writes `shift_bits_right_arith logic_val 56` to `rd`
-- and leaves vregs and all other memory untouched. Uses only generic
-- `wX_bits` shape lemmas — no LB-specific algebra.
theorem jolt_lb_write_phase_concrete (rd : regidx) (js : SailJoltState)
    (js_logic : SailJoltState) (logic_val : BitVec 64)
    (hlogic_sail : js_logic.sail = js.sail) :
    ∃ js',
      (jolt_lb_write_phase rd logic_val).run js_logic = .ok RETIRE_SUCCESS js' ∧
      js'.sail =
        stateAfterWrite js.sail rd (shift_bits_right_arith logic_val (56 : BitVec 6)) := by
  unfold jolt_lb_write_phase
  obtain ⟨s', hw⟩ := wX_shape rd (shift_bits_right_arith logic_val (56 : BitVec 6)) js.sail
  let js' : SailJoltState := { sail := s', vregs := js_logic.vregs }
  refine ⟨js', ?_, ?_⟩
  · simp only [liftSail, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
    rw [hlogic_sail, hw]
  · exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

-- Used by: `jolt_lb_decomposed_writes_logic_value`.
-- If the load, logic, and write phases all run successfully in sequence,
-- then `jolt_lb_decomposed` itself runs successfully with the same final
-- state.
theorem jolt_lb_decomposed_from_phase_runs (imm : BitVec 12) (rs1 rd : regidx)
    (js js_load js_logic js' : SailJoltState)
    (val logic_val : BitVec 64)
    (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (hload_run :
      (jolt_lb_load_phase (load_effective_address val imm)).run js = .ok RETIRE_SUCCESS js_load)
    (hlogic_run :
      (jolt_lb_logic_phase).run js_load = .ok logic_val js_logic)
    (hwrite_run :
      (jolt_lb_write_phase rd logic_val).run js_logic = .ok RETIRE_SUCCESS js') :
    (jolt_lb_decomposed imm rs1 rd).run js = .ok RETIRE_SUCCESS js' := by
  have hload_run' :
      jolt_lb_load_phase (val + sign_extend (m := 64) imm) js = .ok RETIRE_SUCCESS js_load := by
    simpa [load_effective_address, EStateM.run] using hload_run
  have hlogic_run' :
      jolt_lb_logic_phase js_load = .ok logic_val js_logic := by
    simpa [EStateM.run] using hlogic_run
  have hwrite_run' :
      jolt_lb_write_phase rd logic_val js_logic = .ok RETIRE_SUCCESS js' := by
    simpa [EStateM.run] using hwrite_run
  unfold jolt_lb_decomposed
  simp only [liftSail, bind, EStateM.bind, pure, EStateM.run]
  rw [hrx]
  simp only []
  rw [hload_run']
  change (EStateM.bind jolt_lb_logic_phase (fun v1 => jolt_lb_write_phase rd v1)) js_load =
    .ok RETIRE_SUCCESS js'
  simp only [EStateM.bind]
  rw [hlogic_run']
  simpa using hwrite_run'

-- Used by: `aligned_dword_addr_is_aligned_dword_access`.
-- The enclosing-dword base address `val + sext imm & -8` is 8-aligned.
theorem aligned_dword_addr_aligns (val : BitVec 64) (imm : BitVec 12) :
    aligned_dword_addr val imm &&& 7 = 0 := by
  rw [aligned_dword_addr_eq]
  bv_decide

-- Used by: `aligned_dword_addr_no_ovf`.
-- An 8-aligned 64-bit address has no overflow when we add 7.
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

-- Used by: `aligned_dword_addr_is_aligned_dword_access`.
theorem aligned_dword_addr_no_ovf (val : BitVec 64) (imm : BitVec 12) :
    (aligned_dword_addr val imm).toNat + 7 < 2 ^ 64 :=
  aligned_addr_no_ovf_of_align _ (aligned_dword_addr_aligns val imm)

-- Used by: `jolt_lb_decomposed_writes_logic_value`.
-- The enclosing-dword base is a properly aligned dword access: the
-- misalignment and split conditions hold, the address is 8-aligned, and
-- adding 7 doesn't overflow.
theorem aligned_dword_addr_is_aligned_dword_access (val : BitVec 64) (imm : BitVec 12) :
    AlignedDwordAccess (aligned_dword_addr val imm) := by
  refine
    { misalign := access_misaligned_8_aligned_false _ (aligned_dword_addr_aligns val imm)
      split := split_misaligned_aligned_8 _ (aligned_dword_addr_aligns val imm)
      align := aligned_dword_addr_aligns val imm
      no_ovf := aligned_dword_addr_no_ovf val imm }

-- Used by: `jolt_lb_concrete`.
-- Under our standing assumptions, the decomposed LB program
--   1. succeeds with some final state `js'`,
--   2. its logic phase returns `logic_val = shift_left dword (shift_left (ea XOR 7) 3)[5:0]`
--      (the target byte pushed to the top 8 bits of a 64-bit register), and
--   3. `rd` holds `shift_bits_right_arith logic_val 56` (arith-shift pulls the
--      target byte down and replicates the sign bit over the upper 56 bits).
-- No alignment hypothesis is required: byte loads have no alignment check.
theorem jolt_lb_decomposed_writes_logic_value (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (val : BitVec 64)
    (hrd : rd ≠ regidx.Regidx 0)
    (hcfg : JoltConfig js.sail)
    (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail) :
    ∃ js' logic_val,
      (jolt_lb_decomposed imm rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      logic_val =
        shift_bits_left
          (loaded_dword_at js.sail (compute_aligned_dword_base_address val imm))
          (Sail.BitVec.extractLsb
            (shift_bits_left
              ((load_effective_address val imm) ^^^ (7 : BitVec 64))
              (3 : BitVec 6)) 5 0) ∧
      js'.sail =
        stateAfterWrite js.sail rd
          (shift_bits_right_arith logic_val (56 : BitVec 6)) := by
  -- Setup: `v0 := ea; v1 := ea &&& -8` via the `vreg_ANDI` form.
  rcases InstructionEquivalence.load_phase_setup_concrete_andi imm js val with
    ⟨js1, hsetup_run, hsetup_sail, hsetup_v0, hsetup_v1⟩
  -- The aligned dword address is naturally aligned.
  have h_daddr_aligned : AlignedDwordAccess (compute_aligned_dword_base_address val imm) := by
    simpa [compute_aligned_dword_base_address, load_effective_address, aligned_dword_addr_eq] using
      (aligned_dword_addr_is_aligned_dword_access val imm)
  -- Load the enclosing double word into vreg 1.
  rcases InstructionEquivalence.vreg_LD_step_concrete js js1 (compute_aligned_dword_base_address val imm)
      hcfg hsetup_sail hsetup_v1 h_daddr_aligned h_dword_translate h_dword_phys with
    ⟨js_load, hld, hload_sail, hload_v0_raw, hload_v1⟩
  -- Assemble the full load phase run. Uses the ER-typed composition helper
  -- `vreg_LD_phase_from_setup_er` so the setup matches `jolt_lb_load_phase`
  -- minus `vreg_LD` directly, with no `pure ()` to collapse.
  have hload_run :
      (jolt_lb_load_phase (load_effective_address val imm)).run js = .ok RETIRE_SUCCESS js_load := by
    simpa [jolt_lb_load_phase, bind, EStateM.bind, EStateM.run] using
      (InstructionEquivalence.vreg_LD_phase_from_setup_er
        ((do
          writeVReg 0 (load_effective_address val imm)
          vreg_ANDI 1 0 (-8 : BitVec 12)) : JoltMonad ExecutionResult)
        js js1 js_load hsetup_run hld)
  have hload_v0 : js_load.vregs 0 = load_effective_address val imm := by
    rw [hload_v0_raw, hsetup_v0]
  -- Logic phase: shifts the dword left into the target-byte-at-top form.
  rcases jolt_lb_logic_phase_concrete imm js js_load val hload_sail hload_v0 hload_v1 with
    ⟨js_logic, logic_val, hlogic_run, hlogic_v1, hlogic_val, hlogic_sail⟩
  -- Write phase: `wX_bits rd (shift_bits_right_arith logic_val 56)`.
  rcases jolt_lb_write_phase_concrete rd js js_logic logic_val hlogic_sail with
    ⟨js', hwrite_run, hwrite_sail⟩
  refine ⟨js', logic_val, ?_, hlogic_val, hwrite_sail⟩
  exact jolt_lb_decomposed_from_phase_runs imm rs1 rd js js_load js_logic js' val logic_val
    hrx hload_run hlogic_run hwrite_run

-- Extracts the `k`-th byte (0-indexed from the low end) of a 64-bit dword.
def byte_of_dword (d : BitVec 64) (k : Nat) : BitVec 8 :=
  (d >>> (8 * k)).setWidth 8

-- Used by: `loaded_byte_in_dword`.
theorem loaded_dword_byte_k (s : SailState) (V : BitVec 64) (k : Nat)
    (hk : k < 8) :
    byte_of_dword (loaded_dword_at s V) k =
    loaded_byte_at s (V + BitVec.ofNat 64 k) := by
  unfold byte_of_dword loaded_dword_at
  interval_cases k <;> bv_decide

-- Used by: `loaded_byte_in_dword`.
theorem addr_split_aligned_offset (addr : BitVec 64) :
    (addr &&& (-8 : BitVec 64)) + BitVec.ofNat 64 (addr &&& 7).toNat = addr := by
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  bv_decide

-- Used by: `loaded_byte_in_dword` and `sll_srai_extracts_byte`.
theorem addr_and_seven_lt_eight (addr : BitVec 64) : (addr &&& 7).toNat < 8 := by
  rw [BitVec.toNat_and]
  exact Nat.and_lt_two_pow addr.toNat (by decide : (7 : BitVec 64).toNat < 2^3)

-- Used by: `jolt_lb_bridge`.
-- Hashmap key fact: the byte at `addr` equals the byte at position
-- `(addr & 7).toNat` of the enclosing dword.
--
-- Compared to LW_mod.lean's `loaded_word_in_dword`:
--   * DIFF: no `halign` hypothesis — byte accesses don't need alignment.
--   * DIFF: no `unfold byte_of_dword` step. LW's `loaded_dword_word_k`
--     is stated in the *unfolded* shift-and-setWidth form, so the LW
--     proof first unfolds `word_of_dword` to match. Our
--     `loaded_dword_byte_k` is stated in the *folded* form
--     `byte_of_dword (loaded_dword_at s V) k = …`, so the rewrite
--     matches the goal's RHS directly — and unfolding would actually
--     erase the pattern.
theorem loaded_byte_in_dword (s : SailState) (addr : BitVec 64) :
    loaded_byte_at s addr =
    byte_of_dword
      (loaded_dword_at s (addr &&& (-8 : BitVec 64)))
      (addr &&& 7).toNat := by
  rw [loaded_dword_byte_k s (addr &&& -8) (addr &&& 7).toNat
        (addr_and_seven_lt_eight addr)]
  rw [addr_split_aligned_offset]

-- Used by: `jolt_lb_bridge`.
-- Pure bit-vector identity: Jolt's XOR+SLLI+SLL+SRAI arithmetic on `d`
-- produces the sign-extension of `byte_of_dword d (addr & 7).toNat`.
theorem sll_srai_extracts_byte (d : BitVec 64) (addr : BitVec 64) :
    (let xor_addr  := addr ^^^ (7 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6   := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted   := shift_bits_left d shift_6
     shift_bits_right_arith shifted (56 : BitVec 6))
    = sign_extend (m := 64) (byte_of_dword d (addr &&& 7).toNat) := by
  unfold byte_of_dword shift_bits_left shift_bits_right_arith sign_extend
    Sail.BitVec.signExtend Sail.BitVec.extractLsb Sail.BitVec.toNatInt
  have hk_lt : (addr &&& 7).toNat < 8 := addr_and_seven_lt_eight addr
  set k := (addr &&& 7).toNat with hk_def
  have hk_eq : addr &&& 7 = BitVec.ofNat 64 k := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, hk_def]
    omega
  interval_cases k <;> bv_decide

-- Used by: `jolt_lb_concrete`.
-- Bridge lemma: the Jolt logic-phase computation for LB (shift the enclosing
-- dword left so the target byte occupies the top 8 bits, then arith-shift
-- right by 56 to pull it into the low 8 bits with sign replication) equals
-- the Sail-side direct byte load sign-extended to 64 bits. Pure bit-vector
-- algebra — no monads, no Sail pipeline.
theorem jolt_lb_bridge (s : SailState) (addr : BitVec 64) :
    (let dword     := loaded_dword_at s (addr &&& (-8 : BitVec 64))
     let xor_addr  := addr ^^^ (7 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6   := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted   := shift_bits_left dword shift_6
     shift_bits_right_arith shifted (56 : BitVec 6))
    = sign_extend (m := 64) (loaded_byte_at s addr) := by
  simp only [sll_srai_extracts_byte, ← loaded_byte_in_dword]

-- Used by: `jolt_lb_eq_sail`.
-- LHS helper: the Jolt LB sequence writes the sign-extended byte at `ea`
-- into `rd` and leaves everything else unchanged.
theorem jolt_lb_concrete (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail) :
    ∃ js' : SailJoltState,
      (jolt_lb imm rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (loaded_byte_at js.sail (load_effective_address val imm))) := by
  -- Running `jolt_lb` is the same as running `jolt_lb_decomposed`.
  have hrun_eq :
      (jolt_lb imm rs1 rd).run js = (jolt_lb_decomposed imm rs1 rd).run js := by
    simpa using jolt_lb_run_eq_decomposed imm rs1 rd js val hrx
  -- The decomposed program succeeds, producing `logic_val` in the long
  -- shift-left form; `rd` ends up holding `shift_bits_right_arith logic_val 56`.
  rcases jolt_lb_decomposed_writes_logic_value imm rs1 rd js val
      hrd hcfg hrx h_dword_translate h_dword_phys with
    ⟨js', logic_val, hdecomp_run, hlogic_val, hwrite_sail⟩
  refine ⟨js', ?_, ?_⟩
  -- (1) jolt_lb succeeds with final state js'.
  · rw [hrun_eq]
    exact hdecomp_run
  -- (2) `rd` holds the sign-extended byte: use the bridge lemma to rewrite
  --     the Jolt dword-shift expression into `sign_extend (loaded_byte_at …)`.
  · rw [hwrite_sail, hlogic_val]
    exact congrArg (stateAfterWrite js.sail rd)
      (jolt_lb_bridge js.sail (load_effective_address val imm))

-- Used by: `jolt_lb_eq_sail`.
-- RHS helper: Sail's `execute_LOAD` at width 1 (signed) writes the same value.
-- NOTE: Structurally identical to `execute_LW_reduces` in LW_mod.lean; the only
-- differences from the LW version are marked `-- DIFF:` below.
theorem execute_LB_reduces (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    -- DIFF: width = 1 (byte) instead of 4 (word).
    (hload : LoadReadAssumptions (load_effective_address val imm) 1 js.sail) :
    -- DIFF: no `h_no_ovf` hypothesis — single-byte reads cannot overflow the
    -- 64-bit address space, so the +3 side condition from LW drops out.
    -- DIFF: size = 1 in `execute_LOAD`, not 4.
    (execute_LOAD imm rs1 rd false 1).run js.sail =
    .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          -- DIFF: `loaded_byte_at` instead of `loaded_word_at`.
          (loaded_byte_at js.sail (load_effective_address val imm)))) := by
  -- Unfold execute_LOAD to vmem_read + extend_value + wX_bits.
  unfold execute_LOAD
  simp only [bind, pure]
  -- assert (1 ≤ xlen_bytes) passes.
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  simp (config := { decide := true }) only []
  -- Kill the assert.
  simp (config := { decide := true }) only [PreSail.assert, EStateM.bind, pure, EStateM.pure,
       EStateM.run, if_true]
  -- DIFF: reduce the memory read via the byte-width lemmas
  --   `vmem_read_byte_reduces` (LW used `vmem_read_word_reduces`) and
  --   `mem_read_1_eq_loaded_byte` (LW used `mem_read_4_eq_loaded_word`, which
  --   additionally required `h_no_ovf`).
  rw [vmem_read_byte_reduces imm rs1 js.sail val hrx hload.aligned hload.translate
      (mem_read_1_eq_loaded_byte _ js.sail hcfg hload.phys)]
  simp only [extend_value, Bool.false_eq_true, if_false, EStateM.bind, EStateM.pure]
  obtain ⟨s', hw⟩ := wX_shape rd
    -- DIFF: `loaded_byte_at` again, as in the goal.
    (sign_extend (m := 64) (loaded_byte_at js.sail (load_effective_address val imm)))
    js.sail
  rw [hw]
  simp only [RETIRE_SUCCESS]
  congr 1
  -- Final step: identical to LW — reusing `wX_bits_eq_stateAfterWrite`.
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

-- Main theorem: Jolt LB = Sail LB.
-- Unlike LW, byte loads have no alignment failure case, so there is no
-- aligned/misaligned split — we have a single path.
theorem jolt_lb_eq_sail (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hcfg : JoltConfig js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_dword_translate : BareTranslation (compute_aligned_dword_base_address val imm) js.sail)
    (h_dword_phys : FlatPhysMem (compute_aligned_dword_base_address val imm) 8 js.sail)
    (hload : LoadReadAssumptions (load_effective_address val imm) 1 js.sail) :
    projectResult ((jolt_lb imm rs1 rd).run js) =
    (execute_LOAD imm rs1 rd false 1).run js.sail := by
  -- LHS: Jolt runs to `stateAfterWrite rd (sign_extend (loaded_byte_at js.sail ea))`.
  have hjolt :=
    jolt_lb_concrete imm rs1 rd hrd js hcfg val hrx h_dword_translate h_dword_phys
  -- RHS: Sail `execute_LOAD … false 1` reduces to the same canonical state.
  have hsail := execute_LB_reduces imm rs1 rd js hcfg val hrx hload
  rcases hjolt with ⟨js', hjolt_run, hjolt_sail⟩
  rw [hjolt_run]
  simp only [projectResult, project]
  rw [hjolt_sail, hsail]

end LB_mod

