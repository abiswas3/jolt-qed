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
# LBU: Jolt load-byte unsigned decomposition

From `tracer/src/instruction/lbu.rs::inline_sequence_64`:

    ADDI  v0, rs1, imm
    ANDI  v1, v0, -8
    LD    v1, v1, 0
    XORI  v0, v0, 7
    SLLI  v0, v0, 3
    SLL   v1, v1, v0
    SRLI  rd, v1, 56
-/

def jolt_lbu (imm : BitVec 12) (rs1 rd : regidx) : JoltMonad ExecutionResult :=
  jolt_byte_load_family imm rs1 rd
    (fun v1 => shift_bits_right v1 (56 : BitVec 6))

def byte_of_dword (d : BitVec 64) (k : Nat) : BitVec 8 :=
  (d >>> (8 * k)).setWidth 8

theorem loaded_dword_byte_k (s : SailState) (V : BitVec 64) (k : Nat)
    (hk : k < 8) :
    ((loaded_dword_at s V) >>> (8 * k)).setWidth 8 =
    loaded_byte_at s (V + BitVec.ofNat 64 k) := by
  unfold loaded_dword_at
  interval_cases k <;> bv_decide

theorem addr_split_aligned_offset (addr : BitVec 64) :
    (addr &&& (-8 : BitVec 64)) + BitVec.ofNat 64 (addr &&& 7).toNat = addr := by
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  bv_decide

theorem addr_and_seven_lt_eight (addr : BitVec 64) : (addr &&& 7).toNat < 8 := by
  rw [BitVec.toNat_and]
  exact Nat.and_lt_two_pow addr.toNat (by decide : (7 : BitVec 64).toNat < 2^3)

theorem loaded_byte_in_dword (s : SailState) (addr : BitVec 64) :
    loaded_byte_at s addr =
    byte_of_dword
      (loaded_dword_at s (addr &&& (-8 : BitVec 64)))
      (addr &&& 7).toNat := by
  unfold byte_of_dword
  rw [loaded_dword_byte_k s (addr &&& -8) (addr &&& 7).toNat
        (addr_and_seven_lt_eight addr)]
  rw [addr_split_aligned_offset]

theorem sll_srli_extracts_byte (d : BitVec 64) (addr : BitVec 64) :
    (let xor_addr  := addr ^^^ (7 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6   := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted   := shift_bits_left d shift_6
     shift_bits_right shifted (56 : BitVec 6))
    = zero_extend (m := 64) (byte_of_dword d (addr &&& 7).toNat) := by
  unfold byte_of_dword shift_bits_left shift_bits_right zero_extend
    Sail.BitVec.zeroExtend Sail.BitVec.extractLsb
  have hk_lt : (addr &&& 7).toNat < 8 := addr_and_seven_lt_eight addr
  set k := (addr &&& 7).toNat with hk_def
  have hk_eq : addr &&& 7 = BitVec.ofNat 64 k := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, hk_def]
    omega
  interval_cases k <;> bv_decide

theorem jolt_lbu_bridge (s : SailState) (addr : BitVec 64) :
    (let dword     := loaded_dword_at s (addr &&& (-8 : BitVec 64))
     let xor_addr  := addr ^^^ (7 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6   := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted   := shift_bits_left dword shift_6
     shift_bits_right shifted (56 : BitVec 6))
    = zero_extend (m := 64) (loaded_byte_at s addr) := by
  simp only [sll_srli_extracts_byte, ← loaded_byte_in_dword]

theorem jolt_lbu_concrete (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) (hcfg : JoltConfig js.sail)
    (v : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok v js.sail)
    (hdw : DwordLoadAssumptions (aligned_dword_addr v imm) js.sail) :
    ∃ js' : SailJoltState,
      (jolt_lbu imm rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (zero_extend (m := 64)
          (loaded_byte_at js.sail (v + sign_extend (m := 64) imm))) := by
  unfold jolt_lbu jolt_byte_load_family vreg_LD
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
             liftSail, writeVReg, readVReg, modify, modifyGet,
             getThe, MonadStateOf.get, MonadStateOf.modifyGet,
             EStateM.get, EStateM.modifyGet, get, hrx,
             vreg_ANDI_run, if_true]
  rw [aligned_dword_vmem_read_reduces _ js.sail hcfg hdw]
  simp only [RETIRE_SUCCESS, vreg_XORI_run, vreg_SLLI_run, vreg_SLL_run, if_true,
             EStateM.bind, EStateM.pure,
             EStateM.get, EStateM.modifyGet]
  simp (config := {decide := true}) only [if_false]
  have h_xor : v + sign_extend (m := 64) imm ^^^ sign_extend (m := 64) (7 : BitVec 12) =
               (v + sign_extend (m := 64) imm) ^^^ (7 : BitVec 64) := by
    have h7 : sign_extend (m := 64) (7 : BitVec 12) = (7 : BitVec 64) := by decide
    rw [h7]
  rw [aligned_dword_addr_eq, h_xor]
  rw [jolt_lbu_bridge]
  unfold liftSail
  obtain ⟨s', hw⟩ := wX_shape rd
    (zero_extend (m := 64) (loaded_byte_at js.sail (v + sign_extend (m := 64) imm)))
    js.sail
  rw [hw]
  refine ⟨_, rfl, ?_⟩
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

theorem execute_LBU_reduces (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) (hcfg : JoltConfig js.sail)
    (v : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok v js.sail)
    (hload : LoadReadAssumptions (v + sign_extend (m := 64) imm) 1 js.sail) :
    (execute_LOAD imm rs1 rd true 1).run js.sail =
    .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd
        (zero_extend (m := 64)
          (loaded_byte_at js.sail (v + sign_extend (m := 64) imm)))) := by
  unfold execute_LOAD
  simp only [bind, pure]
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  simp (config := { decide := true }) only []
  simp (config := { decide := true }) only [PreSail.assert, EStateM.bind, pure, EStateM.pure,
       EStateM.run, if_true]
  rw [vmem_read_byte_reduces imm rs1 js.sail v hrx hload.aligned hload.translate
      (mem_read_1_eq_loaded_byte _ js.sail hcfg hload.phys)]
  simp only [extend_value, if_true, EStateM.bind, EStateM.pure]
  obtain ⟨s', hw⟩ := wX_shape rd
    (zero_extend (m := 64) (loaded_byte_at js.sail (v + sign_extend (m := 64) imm)))
    js.sail
  rw [hw]
  simp only [RETIRE_SUCCESS]
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

theorem jolt_lbu_eq_sail (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) (hcfg : JoltConfig js.sail)
    (h_dw : ∀ v : BitVec 64, DwordLoadAssumptions (aligned_dword_addr v imm) js.sail)
    (h_byte : ∀ v : BitVec 64, LoadReadAssumptions (v + sign_extend (m := 64) imm) 1 js.sail) :
    projectResult ((jolt_lbu imm rs1 rd).run js) =
    (execute_LOAD imm rs1 rd true 1).run js.sail := by
  obtain ⟨v, hrx⟩ := hwf rs1
  obtain ⟨js', hjolt, hjolt_sail⟩ :=
    jolt_lbu_concrete imm rs1 rd hrd js hwf hcfg v hrx (h_dw v)
  have hsail := execute_LBU_reduces imm rs1 rd js hwf hcfg v hrx (h_byte v)
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail, hsail]
