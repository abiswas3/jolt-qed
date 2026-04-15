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
# LHU: Jolt load-halfword unsigned decomposition

From `tracer/src/instruction/lhu.rs::inline_sequence_64`:

    VirtualAssertHalfwordAlignment rs1, imm
    ADDI  v0, rs1, imm
    ANDI  v1, v0, -8
    LD    v1, v1, 0
    XORI  v0, v0, 6
    SLLI  v0, v0, 3
    SLL   v1, v1, v0
    SRLI  rd, v1, 48
-/

def jolt_lhu (imm : BitVec 12) (rs1 rd : regidx) : JoltMonad ExecutionResult :=
  jolt_halfword_load_family imm rs1 rd
    "LHU: effective address not halfword-aligned"
    (fun v1 => shift_bits_right v1 (48 : BitVec 6))

def halfword_of_dword (d : BitVec 64) (k : Nat) : BitVec 16 :=
  (d >>> (8 * k)).setWidth 16

theorem loaded_halfword_in_dword (s : SailState) (addr : BitVec 64)
    (halign : addr &&& 1 = 0) :
    loaded_halfword_at s addr =
    halfword_of_dword
      (loaded_dword_at s (addr &&& (-8 : BitVec 64)))
      (addr &&& 7).toNat := by
  sorry

theorem sll_srli_extracts_halfword (d : BitVec 64) (addr : BitVec 64)
    (halign : addr &&& 1 = 0) :
    (let xor_addr := addr ^^^ (6 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted := shift_bits_left d shift_6
     shift_bits_right shifted (48 : BitVec 6))
    = zero_extend (m := 64) (halfword_of_dword d (addr &&& 7).toNat) := by
  sorry

theorem jolt_lhu_bridge (s : SailState) (addr : BitVec 64)
    (halign : addr &&& 1 = 0) :
    (let dword := loaded_dword_at s (addr &&& (-8 : BitVec 64))
     let xor_addr := addr ^^^ (6 : BitVec 64)
     let shift_amt := shift_bits_left xor_addr (3 : BitVec 6)
     let shift_6 := Sail.BitVec.extractLsb shift_amt 5 0
     let shifted := shift_bits_left dword shift_6
     shift_bits_right shifted (48 : BitVec 6))
    = zero_extend (m := 64) (loaded_halfword_at s addr) := by
  sorry

theorem jolt_lhu_concrete (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) (hcfg : JoltConfig js.sail)
    (v : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok v js.sail)
    (halign : (v + sign_extend (m := 64) imm) &&& 1 = 0)
    (hdw : DwordLoadAssumptions (aligned_dword_addr v imm) js.sail) :
    ∃ js' : SailJoltState,
      (jolt_lhu imm rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (zero_extend (m := 64)
          (loaded_halfword_at js.sail (v + sign_extend (m := 64) imm))) := by
  sorry

theorem execute_LHU_reduces (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) (hcfg : JoltConfig js.sail)
    (v : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok v js.sail)
    (hload : LoadReadAssumptions (v + sign_extend (m := 64) imm) 2 js.sail)
    (h_no_ovf : (v + sign_extend (m := 64) imm).toNat + 1 < 2 ^ 64) :
    (execute_LOAD imm rs1 rd true 2).run js.sail =
    .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd
        (zero_extend (m := 64)
          (loaded_halfword_at js.sail (v + sign_extend (m := 64) imm)))) := by
  sorry

theorem jolt_lhu_eq_sail (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) (hcfg : JoltConfig js.sail)
    (h_half_aligned : ∀ v : BitVec 64, (v + sign_extend (m := 64) imm) &&& 1 = 0)
    (h_dw : ∀ v : BitVec 64, DwordLoadAssumptions (aligned_dword_addr v imm) js.sail)
    (h_half : ∀ v : BitVec 64, LoadReadAssumptions (v + sign_extend (m := 64) imm) 2 js.sail)
    (h_half_no_ovf : ∀ v : BitVec 64, (v + sign_extend (m := 64) imm).toNat + 1 < 2 ^ 64) :
    projectResult ((jolt_lhu imm rs1 rd).run js) =
    (execute_LOAD imm rs1 rd true 2).run js.sail := by
  sorry
