import JoltBytecode.JoltInstructions.JoltOps
import JoltBytecode.BytecodeExpansions.Instructions.Lw -- for read_dword, lw_eq lemmas

/-!
# LW: Jolt Stateful Inline Sequence

## Rust Reference (tracer/src/instruction/lw.rs, inline_sequence_64)

```rust
fn inline_sequence_64(&self, allocator: &VirtualRegisterAllocator) -> Vec<Instruction> {
    let v0 = allocator.allocate();
    let mut asm = InstrAssembler::new(self.address, self.is_compressed, Xlen::Bit64, allocator);
    asm.emit_align::<VirtualAssertWordAlignment>(self.operands.rs1, self.operands.imm);
    asm.emit_i::<ADDI>(*v0, self.operands.rs1, self.operands.imm as u64);
    asm.emit_i::<ANDI>(self.operands.rd, *v0, -8i64 as u64);
    asm.emit_ld::<LD>(self.operands.rd, self.operands.rd, 0);
    asm.emit_i::<SLLI>(*v0, *v0, 3);
    asm.emit_r::<SRL>(self.operands.rd, self.operands.rd, *v0);
    asm.emit_i::<VirtualSignExtendWord>(self.operands.rd, self.operands.rd, 0);
    asm.finalize()
}
```

## Register Allocation
- `rs1` : RISC-V source register (embedded as 7-bit via `embedReg`)
- `rd`  : RISC-V destination register (embedded as 7-bit via `embedReg`)
- `v0`  : Virtual register 40 (first allocatable temporary)
-/

open JoltOps

namespace JoltLw

-- ============================================================================
-- Composed sequence using shared JoltOps
-- ============================================================================

/-- The full Jolt LW inline sequence as a composition of state transitions. -/
def jolt_lw_seq (rs1 rd : BitVec 7) (imm : BitVec 12) (js : JoltState) : JoltState :=
  -- Step 1: VirtualAssertWordAlignment rs1, imm
  let js := jolt_virtual_assert_word_align rs1 imm js
  if js.error then js else
  -- Step 2: ADDI v0, rs1, imm
  let js := jolt_addi v0_reg rs1 imm js
  -- Step 3: ANDI rd, v0, -8
  let js := jolt_andi rd v0_reg (-8#64) js
  -- Step 4: LD rd, rd, 0
  let js := jolt_ld rd rd js
  -- Step 5: SLLI v0, v0, 3
  let js := jolt_slli v0_reg v0_reg 3 js
  -- Step 6: SRL rd, rd, v0
  let js := jolt_srl rd rd v0_reg js
  -- Step 7: VirtualSignExtendWord rd, rd
  let js := jolt_virtual_sign_extend_word rd rd js
  js

-- ============================================================================
-- Bridge lemmas (jolt_read_dword ↔ read_dword)
-- ============================================================================

@[simp] private lemma jolt_read_dword_toJoltState (addr : BitVec 64) (s : State) :
    jolt_read_dword addr s.toJoltState = read_dword addr s := rfl

@[simp] private lemma jolt_read_dword_mk_mem (addr : BitVec 64) (s : State)
    (reg : JoltRegFile) (pc : BitVec 64) (err : Bool) :
    jolt_read_dword addr ⟨s.mem, reg, pc, err⟩ = read_dword addr s := rfl

-- Unconditional cross-register read lemmas (avoids simp discharger issues with read_write_ne)
@[simp] private lemma read_v0_write_embedReg (r : BitVec 5) (v : BitVec 64) (ds : JoltRegFile) :
    _root_.read v0_reg (write (embedReg r) v ds) = _root_.read v0_reg ds :=
  read_write_ne _ _ _ _ (v0_ne_embedReg r)

@[simp] private lemma read_embedReg_write_v0 (r : BitVec 5) (v : BitVec 64) (ds : JoltRegFile) :
    _root_.read (embedReg r) (write v0_reg v ds) = _root_.read (embedReg r) ds :=
  read_write_ne _ _ _ _ (embedReg_ne_v0 r)

-- ============================================================================
-- Main theorem: register file correctness
-- ============================================================================

/-- The result's register file matches RISC-V LW for every register. -/
theorem jolt_lw_seq_reg_eq (rs1 rd : BitVec 5) (imm : BitVec 12) (s : State)
    (h_no_error : s.error = false) (r : BitVec 5) :
    (jolt_lw_seq (embedReg rs1) (embedReg rd) imm s.toJoltState).toState.reg r
    = (Riscv.lw rs1 rd imm s).reg r := by
  -- Unfold both sides and split on alignment
  simp only [jolt_lw_seq, jolt_virtual_assert_word_align, toJoltState_read_embedReg,
             Riscv.lw, Riscv.addi]
  split
  · -- Misaligned: both sides set error, register file unchanged
    rename_i h
    simp only [h, ↓reduceIte, JoltState.toState, toJoltState_read_embedReg]
    rfl
  · -- Aligned: both sides compute the LW value
    rename_i h_aligned
    simp only [ne_eq, not_not] at h_aligned
    -- Phase 0: Resolve error check and alignment condition
    simp only [toJoltState_error, h_no_error, h_aligned, ne_eq, not_true_eq_false,
               ↓reduceIte, Bool.false_eq_true, not_false_eq_true]
    -- Phase 1: Unfold jolt ops, simplify register chain, convert jolt_read_dword → read_dword
    simp only [jolt_addi, jolt_andi, jolt_ld, jolt_slli, jolt_srl,
               jolt_virtual_sign_extend_word,
               read_write_eq, read_v0_write_embedReg, read_embedReg_write_v0, write_write_eq,
               toJoltState_read_embedReg,
               toJoltState_mem, toJoltState_pc, toJoltState_error,
               jolt_read_dword_mk_mem,
               Riscv.addi, Riscv.andi, Riscv.slli, Riscv.srl, Jolt.virtualSignExtendWord]
    -- Phase 2: Bridge read_word to dword extract so both sides have the same value
    rw [read_word_eq_dword_extract _ s h_aligned]
    -- Phase 3: Project to State, case split on r = rd
    simp only [JoltState.toState]
    by_cases hr : r = rd
    · -- r = rd: both sides compute the same value
      subst hr; simp only [read_write_eq, _root_.write, ↓reduceIte]
    · -- r ≠ rd: register unchanged by LW
      have hne : embedReg r ≠ embedReg rd := fun h => hr (embedReg_injective h)
      rw [read_write_ne _ _ _ _ hne, read_embedReg_write_v0,
          read_write_ne _ _ _ _ hne, read_embedReg_write_v0,
          toJoltState_read_embedReg]
      simp only [_root_.write, hr, ↓reduceIte]
      rfl

/-- Memory is unchanged by LW (all steps only write registers). -/
theorem jolt_lw_seq_mem_eq (rs1 rd : BitVec 5) (imm : BitVec 12) (s : State)
    (h_no_error : s.error = false) :
    (jolt_lw_seq (embedReg rs1) (embedReg rd) imm s.toJoltState).toState.mem
    = s.mem := by
  simp only [jolt_lw_seq, jolt_virtual_assert_word_align, toJoltState_read_embedReg]
  split
  · -- Misaligned: early exit, state unchanged except error
    simp [JoltState.toState, State.toJoltState]
  · -- Aligned: 6 register-only ops, memory preserved
    simp [h_no_error, jolt_addi, jolt_andi, jolt_ld, jolt_slli, jolt_srl,
          jolt_virtual_sign_extend_word, JoltState.toState, State.toJoltState]

/-- Error flag matches RISC-V LW. -/
theorem jolt_lw_seq_error_eq (rs1 rd : BitVec 5) (imm : BitVec 12) (s : State)
    (h_no_error : s.error = false) :
    (jolt_lw_seq (embedReg rs1) (embedReg rd) imm s.toJoltState).toState.error
    = (Riscv.lw rs1 rd imm s).error := by
  simp only [jolt_lw_seq, jolt_virtual_assert_word_align, toJoltState_read_embedReg,
             Riscv.lw, Riscv.addi]
  split
  · -- Misaligned
    simp [JoltState.toState, State.toJoltState, h_no_error]
  · -- Aligned
    rename_i h
    simp only [ne_eq, not_not] at h
    simp [h, h_no_error, jolt_addi, jolt_andi, jolt_ld, jolt_slli, jolt_srl,
          jolt_virtual_sign_extend_word, JoltState.toState, State.toJoltState]

/-- PC is unchanged by LW. -/
theorem jolt_lw_seq_pc_eq (rs1 rd : BitVec 5) (imm : BitVec 12) (s : State)
    (h_no_error : s.error = false) :
    (jolt_lw_seq (embedReg rs1) (embedReg rd) imm s.toJoltState).toState.pc
    = s.pc := by
  simp only [jolt_lw_seq, jolt_virtual_assert_word_align, toJoltState_read_embedReg]
  split
  · simp [JoltState.toState, State.toJoltState]
  · simp [h_no_error, jolt_addi, jolt_andi, jolt_ld, jolt_slli, jolt_srl,
          jolt_virtual_sign_extend_word, JoltState.toState, State.toJoltState]

end JoltLw
