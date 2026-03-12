import JoltBytecode.JoltInstructions.RiscvState
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
-- Helper lemmas
-- ============================================================================

-- Unconditional cross-register read lemmas (avoids simp discharger issues with read_write_ne)
@[simp] private lemma read_v0_write_embedReg (r : BitVec 5) (v : BitVec 64) (ds : JoltRegFile) :
    _root_.read v0_reg (write (embedReg r) v ds) = _root_.read v0_reg ds :=
  read_write_ne _ _ _ _ (v0_ne_embedReg r)

@[simp] private lemma read_embedReg_write_v0 (r : BitVec 5) (v : BitVec 64) (ds : JoltRegFile) :
    _root_.read (embedReg r) (write v0_reg v ds) = _root_.read (embedReg r) ds :=
  read_write_ne _ _ _ _ (embedReg_ne_v0 r)

/-- jolt_read_word equals the dword-extract formula (bridges to read_word_eq_dword_extract). -/
private lemma jolt_read_word_eq_dword_extract (addr : BitVec 64) (js : JoltState)
    (h_aligned : addr &&& 3#64 = 0#64) :
    jolt_read_word addr js =
    (jolt_read_dword (addr &&& (-8#64)) js >>> ((addr <<< 3).setWidth 6).toNat).setWidth 32 := by
  -- Construct a State with same memory to reuse existing read_word_eq_dword_extract
  let s : State := ⟨js.mem, fun _ => 0#64, fun _ => 0#64, 0#64, false⟩
  -- jolt_read_* and read_* agree when memory matches (definitional equality)
  exact read_word_eq_dword_extract addr s h_aligned

-- ============================================================================
-- RiscvState: single whole-state equality theorem
-- ============================================================================

/-- LW on RiscvState: load 32-bit word, sign-extend to 64 bits.
    Sets error if address is not word-aligned. -/
def riscv_lw (rs1 rd : BitVec 5) (imm : BitVec 12) (s : RiscvState) : RiscvState :=
  let addr := Riscv.addi (read (embedReg rs1) s.reg) imm
  if addr &&& 3#64 ≠ 0#64 then { s with error := true }
  else
    let word := riscv_read_word addr s
    { s with reg := write (embedReg rd) (word.signExtend 64) s.reg }

/-- The toRiscvState.reg read at embedReg equals the raw js.reg read. -/
private lemma toRiscvState_read_embedReg' (js : JoltState) (r : BitVec 5) :
    _root_.read (embedReg r) js.toRiscvState.reg = _root_.read (embedReg r) js.reg := by
  simp [_root_.read, JoltState.toRiscvState,
        show (embedReg r).toNat < 40 from by have := embedReg_toNat_lt r; omega]

/-- Whole-state correctness: Jolt LW sequence projected to RiscvState
    equals RISC-V LW on the projected RiscvState. -/
theorem jolt_lw_seq_eq (rs1 rd : BitVec 5) (imm : BitVec 12) (js : JoltState)
    (h_no_error : js.error = false) :
    (jolt_lw_seq (embedReg rs1) (embedReg rd) imm js).toRiscvState
    = riscv_lw rs1 rd imm js.toRiscvState := by
  -- Normalize the RHS address read
  have h_rhs_addr : _root_.read (embedReg rs1) js.toRiscvState.reg = _root_.read (embedReg rs1) js.reg :=
    toRiscvState_read_embedReg' js rs1
  -- Unfold the LHS alignment check
  simp only [jolt_lw_seq, jolt_virtual_assert_word_align, Riscv.addi]
  -- Split on alignment (matches the LHS if)
  by_cases h_align : (imm.setWidth 64 + _root_.read (embedReg rs1) js.reg) &&& 3#64 = 0#64
  · -- ===== Aligned case =====
    -- Resolve LHS: alignment ok → error stays false → proceed
    have h_not_ne : ¬ ((imm.setWidth 64 + _root_.read (embedReg rs1) js.reg) &&& 3#64 ≠ 0#64) :=
      not_not.mpr h_align
    -- Simplify LHS: reduce alignment check, error check
    simp only [h_not_ne, ↓reduceIte, h_no_error]
    -- Unfold all jolt ops
    simp only [jolt_addi, jolt_andi, jolt_ld, jolt_slli, jolt_srl,
               jolt_virtual_sign_extend_word,
               read_write_eq, read_v0_write_embedReg, read_embedReg_write_v0, write_write_eq,
               jolt_read_dword_with_reg,
               Riscv.addi, Riscv.andi, Riscv.slli, Riscv.srl, Jolt.virtualSignExtendWord]
    -- Unfold RHS
    simp only [riscv_lw, h_rhs_addr, Riscv.addi, h_not_ne, ↓reduceIte]
    -- Bridge: riscv_read_word on toRiscvState = jolt_read_word = dword extract
    rw [riscv_read_word_toRiscvState,
        jolt_read_word_eq_dword_extract _ js h_align]
    -- Structural equality
    apply RiscvState.ext
    · simp [JoltState.toRiscvState]
    · funext r
      simp only [JoltState.toRiscvState, _root_.read, write]
      by_cases hr40 : r.toNat < 40
      · rw [if_pos hr40]
        by_cases hrd : r = embedReg rd
        · subst hrd; simp [_root_.write, ↓reduceIte]
        · have hne_rd : ¬ (embedReg rd = r) := fun h => hrd h.symm
          have hne_v0 : ¬ (v0_reg = r) := by
            intro h; rw [← h] at hr40; simp [v0_reg] at hr40
          have hne_v0' : ¬ (r = v0_reg) := Ne.symm hne_v0
          simp [hne_rd, hne_v0', _root_.write, hrd, if_pos hr40]
      · rw [if_neg hr40]
        have hne_rd : r ≠ embedReg rd := by
          intro h; have := embedReg_toNat_lt rd; rw [h] at hr40; omega
        simp [_root_.write, hne_rd, if_neg hr40]
    · simp [JoltState.toRiscvState]
    · simp [JoltState.toRiscvState, h_no_error]
  · -- ===== Misaligned case =====
    -- Resolve LHS: alignment fails → error set → early return
    -- h_align : ¬ (... = 0#64), which is ≠ 0#64
    -- Resolve LHS if (... ≠ 0#64)
    simp only [ne_eq, h_align, not_false_eq_true, ↓reduceIte]
    -- Unfold RHS: misaligned too
    simp only [riscv_lw, h_rhs_addr, Riscv.addi, ne_eq, h_align, not_false_eq_true, ↓reduceIte]
    apply RiscvState.ext
    · simp [JoltState.toRiscvState]
    · funext r; simp [JoltState.toRiscvState]
    · simp [JoltState.toRiscvState]
    · simp [JoltState.toRiscvState]

end JoltLw
