import JoltBytecode.JoltInstructions.JoltOps

/-!
# ADDW: Jolt Stateful Inline Sequence

## Rust Reference (tracer/src/instruction/addw.rs)

```rust
fn inline_sequence(&self, allocator: &VirtualRegisterAllocator, xlen: Xlen) -> Vec<Instruction> {
    let mut asm = InstrAssembler::new(self.address, self.is_compressed, xlen, allocator);
    asm.emit_r::<ADD>(self.operands.rd, self.operands.rs1, self.operands.rs2);
    asm.emit_i::<VirtualSignExtendWord>(self.operands.rd, self.operands.rd, 0);
    asm.finalize()
}
```

## Proof Strategy

ADDW is pure (no memory, no virtual temporaries). We keep the clean
separation: pure function equivalence, then state plumbing.
-/

open JoltOps

namespace JoltAddw

-- ============================================================================
-- Pure function (unchanged from old Addw.lean)
-- ============================================================================

def addwJolt (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  Jolt.virtualSignExtendWord (rs1_val + rs2_val)

theorem addw_eq_addwJolt (rs1_val rs2_val : BitVec 64) :
    Riscv.addw rs1_val rs2_val = addwJolt rs1_val rs2_val := by
  unfold Riscv.addw addwJolt Jolt.virtualSignExtendWord; rfl

-- ============================================================================
-- Composed sequence using shared JoltOps
-- ============================================================================

/-- ADDW inline sequence:
    ADD rd, rs1, rs2
    VirtualSignExtendWord rd, rd -/
def jolt_addw_seq (rs1 rs2 rd : BitVec 7) (js : JoltState) : JoltState :=
  let js := jolt_add rd rs1 rs2 js
  let js := jolt_virtual_sign_extend_word rd rd js
  js

-- ============================================================================
-- State: single whole-state equality theorem
-- ============================================================================

/-- ADDW on State: rd = signext32(rs1 + rs2). -/
def riscv_addw (rs1 rs2 rd : BitVec 5) (s : State) : State :=
  let val := Riscv.addw (read rs1 s.reg) (read rs2 s.reg)
  { s with reg := write rd val s.reg }

/-- Whole-state correctness: Jolt ADDW sequence on JoltState, projected to State,
    equals RISC-V ADDW on the projected State. -/
theorem jolt_addw_seq_eq (rs1 rs2 rd : BitVec 5) (js : JoltState) :
    (jolt_addw_seq (embedReg rs1) (embedReg rs2) (embedReg rd) js).toState
    = riscv_addw rs1 rs2 rd js.toState := by
  apply State.ext
  · -- mem
    simp [jolt_addw_seq, jolt_add, jolt_virtual_sign_extend_word, riscv_addw]
  · -- reg
    funext r
    simp only [jolt_addw_seq, jolt_add, jolt_virtual_sign_extend_word,
               riscv_addw, JoltState.toState, _root_.read, write,
               read_write_eq, write_write_eq,
               Riscv.addw, Jolt.virtualSignExtendWord]
    by_cases hrd : r = rd
    · subst hrd; simp [embedReg_inj]
    · have : embedReg r ≠ embedReg rd := by rwa [Ne, embedReg_inj]
      simp [this, hrd]
  · -- csr
    exact toState_csr_preserved js _ (by
      intro vr hge _
      simp only [jolt_addw_seq, jolt_add, jolt_virtual_sign_extend_word, write, read_write_eq, write_write_eq]
      have : embedReg rd ≠ vr := by
        intro h; have := embedReg_toNat_lt rd; rw [h] at this; omega
      simp [this])
  · -- pc
    simp [jolt_addw_seq, jolt_add, jolt_virtual_sign_extend_word, riscv_addw]
  · -- error
    simp [jolt_addw_seq, jolt_add, jolt_virtual_sign_extend_word, riscv_addw]

end JoltAddw
