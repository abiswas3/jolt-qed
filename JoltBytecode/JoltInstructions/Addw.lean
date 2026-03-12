import JoltBytecode.JoltInstructions.JoltOps
import JoltBytecode.BytecodeExpansions.Common.FormatR

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
-- Main theorem
-- ============================================================================

/-- The result's register file matches: rd gets addw result, others unchanged. -/
theorem jolt_addw_seq_reg_eq (rs1 rs2 rd : BitVec 5) (s : State) (r : BitVec 5) :
    (jolt_addw_seq (embedReg rs1) (embedReg rs2) (embedReg rd) s.toJoltState).toState.reg r
    = (format_r_exec rs1 rs2 rd Riscv.addw s).reg r := by
  simp only [jolt_addw_seq, jolt_add, jolt_virtual_sign_extend_word,
             read_write_eq, write_write_eq, toJoltState_read_embedReg]
  simp only [JoltState.toState, _root_.read, write]
  simp only [format_r_exec, Riscv.addw, Jolt.virtualSignExtendWord, write]
  by_cases hr : embedReg r = embedReg rd
  · have := embedReg_injective hr; simp [this, _root_.read]
  · have hr' : r ≠ rd := fun h => hr (congrArg embedReg h)
    simp [hr, hr']
    exact toState_toJoltState_reg s r

/-- Memory is unchanged by ADDW. -/
theorem jolt_addw_seq_mem_eq (rs1 rs2 rd : BitVec 5) (s : State) :
    (jolt_addw_seq (embedReg rs1) (embedReg rs2) (embedReg rd) s.toJoltState).toState.mem
    = s.mem := by
  simp [jolt_addw_seq, jolt_add, jolt_virtual_sign_extend_word,
        JoltState.toState, State.toJoltState]

/-- Error is unchanged by ADDW. -/
theorem jolt_addw_seq_error_eq (rs1 rs2 rd : BitVec 5) (s : State) :
    (jolt_addw_seq (embedReg rs1) (embedReg rs2) (embedReg rd) s.toJoltState).toState.error
    = s.error := by
  simp [jolt_addw_seq, jolt_add, jolt_virtual_sign_extend_word,
        JoltState.toState, State.toJoltState]

/-- PC is unchanged by ADDW. -/
theorem jolt_addw_seq_pc_eq (rs1 rs2 rd : BitVec 5) (s : State) :
    (jolt_addw_seq (embedReg rs1) (embedReg rs2) (embedReg rd) s.toJoltState).toState.pc
    = s.pc := by
  simp [jolt_addw_seq, jolt_add, jolt_virtual_sign_extend_word,
        JoltState.toState, State.toJoltState]

end JoltAddw
