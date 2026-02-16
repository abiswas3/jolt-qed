import JoltBytecode.BytecodeExpansions.Common.Cpu
-- TODO:
/- 
RISV - Defintion
.store_word(
cpu.x[self.operands.rs1 as usize].wrapping_add(self.operands.imm) as u64,
cpu.x[self.operands.rs2 as usize] as u32,
)

Jolt Expansion
    -- this bit is identical to Jolt LD 
    asm.emit_halign::<VirtualAssertWordAlignment>(self.operands.rs1, self.operands.imm);
    asm.emit_i::<ADDI>(*v_address, self.operands.rs1, self.operands.imm as u64);
    asm.emit_i::<ANDI>(*v_dword_address, *v_address, -8i64 as u64);
    asm.emit_ld::<LD>(*v_dword, *v_dword_address, 0);

    asm.emit_i::<SLLI>(*v_shift, *v_address, 3);
    asm.emit_i::<ORI>(*v_mask, 0, -1i64 as u64);
    asm.emit_i::<SRLI>(*v_mask, *v_mask, 32);
    asm.emit_r::<SLL>(*v_mask, *v_mask, *v_shift);
    asm.emit_r::<SLL>(*v_word, self.operands.rs2, *v_shift);
    asm.emit_r::<XOR>(*v_word, *v_dword, *v_word);
    asm.emit_r::<AND>(*v_word, *v_word, *v_mask);
    asm.emit_r::<XOR>(*v_dword, *v_dword, *v_word);
    asm.emit_s::<SD>(*v_dword_address, *v_dword, 0);

    -- Jolt's LW: read dword, shift, truncate.
def jolt_lw (rs1 rd : BitVec 5) (imm : BitVec 12) (s : State) : State :=
  let base := read rs1 s.reg
  let addr := (imm.setWidth 64 + base) &&& (-4#64)
  let dword_addr := addr &&& (-8#64)
  let dword := read_dword dword_addr s
  let shift := (addr <<< 3).setWidth 6
  let word := (dword >>> shift.toNat).setWidth 32
  let new_reg := write rd (word.signExtend 64) s.reg
  { s with reg := new_reg }
-/

def store_rw (rs1 : BitVec 5) (imm: BitVec 12) (s: State) : State :=
  sorry 
