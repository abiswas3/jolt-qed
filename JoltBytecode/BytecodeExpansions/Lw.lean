/-
    LW (Load Word): Loads a 32-bit word from memory at (rs1 + offset), sign-extending the result into rd.

    TODO: 
    asm.emit_halign::<VirtualAssertWordAlignment>(self.operands.rs1, self.operands.imm);
    asm.emit_i::<ADDI>(*v_address, self.operands.rs1, self.operands.imm as u64);
    asm.emit_i::<ANDI>(*v_dword_address, *v_address, -8i64 as u64);
    asm.emit_ld::<LD>(*v_dword, *v_dword_address, 0);
    asm.emit_i::<SLLI>(*v_shift, *v_address, 3);
    asm.emit_r::<SRL>(self.operands.rd, *v_dword, *v_shift);
    asm.emit_i::<VirtualSignExtendWord>(self.operands.rd, self.operands.rd, 0);


-/ 
