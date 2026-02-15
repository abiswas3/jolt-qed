/-
    LW (Load Word): Loads a 32-bit word from memory at (rs1 + offset), sign-extending the result into rd.

    TODO: 
    VirtualAssertWordAlignment (Assert Word Alignment): Emulator-internal assertion that verifies the computed address (rs1 + imm) is word-aligned (lower 2 bits are zero)
    asm.emit_halign::<VirtualAssertWordAlignment>(self.operands.rs1, self.operands.imm);

    ADDI (Add Immediate): Adds a sign-extended 12-bit immediate to rs1 and stores the result in rd.
    asm.emit_i::<ADDI>(*v_address, self.operands.rs1, self.operands.imm as u64);

    ANDI (AND Immediate): Computes the bitwise AND of rs1 and a sign-extended 12-bit immediate, storing the result in rd.
    asm.emit_i::<ANDI>(*v_dword_address, *v_address, -8i64 as u64);

    LD (Load Doubleword): Loads a 64-bit doubleword from memory at rs1 + offset into rd.
    asm.emit_ld::<LD>(*v_dword, *v_dword_address, 0);

    SLLI (Shift Left Logical Immediate): Shifts rs1 left by the immediate shift amount (masked to log2(XLEN) bits) and stores the result in rd.
    asm.emit_i::<SLLI>(*v_shift, *v_address, 3);
    VirtualSRL (Virtual Shift Right Logical Register): Emulator-internal instruction that performs a logical right shift of rs1 by the shift amount encoded in the trailing zeros of rs2. Description: Logical right shift on the value in register rs1 by the shift amount held in the lower 5 bits of register rs2
    asm.emit_r::<SRL>(self.operands.rd, *v_dword, *v_shift);
    asm.emit_i::<VirtualSignExtendWord>(self.operands.rd, self.operands.rd, 0);
-/ 


