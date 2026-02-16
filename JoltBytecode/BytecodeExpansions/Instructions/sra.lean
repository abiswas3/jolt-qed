-- TODO:
/- SRA (Shift Right Arithmetic): Arithmetically shifts rs1 right by the shift amount in rs2 (masked to log2(XLEN) bits), sign-filling the upper bits, and stores the result in rd.

asm.emit_i::<VirtualShiftRightBitmask>(*v_bitmask, self.operands.rs2, 0);
asm.emit_vshift_r::<VirtualSRA>(self.operands.rd, self.operands.rs1, *v_bitmask);
-/
