/- 
SRLIW (Shift Right Logical Immediate Word): Logically shifts the lower 32 bits of rs1 right by the immediate amount (masked to 5 bits), sign-extending the 32-bit result into rd.
Format I type: 

Jolt Expansion:
    
    -- VirtualSRLI is defined as following 
    -- VirtualSignExtendWord (Sign-Extend Word): Emulator-internal instruction that sign-extends the lower 32 bits of rs1 into a 64-bit value in rd. Only valid in 64-bit mode.
    asm.emit_vshift_i::<VirtualSRLI>(self.operands.rd, *v_rs1, bitmask);
    
    -- We already have Jolt Virtual Sign Extend 
    asm.emit_i::<VirtualSignExtendWord>(self.operands.rd, self.operands.rd, 0);

    
CLAUDE instructions : add virtual srli to Virtual.lean, 
then setup the theorem statement with sorry.
-/
