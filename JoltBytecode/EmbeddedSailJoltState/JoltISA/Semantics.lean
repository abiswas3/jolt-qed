import JoltBytecode.EmbeddedSailJoltState.JoltISA.Instruction

/-!
# Jolt ISA semantics

`execInstr` gives each Jolt-ISA instruction its monadic meaning over
`SailJoltState`.  `execProgram` is the small interpreter used by generated
Rust expansion lists.
-/

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace JoltISA

def execInstr : Instr → JoltMonad ExecutionResult
  | .ADDI dst src imm => do
      let x ← readSrc src
      writeDst dst (x + sign_extend (m := 64) imm)
      pure RETIRE_SUCCESS
  | .ANDI dst src imm => do
      let x ← readSrc src
      writeDst dst (x &&& sign_extend (m := 64) imm)
      pure RETIRE_SUCCESS
  | .ORI dst src imm => do
      let x ← readSrc src
      writeDst dst (x ||| sign_extend (m := 64) imm)
      pure RETIRE_SUCCESS
  | .XORI dst src imm => do
      let x ← readSrc src
      writeDst dst (x ^^^ sign_extend (m := 64) imm)
      pure RETIRE_SUCCESS
  | .LUI dst imm => do
      writeDst dst imm
      pure RETIRE_SUCCESS
  | .AUIPC dst imm => do
      let pc ← liftSail (get_arch_pc ())
      let off : BitVec 64 := sign_extend (m := 64) (imm +++ 0x000#12)
      writeDst dst (pc + off)
      pure RETIRE_SUCCESS
  | .JAL dst imm => do
      let link ← liftSail (get_next_pc ())
      let pc ← liftSail (Sail.readReg Register.PC)
      match ← liftSail (jump_to (pc + sign_extend (m := 64) imm)) with
      | .Retire_Success () =>
          writeDst dst link
          pure RETIRE_SUCCESS
      | other => pure other
  | .JALR dst base imm => do
      let link ← liftSail (get_next_pc ())
      let target ← readSrc base
      match ← liftSail (jump_to (BitVec.update (target + sign_extend (m := 64) imm) 0 0#1)) with
      | .Retire_Success () =>
          writeDst dst link
          pure RETIRE_SUCCESS
      | other => pure other
  | .ADD dst lhs rhs => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      writeDst dst (x + y)
      pure RETIRE_SUCCESS
  | .SUB dst lhs rhs => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      writeDst dst (x - y)
      pure RETIRE_SUCCESS
  | .MUL dst lhs rhs => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      writeDst dst (x * y)
      pure RETIRE_SUCCESS
  | .MULH dst lhs rhs => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      writeDst dst (mulhs x y)
      pure RETIRE_SUCCESS
  | .MULHU dst lhs rhs => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      writeDst dst (jolt_mulhu_value x y)
      pure RETIRE_SUCCESS
  | .VirtualMULI dst src imm => do
      let x ← readSrc src
      writeDst dst (jolt_virtual_muli_value x imm)
      pure RETIRE_SUCCESS
  | .VirtualPow2 dst src => do
      let x ← readSrc src
      writeDst dst (jolt_virtual_pow2_value x)
      pure RETIRE_SUCCESS
  | .VirtualPow2W dst src => do
      let x ← readSrc src
      writeDst dst (jolt_virtual_pow2w_value x)
      pure RETIRE_SUCCESS
  | .VirtualShiftRightBitmask dst src => do
      let x ← readSrc src
      writeDst dst (jolt_virtual_shift_right_bitmask_value x)
      pure RETIRE_SUCCESS
  | .VirtualSRLI dst src bitmask => do
      let x ← readSrc src
      writeDst dst (jolt_virtual_srli_value x bitmask)
      pure RETIRE_SUCCESS
  | .VirtualSRAI dst src bitmask => do
      let x ← readSrc src
      writeDst dst (jolt_virtual_srai_value x bitmask)
      pure RETIRE_SUCCESS
  | .VirtualSRL dst value bitmask => do
      let x ← readSrc value
      let b ← readSrc bitmask
      writeDst dst (jolt_virtual_srl_value x b)
      pure RETIRE_SUCCESS
  | .VirtualSRA dst value bitmask => do
      let x ← readSrc value
      let b ← readSrc bitmask
      writeDst dst (jolt_virtual_sra_value x b)
      pure RETIRE_SUCCESS
  | .OR dst lhs rhs => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      writeDst dst (x ||| y)
      pure RETIRE_SUCCESS
  | .XOR dst lhs rhs => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      writeDst dst (x ^^^ y)
      pure RETIRE_SUCCESS
  | .AND dst lhs rhs => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      writeDst dst (x &&& y)
      pure RETIRE_SUCCESS
  | .SLT dst lhs rhs => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      writeDst dst (zero_extend (m := 64) (bool_to_bit (zopz0zI_s x y)))
      pure RETIRE_SUCCESS
  | .SLTU dst lhs rhs => do
      let x ← readSrc lhs
      let y ← readSrc rhs
      writeDst dst (jolt_sltu_value x y)
      pure RETIRE_SUCCESS
  | .SLLI dst src shamt => do
      let x ← readSrc src
      writeDst dst (shift_bits_left x shamt)
      pure RETIRE_SUCCESS
  | .SRLI dst src shamt => do
      let x ← readSrc src
      writeDst dst (shift_bits_right x shamt)
      pure RETIRE_SUCCESS
  | .SRAI dst src shamt => do
      let x ← readSrc src
      writeDst dst (shift_bits_right_arith x shamt)
      pure RETIRE_SUCCESS
  | .SLL dst value shamt => do
      let x ← readSrc value
      let y ← readSrc shamt
      writeDst dst (shift_bits_left x (Sail.BitVec.extractLsb y 5 0))
      pure RETIRE_SUCCESS
  | .SRL dst value shamt => do
      let x ← readSrc value
      let y ← readSrc shamt
      writeDst dst (shift_bits_right x (Sail.BitVec.extractLsb y 5 0))
      pure RETIRE_SUCCESS
  | .SExtW dst src => do
      let x ← readSrc src
      writeDst dst (sign_extend (m := 64) (Sail.BitVec.extractLsb x 31 0))
      pure RETIRE_SUCCESS
  | .ZExtW dst src => do
      let x ← readSrc src
      writeDst dst (zero_extend (m := 64) (Sail.BitVec.extractLsb x 31 0))
      pure RETIRE_SUCCESS
  | .Movsign dst src => do
      let x ← readSrc src
      writeDst dst (jolt_movsign_value x)
      pure RETIRE_SUCCESS
  | .AssertLoadAlign base imm mask => do
      let baseValue ← liftSail (rX_bits base)
      let addr := baseValue + sign_extend (m := 64) imm
      if addr &&& mask ≠ 0 then
        pure (ExecutionResult.Memory_Exception
          (Virtaddr addr, ExceptionType.E_Load_Addr_Align ()))
      else
        pure RETIRE_SUCCESS
  | .AssertStoreAlign base imm mask => do
      let baseValue ← liftSail (rX_bits base)
      let addr := baseValue + sign_extend (m := 64) imm
      if addr &&& mask ≠ 0 then
        pure (ExecutionResult.Memory_Exception
          (Virtaddr addr, ExceptionType.E_SAMO_Addr_Align ()))
      else
        pure RETIRE_SUCCESS
  | .LD vd base imm => do
      let baseValue ← readVReg base
      let addr := baseValue + sign_extend (m := 64) imm
      match ← liftSail (vmem_read_addr (Virtaddr addr) 0 8 (Load Data) false false false) with
      | .Ok dword =>
          writeVReg vd dword
          pure RETIRE_SUCCESS
      | .Err e => pure e
  | .LDFrom vd base imm => do
      let baseValue ← readSrc base
      let addr := baseValue + sign_extend (m := 64) imm
      match ← liftSail (vmem_read_addr (Virtaddr addr) 0 8 (Load Data) false false false) with
      | .Ok dword =>
          writeVReg vd dword
          pure RETIRE_SUCCESS
      | .Err e => pure e
  | .SD base value imm => do
      let baseValue ← readVReg base
      let addr := baseValue + sign_extend (m := 64) imm
      let stored ← readVReg value
      match ← liftSail (vmem_write_addr (Virtaddr addr) 8 stored (Store Data) false false false) with
      | .Ok _ => pure RETIRE_SUCCESS
      | .Err e => pure e
  | .SDFrom base value imm => do
      let baseValue ← readSrc base
      let addr := baseValue + sign_extend (m := 64) imm
      let stored ← readSrc value
      match ← liftSail (vmem_write_addr (Virtaddr addr) 8 stored (Store Data) false false false) with
      | .Ok _ => pure RETIRE_SUCCESS
      | .Err e => pure e
  | .Advice vd value => do
      writeVReg vd value
      pure RETIRE_SUCCESS
  | .AssertEq lhs rhs => do
      let x ← readVReg lhs
      let y ← readVReg rhs
      if x = y then pure RETIRE_SUCCESS
      else throw (Error.Assertion "VirtualAssertEQ")
  | .AssertEqReal lhs rhs => do
      let x ← readVReg lhs
      let y ← liftSail (rX_bits rhs)
      if x = y then pure RETIRE_SUCCESS
      else throw (Error.Assertion "VirtualAssertEQ (vreg vs real)")
  | .AssertValidDiv0 divisor quotient => do
      let d ← liftSail (rX_bits divisor)
      let q ← readVReg quotient
      if d = 0#64 ∧ q ≠ (-1 : BitVec 64) then
        throw (Error.Assertion "VirtualAssertValidDiv0: divisor = 0 but quotient ≠ -1")
      else
        pure RETIRE_SUCCESS
  | .AssertValidDiv0V divisor quotient => do
      let d ← readVReg divisor
      let q ← readVReg quotient
      if d = 0#64 ∧ q ≠ (-1 : BitVec 64) then
        throw (Error.Assertion "VirtualAssertValidDiv0: divisor = 0 but quotient ≠ -1")
      else
        pure RETIRE_SUCCESS
  | .ChangeDivisor dst dividend divisor => do
      let a ← liftSail (rX_bits dividend)
      let b ← liftSail (rX_bits divisor)
      let mostNeg : BitVec 64 := (1 : BitVec 64) <<< 63
      let negOne : BitVec 64 := -1
      writeVReg dst (if a = mostNeg ∧ b = negOne then 1 else b)
      pure RETIRE_SUCCESS
  | .ChangeDivisorW dst dividend divisor => do
      let a ← readVReg dividend
      let b ← readVReg divisor
      let i32MinSext : BitVec 64 := -((1 : BitVec 64) <<< 31)
      let negOne : BitVec 64 := -1
      writeVReg dst (if a = i32MinSext ∧ b = negOne then 1 else b)
      pure RETIRE_SUCCESS
  | .AssertValidUnsignedRemainder remainder divisor => do
      let r ← readVReg remainder
      let d ← readVReg divisor
      if d = 0#64 ∨ r.toNat < d.toNat then
        pure RETIRE_SUCCESS
      else
        throw (Error.Assertion "VirtualAssertValidUnsignedRemainder: r ≥ d ∧ d ≠ 0")
  | .AssertValidUnsignedRemainderReal remainder divisor => do
      let r ← readVReg remainder
      let d ← liftSail (rX_bits divisor)
      if d = 0#64 ∨ r.toNat < d.toNat then
        pure RETIRE_SUCCESS
      else
        throw (Error.Assertion "VirtualAssertValidUnsignedRemainder: r ≥ d ∧ d ≠ 0")
  | .AssertMulUNoOverflow lhs rhs => do
      let x ← readVReg lhs
      let y ← liftSail (rX_bits rhs)
      if x.toNat * y.toNat < 2^64 then
        pure RETIRE_SUCCESS
      else
        throw (Error.Assertion "VirtualAssertMulUNoOverflow")
  | .AssertMulUNoOverflowV lhs rhs => do
      let x ← readVReg lhs
      let y ← readVReg rhs
      if x.toNat * y.toNat < 2^64 then
        pure RETIRE_SUCCESS
      else
        throw (Error.Assertion "VirtualAssertMulUNoOverflow")
  | .AssertLTEReal lhs rhs => do
      let x ← readVReg lhs
      let y ← liftSail (rX_bits rhs)
      if x.toNat ≤ y.toNat then
        pure RETIRE_SUCCESS
      else
        throw (Error.Assertion "VirtualAssertLTE")
  | .AssertLTE lhs rhs => do
      let x ← readVReg lhs
      let y ← readVReg rhs
      if x.toNat ≤ y.toNat then
        pure RETIRE_SUCCESS
      else
        throw (Error.Assertion "VirtualAssertLTE")

def execProgram : Program → JoltMonad ExecutionResult
  | .done result => pure result
  | .instr instr rest => do
      match ← execInstr instr with
      | .Retire_Success () => execProgram rest
      | result => pure result

end JoltISA

end
