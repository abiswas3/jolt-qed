import JoltBytecode.EmbeddedSailJoltState.JoltISA.Instruction

/-!
# Jolt ISA semantics

`execInstr` gives each Jolt-ISA instruction its monadic meaning over
`SailJoltState`.  `execProgram` is the small interpreter used by generated
Rust expansion lists.
-/

set_option maxHeartbeats 1_000_000_000
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
  | .SD base value imm => do
      let baseValue ← readVReg base
      let addr := baseValue + sign_extend (m := 64) imm
      let stored ← readVReg value
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

def execProgram : Program → JoltMonad ExecutionResult
  | .done result => pure result
  | .instr instr rest => do
      match ← execInstr instr with
      | .Retire_Success () => execProgram rest
      | result => pure result

end JoltISA

end
