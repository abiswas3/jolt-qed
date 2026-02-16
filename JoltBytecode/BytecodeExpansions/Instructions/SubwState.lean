import JoltBytecode.BytecodeExpansions.Common.Cpu
import JoltBytecode.BytecodeExpansions.Instructions.Subw

-- RISCV SUBW Instruction
-- Subtracts lower 32 bits of x[r2] from lower 32 bits of x[r1]
-- Sign extends the result to 64 bits and store it as x[rd]
-- here x[r] is notation for the value stored by register r
def riscv_subw (r1 r2 rd : BitVec 5) (s : State) : State :=
  -- TODO: set flags
  let r1val := read r1 s.reg
  let r2val := read r2 s.reg
  let rdval := Riscv.subw r1val r2val
  let new_reg := write rd rdval s.reg
  { s with reg := new_reg }

-- Jolt's decomposition of SUBW using virtual instructions:
-- SUB rd, rs1, rs2              (64-bit subtraction)
-- VirtualSignExtendWord rd, rd  (sign-extend lower 32 bits)
def jolt_subw (r1 r2 rd : BitVec 5) (s : State) : State :=
  -- TODO set flags
  let r1val := read r1 s.reg
  let r2val := read r2 s.reg
  -- SUB rd, rs1, rs2
  let sub := Riscv.sub r1val r2val
  -- VirtualSignExtendWord rd, rd, 0
  let rdval := Jolt.virtualSignExtendWord sub
  let new_reg := write rd rdval s.reg
  { s with reg := new_reg }

theorem jolt_subw_eq_riscv_subw (r1 r2 rd : BitVec 5) (s : State) :
    riscv_subw r1 r2 rd s = jolt_subw r1 r2 rd s := by
  unfold riscv_subw jolt_subw Riscv.subw Riscv.sub Jolt.virtualSignExtendWord
  simp only [setWidth_sub_32]
