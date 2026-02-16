import JoltBytecode.BytecodeExpansions.Cpu

-- RISCV SUBW Instruction
-- Subtracts lower 32 bits of x[r2] from lower 32 bits of x[r1]
-- Sign extends the result to 64 bits and store it as x[rd]
-- here x[r] is notation for the value stored by register r
def riscv_subw (r1 r2 rd : BitVec 5) (s : State) : State :=
  -- TODO: set flags
  let r1val := read r1 s.reg
  let r2val := read r2 s.reg
  let rdval := ((r1val.setWidth 32) - (r2val.setWidth 32)).signExtend 64
  let new_reg := write rd rdval s.reg
  { s with reg := new_reg }

def jolt_subw (r1 r2 rd : BitVec 5) (s : State) : State :=
  -- TODO set flags
  let r1val := read r1 s.reg
  let r2val := read r2 s.reg
  -- TODO: This should be a composition of Jolt insturctions (see mulh using state)
  -- but we are slowly growing complexity.
  let rdval := ((r1val - r2val).setWidth 32).signExtend 64
  let new_reg := write rd rdval s.reg
  { s with reg := new_reg }

-- NOTE: Bringing in mathlib.tactic allows for use of Lemma instead of theorem
lemma setWidth_sub_32 (x y : BitVec 64) :
    (x - y).setWidth 32 = x.setWidth 32 - y.setWidth 32 := by
  bv_omega

theorem jold_subw_eq_riscv_subw (r1 r2 rd : BitVec 5) (s : State) : riscv_subw r1 r2 rd s = jolt_subw r1 r2 rd s := by
  unfold jolt_subw riscv_subw
  ext x i
  . simp only
  . simp
    unfold write
    by_cases h : x = rd
    . simp_all
      congr 2
      rw [setWidth_sub_32]
    . simp_all
