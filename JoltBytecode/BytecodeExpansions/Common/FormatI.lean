import JoltBytecode.BytecodeExpansions.Common.Cpu

/-! # Format I: State-level execution for I-type instructions

I-type instructions read one source register and a sign-extended immediate,
apply a pure operation, and write the result to a destination register.
This mirrors `format_r_exec` but the second operand is an immediate value
rather than a second register read.

As with Format R, the lifting theorem lets us prove state equivalence by
working entirely at the pure-function level. -/

abbrev FormatIOp := BitVec 64 → BitVec 64 → BitVec 64

def format_i_exec (rs1 rd : BitVec 5) (imm : BitVec 64) (op : FormatIOp) (s : State) : State :=
  let rs1val := read rs1 s.reg
  let rdval := op rs1val imm
  let new_reg := write rd rdval s.reg
  { s with reg := new_reg }

theorem format_i_ops_eq_of_fns_eq (op1 op2 : FormatIOp)
    (rs1 rd : BitVec 5) (imm : BitVec 64) (s : State)
    (h : op1 = op2) :
    format_i_exec rs1 rd imm op1 s = format_i_exec rs1 rd imm op2 s := by
  unfold format_i_exec
  simp_all
