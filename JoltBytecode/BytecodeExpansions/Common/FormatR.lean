import JoltBytecode.BytecodeExpansions.Common.Cpu

/-! # Format R: State-level execution for R-type instructions

R-type instructions read two source registers, apply a pure operation,
and write the result to a destination register. This file defines the
common execution pattern and a lifting theorem: if two pure operations
are (extensionally) equal, then their state-level executions are equal.

This lets us prove state equivalence for any R-type instruction by
working entirely at the pure-function level. (Load/store instructions
that touch memory will need a different pattern.) -/

abbrev FormatROp := BitVec 64 → BitVec 64 → BitVec 64

def format_r_exec (r1 r2 rd : BitVec 5) (op : FormatROp) (s : State) : State :=
  let r1val := read r1 s.reg
  let r2val := read r2 s.reg
  let rdval := op r1val r2val
  let new_reg := write rd rdval s.reg
  { s with reg := new_reg }

theorem format_r_ops_eq_of_fns_eq (op1 op2 : FormatROp)
    (r1 r2 rd : BitVec 5) (s : State)
    (h : op1 = op2) :
    format_r_exec r1 r2 rd op1 s = format_r_exec r1 r2 rd op2 s := by
  unfold format_r_exec
  simp_all
