
def riscvSubw (x y : BitVec 64) : BitVec 64 := ((x.setWidth 32)-(y.setWidth 32)).signExtend 64
def joltSubw (x y : BitVec 64) : BitVec 64 := ((x-y).setWidth 32).signExtend 64

theorem rv_eq_jolt_subw (x y : BitVec 64)  : riscvSubw x y = joltSubw x y := by sorry

abbrev FormatROp := BitVec 64 → BitVec 64 → BitVec 64

def format_r_exec (r1 r2 rd : BitVec 5) (op : FormatROp) (s : State) : State := 
  let r1val := readdata r1 s.reg
  let r2val := readdata r2 s.reg
  let rdval := op r1val r2val
  let new_reg := writedata rd rdval s.reg
  { s with reg := new_reg }

def add_op (r1 r2 rd : BitVec 5) (s : State) : State :=
  format_r_exec r1 r2 rd add s


theorem format_r_ops_eq_of_fns_eq (op1 op2 : FormatROp) (r1 r2 rd : BitVec 5) (s : State) (h : op1 = op2): format_r_exec r1 r2 rd op1 s = format_r_exec r1 r2 rd op2 s := by
  unfold format_r_exec
  simp_all

theorem subw_with_state_are_equal (r1 r2 rd : BitVec 5) (s : State) : format_r_exec r1 r2 rd riscvSubw s = format_r_exec r1 r2 rd joltSubw s := by
  exact format_r_ops_eq_of_fns_eq riscvSubw joltSubw r1 r2 rd s (by ext1 x ; ext1 y; exact rv_eq_jolt_subw x y)
