
    /-
        asm.emit_i::<VirtualMovsign>(*v_sx, self.operands.rs1, 0);
    asm.emit_i::<VirtualMovsign>(*v_sy, self.operands.rs2, 0);
    asm.emit_r::<MULHU>(*v_0, self.operands.rs1, self.operands.rs2);
    asm.emit_r::<MUL>(*v_sx, *v_sx, self.operands.rs2);
    asm.emit_r::<MUL>(*v_sy, *v_sy, self.operands.rs1);
    asm.emit_r::<ADD>(*v_0, *v_0, *v_sx);
    asm.emit_r::<ADD>(self.operands.rd, *v_0, *v_sy);
    asm.finalize()
    
    -/
def signExtract (x : BitVec w) : Int :=
  if x.msb then -1 else 0

/-- VirtualMovSign: extracts the sign bit as a w-bit register value.
    Produces allOnes (two's complement -1) if negative, 0 otherwise.
    This is the BitVec-valued counterpart of `signExtract`. -/
def virtualMovSign (x : BitVec w) : BitVec w :=
  BitVec.ofInt w (signExtract x)

/-- MULHU: unsigned high multiplication.
    Computes the upper w bits of the unsigned product of x and y:
      floor(toNat(x) * toNat(y) / 2^w) -/
def mulhu (x y : BitVec w) : BitVec w :=
  BitVec.ofNat w (x.toNat * y.toNat / 2 ^ w)


/-- The RISC-V MULH instruction: computes the upper w bits of the signed product.
    Given two w-bit signed integers x and y, MULH returns:
      floor(toInt(x) * toInt(y) / 2^w)  mod 2^w -/
def mulh (x y : BitVec w) : BitVec w :=
  BitVec.ofInt w (x.toInt * y.toInt / (2 ^ w : Int))



def jolt_VirtualMovSign (r1 rd : BitVec 6) (s : JoltState)  : JoltState :=
  let r1val := readdata r1 s.reg
  let rdval := BitVec.ofInt 64 (signExtract r1val)
  let new_reg := writedata rd rdval s.reg
  { s with reg := new_reg }

def jolt_mulhu (r1 r2 rd : BitVec 6) (s : JoltState)  : JoltState :=
  let x := readdata r1 s.reg
  let y := readdata r2 s.reg
  let rdval := BitVec.ofNat 64 (x.toNat * y.toNat / (2 ^ 64))
  let new_reg := writedata rd rdval s.reg
  { s with reg := new_reg }


def jolt_mul (r1 r2 rd : BitVec 6) (s : JoltState)  : JoltState :=
  let x := readdata r1 s.reg
  let y := readdata r2 s.reg
  let rdval := BitVec.ofInt 64 (x.toInt * y.toInt)
  let new_reg := writedata rd rdval s.reg
  { s with reg := new_reg }

def jolt_add (r1 r2 rd : BitVec 6) (s : JoltState)  : JoltState :=
  let x := readdata r1 s.reg
  let y := readdata r2 s.reg
  let rdval := BitVec.ofInt 64 (x.toInt + y.toInt)
  let new_reg := writedata rd rdval s.reg
  { s with reg := new_reg }

def riscv_to_jolt (s : State ) : JoltState := 
  {
  mem := s.mem,
  reg := fun x => if x[5] then 0 else s.reg (x.setWidth 5),
  is_error:= s.is_error
  }

def jolt_to_riscv (s : JoltState) : State := 
  {
  mem:= s.mem,
  reg := fun x => s.reg (x.setWidth 6),
  is_error:= s.is_error
  }

/- The Jolt virtual instruction decomposition for MULH.
    Each line corresponds to a virtual instruction in the expansion sequence.
    MUL and ADD are standard BitVec `*` and `+` (modular arithmetic). 
def mulhJolt (x y : BitVec w) : BitVec w :=
  let v_sx := Jolt.virtualMovSign x       -- VirtualMovsign v_sx, rs1, 0
  let v_sy := Jolt.virtualMovSign y       -- VirtualMovsign v_sy, rs2, 0
  let v_0  := Jolt.mulhu x y              -- MULHU v_0, rs1, rs2
  let v_sx := v_sx * y                    -- MUL v_sx, v_sx, rs2
  let v_sy := v_sy * x                    -- MUL v_sy, v_sy, rs1
  let v_0  := v_0 + v_sx                  -- ADD v_0, v_0, v_sx
  v_0 + v_sy                              -- ADD rd,  v_0, v_sy
-/

def mulhJolt (r1 r2 rd : BitVec 5) (s : State) : State := 
  let js := riscv_to_jolt s
  let v_sx := 32#6
  let v_sy := 33#6
  let v_0 := 34#6
  let r1 := r1.setWidth 6
  let r2 := r2.setWidth 6
  let rd := rd.setWidth 6
  let js := jolt_VirtualMovSign v_sx r1 js
  let js := jolt_VirtualMovSign v_sx r2 js
  let js := jolt_mulhu v_0 r1 r2 js
  let js := jolt_mul v_sx v_sx r2 js
  let js := jolt_mul v_sy v_sy r1 js
  let js := jolt_add v_0 v_0 v_sx js
  let js := jolt_add rd v_0 v_sy js
  jolt_to_riscv js

def mulhRiscv (r1 r2 rd : BitVec 5) (s : State) : State := 
  let x := readdata r1 s.reg
  let y := readdata r2 s.reg
  let rdval := BitVec.ofInt 64 (x.toInt * y.toInt / (2 ^ 64 : Int))
  let new_reg := writedata rd rdval s.reg
  { s with reg := new_reg }

theorem jolt_mulh_eq_riscv_mulh (r1 r2 rd : BitVec 5) (s : State) : mulhJolt r1 r2 rd s = mulhRiscv r1 r2 rd s := by
  unfold mulhJolt mulhRiscv jolt_VirtualMovSign jolt_mulhu jolt_mul jolt_add
  simp_all
  ext1
  . 
