import Mathlib.Tactic
import Mathlib.Data.BitVec
import JoltBytecode.BytecodeExpansions.Common.Cpu

variable {w : Nat}

namespace Riscv

-- ============================================================================
-- Base Integer Instructions (generic over width)
-- ============================================================================

/-- SUB rd, rs1, rs2: subtraction. rd = rs1 - rs2 -/
def sub (x y : BitVec w) : BitVec w :=
  x - y

/-- ADD rd, rs1, rs2: addition. rd = rs1 + rs2 -/
def add (x y : BitVec w) : BitVec w :=
  x + y

/-- ADDI rd, rs1, imm: add immediate (zero-extended to 64 bits).
    rd = rs1 + zeroExtend(imm) -/
def addi (x : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  imm.setWidth 64 + x

/-- ANDI rd, rs1, rs2: bitwise AND. rd = rs1 & rs2 -/
def andi (x y : BitVec w) : BitVec w :=
  x &&& y

/-- SLLI rd, rs1, shamt: logical left shift by immediate. rd = rs1 << shamt -/
def slli (x : BitVec w) (shamt : Nat) : BitVec w :=
  x <<< shamt

/-- SRL rd, rs1, rs2 (RV64): logical right shift.
    rd = rs1 >> rs2[5:0] -/
def srl (x y : BitVec 64) : BitVec 64 :=
  x >>> (y.setWidth 6).toNat

/-- ORI rd, rs1, imm: bitwise OR with immediate. rd = rs1 | imm -/
def ori (x imm : BitVec w) : BitVec w :=
  x ||| imm

/-- SRLI rd, rs1, shamt: logical right shift by immediate. rd = rs1 >>> shamt -/
def srli (x : BitVec w) (shamt : Nat) : BitVec w :=
  x >>> shamt

/-- SLL rd, rs1, rs2 (RV64): logical left shift.
    rd = rs1 << rs2[5:0] -/
def sll (x y : BitVec 64) : BitVec 64 :=
  x <<< (y.setWidth 6).toNat

/-- XOR rd, rs1, rs2: bitwise exclusive OR. rd = rs1 ^ rs2 -/
def xor (x y : BitVec w) : BitVec w :=
  x ^^^ y

/-- AND rd, rs1, rs2: bitwise AND. rd = rs1 & rs2 -/
def and (x y : BitVec w) : BitVec w :=
  x &&& y

/-- SUBW rd, rs1, rs2 (RV64I): subtract lower 32 bits and sign-extend to 64 bits.
    rd = signExtend(rs1[31:0] - rs2[31:0]) -/
def subw (x y : BitVec 64) : BitVec 64 :=
  (x.setWidth 32 - y.setWidth 32).signExtend 64


/-- SRLIW rd, rs1, shamt (RV64I): logical right shift of lower 32 bits by shamt[4:0],
    sign-extend the 32-bit result to 64 bits.
    rd = signExtend(rs1[31:0] >>> shamt[4:0]) -/
def srliw (rs1_val shamt : BitVec 64) : BitVec 64 :=
  ((rs1_val.setWidth 32) >>> (shamt.setWidth 5).toNat).signExtend 64

/-- SRAW rd, rs1, rs2 (RV64I): arithmetic right shift of lower 32 bits by rs2[4:0],
    sign-extend the 32-bit result to 64 bits.
    rd = signExtend(rs1[31:0] >>_arith rs2[4:0]) -/
def sraw (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  ((rs1_val.setWidth 32).sshiftRight (rs2_val.setWidth 5).toNat).signExtend 64

/-- SRAIW rd, rs1, shamt (RV64I): arithmetic right shift of lower 32 bits by shamt[4:0],
    sign-extend the 32-bit result to 64 bits.
    rd = signExtend(rs1[31:0] >>_arith shamt[4:0]) -/
def sraiw (rs1_val shamt : BitVec 64) : BitVec 64 :=
  ((rs1_val.setWidth 32).sshiftRight (shamt.setWidth 5).toNat).signExtend 64

/-- SLLIW rd, rs1, shamt (RV64I): logical left shift of lower 32 bits by shamt[4:0],
    sign-extend the 32-bit result to 64 bits.
    rd = signExtend(rs1[31:0] << shamt[4:0]) -/
def slliw (rs1_val shamt : BitVec 64) : BitVec 64 :=
  ((rs1_val.setWidth 32) <<< (shamt.setWidth 5).toNat).signExtend 64

-- ============================================================================
-- Full 64-bit immediate shift/add (RV64I, Format I)
-- ============================================================================

/-- ADDIW rd, rs1, imm (RV64I): add immediate to rs1, truncate to 32 bits,
    sign-extend to 64 bits.
    rd = signExtend((rs1 + imm)[31:0]) -/
def addiw (rs1_val imm : BitVec 64) : BitVec 64 :=
  ((rs1_val + imm).setWidth 32).signExtend 64

/-- TODO: Write proper docstrings --/ 
def addw (rs1_val rs2_val : BitVec 64): BitVec 64 := 
  ((rs1_val + rs2_val).setWidth 32).signExtend 64

/-- SLLI rd, rs1, shamt (RV64I, Format I): logical left shift of full 64-bit value
    by shamt[5:0].
    rd = rs1 << shamt[5:0] -/
def slli64 (rs1_val shamt : BitVec 64) : BitVec 64 :=
  rs1_val <<< (shamt.setWidth 6).toNat

/-- SRLI rd, rs1, shamt (RV64I, Format I): logical right shift of full 64-bit value
    by shamt[5:0].
    rd = rs1 >>> shamt[5:0] -/
def srli64 (rs1_val shamt : BitVec 64) : BitVec 64 :=
  rs1_val >>> (shamt.setWidth 6).toNat

/-- SRAI rd, rs1, shamt (RV64I, Format I): arithmetic right shift of full 64-bit value
    by shamt[5:0].
    rd = rs1 >>_arith shamt[5:0] -/
def srai64 (rs1_val shamt : BitVec 64) : BitVec 64 :=
  rs1_val.sshiftRight (shamt.setWidth 6).toNat

-- ============================================================================
-- Multiply Extension (generic over width)
-- ============================================================================

/-- MUL rd, rs1, rs2: multiplication (lower w bits of product). -/
def mul (x y : BitVec w) : BitVec w :=
  x * y

/-- MULHU rd, rs1, rs2: unsigned high multiplication.
    Returns upper w bits of the unsigned 2w-bit product. -/
def mulhu (x y : BitVec w) : BitVec w :=
  BitVec.ofNat w (x.toNat * y.toNat / 2 ^ w)

/-- MULH rd, rs1, rs2: signed high multiplication.
    Returns upper w bits of the signed 2w-bit product. -/
def mulh (x y : BitVec w) : BitVec w :=
  BitVec.ofInt w (x.toInt * y.toInt / (2 ^ w : Int))

/-- MULHSU rd, rs1, rs2: signed×unsigned high multiplication.
    Returns upper w bits of the mixed-sign 2w-bit product. -/
def mulhsu (x y : BitVec w) : BitVec w :=
  BitVec.ofInt w (x.toInt * (y.toNat : Int) / (2 ^ w : Int))

/-- MULW rd, rs1, rs2 (RV64M): multiply rs1 and rs2, truncate to 32 bits,
    sign-extend to 64 bits.
    rd = signExtend((rs1 * rs2)[31:0]) -/
def mulw (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  ((rs1_val * rs2_val).setWidth 32).signExtend 64

-- ============================================================================
-- Division Extension (RV64M, Format R)
-- ============================================================================

/-- DIV rd, rs1, rs2 (RV64M): signed division truncated toward zero.
    Division by zero returns -1 (all ones).
    Overflow (INT_MIN / -1) returns INT_MIN, handled by BitVec.ofInt wrapping.
    Uses Int.tdiv (truncated toward zero) matching RISC-V semantics.
    Note: Lean's `/` for Int is Euclidean (floors toward -∞), NOT truncated. -/
def sdiv (x y : BitVec 64) : BitVec 64 :=
  if y = (0 : BitVec 64) then BitVec.ofInt 64 (-1)
  else BitVec.ofInt 64 (x.toInt.tdiv y.toInt)

-- ============================================================================
-- Register-register shifts (RV64I, Format R, word variants)
-- ============================================================================

/-- SLLW rd, rs1, rs2 (RV64I): logical left shift of lower 32 bits by rs2[4:0],
    sign-extend the 32-bit result to 64 bits. -/
def sllw (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  ((rs1_val.setWidth 32) <<< (rs2_val.setWidth 5).toNat).signExtend 64

/-- SRA rd, rs1, rs2 (RV64I): arithmetic right shift of full 64-bit value
    by rs2[5:0].
    rd = rs1 >>_arith rs2[5:0] -/
def sra (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  rs1_val.sshiftRight (rs2_val.setWidth 6).toNat

/-- SRLW rd, rs1, rs2 (RV64I): logical right shift of lower 32 bits by rs2[4:0],
    sign-extend the 32-bit result to 64 bits. -/
def srlw (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  ((rs1_val.setWidth 32) >>> (rs2_val.setWidth 5).toNat).signExtend 64

end Riscv

-- ============================================================================
-- Load/Store helpers and instructions (require State)
-- ============================================================================

-- Nat value of 4 little-endian bytes at addr
-- NOTE: the value at address might be a negative value
def read_word_val (addr : BitVec 64) (s : State) : Nat :=
  (read_mem addr s).toNat +
  (read_mem (addr + 1) s).toNat * 2^8 +
  (read_mem (addr + 2) s).toNat * 2^16 +
  (read_mem (addr + 3) s).toNat * 2^24

-- BitVec wrapper: read a 32-bit word from memory.
def read_word (addr : BitVec 64) (s : State) : BitVec 32 :=
  BitVec.ofNat 32 (read_word_val addr s)

-- Nat value of 2 little-endian bytes at addr
def read_halfword_val (addr : BitVec 64) (s : State) : Nat :=
  (read_mem addr s).toNat +
  (read_mem (addr + 1) s).toNat * 2^8

-- BitVec wrapper: read a 16-bit halfword from memory.
def read_halfword (addr : BitVec 64) (s : State) : BitVec 16 :=
  BitVec.ofNat 16 (read_halfword_val addr s)

-- Write a 32-bit word to memory (little-endian, 4 bytes).
def write_word (addr : BitVec 64) (val : BitVec 32) (s : State) : State :=
  write_mem_bytes 4 addr val s

namespace Riscv

/-- LW rd, offset(rs1) (RV32I/RV64I): load a 32-bit word from memory,
    sign-extend to 64 bits. Panics (sets error) if address is not word-aligned.
    rd = signExtend(mem[addr..addr+3]) -/
def lw (rs1 rd : BitVec 5) (imm : BitVec 12) (s : State) : State :=
  let base := read rs1 s.reg
  let addr := imm.setWidth 64 + base
  if addr &&& 3#64 ≠ 0#64 then { s with error := true }
  else
    let word := read_word addr s
    let new_reg := write rd (word.signExtend 64) s.reg
    { s with reg := new_reg }

/-- LB rd, offset(rs1) (RV32I/RV64I): load a byte from memory,
    sign-extend to 64 bits. No alignment check needed for byte loads.
    rd = signExtend(mem[addr]) -/
def lb (rs1 rd : BitVec 5) (imm : BitVec 12) (s : State) : State :=
  let base := read rs1 s.reg
  let addr := imm.setWidth 64 + base
  let byte := read_mem addr s
  let new_reg := write rd (byte.signExtend 64) s.reg
  { s with reg := new_reg }

/-- LH rd, offset(rs1) (RV32I/RV64I): load a 16-bit halfword from memory,
    sign-extend to 64 bits. Panics (sets error) if address is not halfword-aligned.
    rd = signExtend(mem[addr..addr+1]) -/
def lh (rs1 rd : BitVec 5) (imm : BitVec 12) (s : State) : State :=
  let base := read rs1 s.reg
  let addr := imm.setWidth 64 + base
  if addr &&& 1#64 ≠ 0#64 then { s with error := true }
  else
    let halfword := read_halfword addr s
    let new_reg := write rd (halfword.signExtend 64) s.reg
    { s with reg := new_reg }

/-- SW rs2, offset(rs1) (RV32I/RV64I): store the lower 32 bits of rs2 to memory.
    Panics (sets error) if address is not word-aligned.
    mem[addr..addr+3] = rs2[31:0] -/
def sw (rs1 rs2 : BitVec 5) (imm : BitVec 12) (s : State) : State :=
  let base := read rs1 s.reg -- get value inside rs1
  let addr := imm.setWidth 64 + base -- comput address to be loaded
  if addr &&& 3#64 ≠ 0#64 then { s with error := true }
  else
    let word := (read rs2 s.reg).setWidth 32
    write_word addr word s

-- ============================================================================
-- CSR Instructions (RV64 Zicsr)
-- ============================================================================

/-- CSRRW rd, csr, rs1: atomically read CSR into rd and write rs1 to CSR.
    If rd = x0, the read is suppressed (write-only). -/
def csrrw (rs1 rd : BitVec 5) (csr_addr : BitVec 12) (s : State) : State :=
  let rs1_val := read rs1 s.reg
  let old_csr := read_csr csr_addr s
  let s := write_csr csr_addr rs1_val s
  if rd = 0#5 then s
  else { s with reg := write rd old_csr s.reg }

/-- ECALL (RV64, Machine Mode): environment call from U/S/M-mode.
    Saves current PC to mepc, sets mcause to 11 (environment call from M-mode),
    clears mtval, sets MPP bits in mstatus, and jumps to mtvec. -/
def ecall (s : State) : State :=
  let s := write_csr CSR_MEPC s.pc s
  let s := write_csr CSR_MCAUSE 11#64 s
  let s := write_csr CSR_MTVAL 0#64 s
  let s := write_csr CSR_MSTATUS (read_csr CSR_MSTATUS s ||| (3#64 <<< 11)) s
  { s with pc := read_csr CSR_MTVEC s }

-- ============================================================================
-- Advice (virtual) instructions — load from advice tape
-- ============================================================================

/-- ADVICELB: load 1 byte from the advice tape, sign-extend to 64 bits. -/
def advicelb (rd : BitVec 5) (advice : BitVec 8) (s : State) : State :=
  { s with reg := write rd (advice.signExtend 64) s.reg }

/-- ADVICELH: load 2 bytes from the advice tape, sign-extend to 64 bits. -/
def advicelh (rd : BitVec 5) (advice : BitVec 16) (s : State) : State :=
  { s with reg := write rd (advice.signExtend 64) s.reg }

/-- ADVICELW: load 4 bytes from the advice tape, sign-extend to 64 bits. -/
def advicelw (rd : BitVec 5) (advice : BitVec 32) (s : State) : State :=
  { s with reg := write rd (advice.signExtend 64) s.reg }

/-- ADVICELD: load 8 bytes from the advice tape into rd. -/
def adviceld (rd : BitVec 5) (advice : BitVec 64) (s : State) : State :=
  { s with reg := write rd advice s.reg }

end Riscv
