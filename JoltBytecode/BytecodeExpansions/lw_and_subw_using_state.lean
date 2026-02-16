import Mathlib.Tactic
import Mathlib.Data.BitVec


abbrev ByteDataStore addr_bits := BitVec addr_bits → BitVec 8

abbrev DataStore α β := α → β

def readdata {α β : Type} [DecidableEq α] (a : α) (datastore : DataStore α β) : β :=
  datastore a

-- takes a datastore, an address a, and a new value b (to be written at address a)
-- returns a new datastore that returns the same values as the origianl datastore at all addresses except a, where it returns b
def writedata {α β : Type} [DecidableEq α] (a : α) (b : β) (datastore : DataStore α β) : DataStore α β :=
  fun x => if x = a then b else (datastore x)

abbrev Memory := DataStore (BitVec 64) (BitVec 8)

abbrev RegFile := DataStore (BitVec 5) (BitVec 64)

@[ext]
structure State where
  mem : Memory
  reg : RegFile
  is_error : Bool
  -- flags

def read_mem (addr : BitVec 64) (s : State) : BitVec 8 :=
 readdata addr s.mem

def read_mem_word (addr : BitVec 64) (s : State) : BitVec 32 := 
  (readdata addr s.mem)++(readdata (addr+1) s.mem)++(readdata (addr+2) s.mem)++(readdata (addr+3) s.mem)

def read_mem_dword (addr : BitVec 64) (s : State) : BitVec 64 := 
  (readdata addr s.mem)++(readdata (addr+1) s.mem)++(readdata (addr+2) s.mem)++(readdata (addr+3) s.mem)++(readdata (addr+4) s.mem)++(readdata (addr+5) s.mem)++(readdata (addr+6) s.mem)++(readdata (addr+7) s.mem)

def read_mem_bytes (n : Nat) (addr : BitVec 64) (s : State) : BitVec (n * 8) :=
  match n with
  | 0 => 0#0
  | n' + 1 =>
    let byte := read_mem addr s
    let rest := read_mem_bytes n' (addr + 1#64) s
    (rest ++ byte).cast (by omega)

def write_mem (addr : BitVec 64) (val : BitVec 8) (s : State) : State :=
  let new_mem := writedata addr val s.mem
  { s with mem := new_mem }

def write_mem_bytes (n : Nat) (addr : BitVec 64) (val : BitVec (n * 8)) (s : State) : State :=
  match n with
  | 0 => s
  | n' + 1 =>
    let byte := BitVec.extractLsb' 0 8 val
    let s := write_mem addr byte s
    let val_rest := BitVec.setWidth (n' * 8) (val >>> 8)
    write_mem_bytes n' (addr + 1#64) val_rest s

def riscv_subw (r1 r2 rd : BitVec 5) (s : State) : State := 
  -- TODO set flags
  let r1val := readdata r1 s.reg
  let r2val := readdata r2 s.reg
  let rdval := ((r1val.setWidth 32) - (r2val.setWidth 32)).signExtend 64
  let new_reg := writedata rd rdval s.reg
  { s with reg := new_reg }

def jolt_subw (r1 r2 rd : BitVec 5) (s : State) : State := 
  -- TODO set flags
  let r1val := readdata r1 s.reg
  let r2val := readdata r2 s.reg
  let rdval := ((r1val - r2val).setWidth 32).signExtend 64
  let new_reg := writedata rd rdval s.reg
  { s with reg := new_reg }

theorem setWidth_sub_32 (x y : BitVec 64) :
    (x - y).setWidth 32 = x.setWidth 32 - y.setWidth 32 := by
  bv_omega

theorem jolt_subw_eq_riscv_subw (r1 r2 rd : BitVec 5) (s : State) : riscv_subw r1 r2 rd s = jolt_subw r1 r2 rd s := by
  unfold jolt_subw riscv_subw
  ext1
  . simp only
  . simp
    unfold writedata
    ext1 x
    by_cases h : x = rd
    . simp_all
      congr 2
      rw [setWidth_sub_32]
    . simp_all
  . simp

def riscv_lw (r1 rd : BitVec 5) (imm : BitVec 12) (s : State)  : State :=
  let r1val := readdata r1 s.reg
  let address := ((imm.setWidth 64) + r1val) &&&(-4#64)
  let memval := read_mem_word address s
  let new_reg := writedata rd (memval.signExtend 64) s.reg
  { s with reg := new_reg }

def jolt_lw (r1 rd : BitVec 5) (imm : BitVec 12) (s : State)  : State :=
  let r1val := readdata r1 s.reg
  let v_address := ((imm.setWidth 64) + r1val)&&&(-4#64)
  let v_dword_address := v_address &&& (-8#64)
  let v_dword := read_mem_dword v_dword_address s
  let v_shift := (v_address.shiftLeft 3).setWidth 6
  let rd_val := (v_dword.ushiftRight v_shift.toNat).setWidth 32
  let new_reg := writedata rd (rd_val.signExtend 64) s.reg
  { s with reg := new_reg }

theorem dword_align_eq_of_bits_0_to_2_eq_0 (x : BitVec 64) (h : x[2] = false) (h2 : x &&& 3#64 = 0): x = x &&& (-8#64) := by sorry
theorem word_align_eq_of_bit2_eq_1 (x : BitVec 64) (h : x[2] = true) (h2 : x &&& 3#64 = 0): x - 4 = x &&& (-8#64) := by sorry

theorem foo3 (x : BitVec 64) (h : x[2] = false) (h2 : x &&& 3#64 = 0): (x.toNat <<< 3) % 64 = 0:= by sorry

theorem foo4 (x1 x2 x3 x4 x5 x6 x7 x8: BitVec 8) : BitVec.setWidth 32 (x1 ++ x2 ++ x3 ++ x4 ++ x5 ++ x6 ++x7 ++x8) = x1 ++ x2 ++ x3 ++ x4 := by sorry


theorem foo5 (x : BitVec 64) (h : x[2] = true) (h2 : x &&& 3#64 = 0): (x.toNat <<< 3) % 64 = 32 := by sorry

theorem foo6 (x1 x2 x3 x4 x5 x6 x7 x8: BitVec 8) : BitVec.setWidth 32 ((x1 ++ x2 ++ x3 ++ x4 ++ x5 ++ x6 ++x7 ++x8) >>> 32) = x5 ++ x6 ++ x7 ++ x8 := by sorry

theorem foo7 (x : BitVec 64) (y z : Nat) : x - BitVec.ofNat 64 y + BitVec.ofNat 64 z = (x + BitVec.ofNat 64 (z-y)) := by sorry


theorem read_word_eq_read_dword_shift (addr : BitVec 64) (s : State) (h : addr &&& 3#64 == 0): 
  read_mem_word addr s =
  BitVec.setWidth 32 (read_mem_dword (addr &&& -8#64) s >>> ((addr.toNat <<< 3) % 64))
       := by
    unfold read_mem_word read_mem_dword
    by_cases h2 : addr[2] = true
    . unfold readdata
      simp at h2
      simp at h
      rw [← word_align_eq_of_bit2_eq_1 addr h2 h]
      rw [foo5 addr h2 h]
      rw [foo6]
      simp [foo7]
    . unfold readdata
      simp at h2
      simp at h
      rw [← dword_align_eq_of_bits_0_to_2_eq_0 addr h2 h]
      rw [foo3 addr h2 h]
      simp
      rw [foo4]


theorem jolt_lw_eq_riscv_lw (r1 rd : BitVec 5) (imm : BitVec 12) (s : State) : riscv_lw r1 rd imm s = jolt_lw r1 rd imm s := by
  unfold jolt_lw riscv_lw
  ext1
  . simp only
  . ext1 x
    unfold writedata
    by_cases h : x = rd
    . simp_all only [↓reduceIte, BitVec.reduceNeg, BitVec.shiftLeft_eq,
      BitVec.toNat_setWidth, BitVec.toNat_shiftLeft,
      Nat.reducePow, Nat.reduceDvd, Nat.mod_mod_of_dvd,
      BitVec.ushiftRight_eq]
      congr 1
      -- `apply read_word_eq_read_dword_shift` also works
      let addr := (BitVec.setWidth 64 imm + readdata r1 s.reg)
      exact read_word_eq_read_dword_shift (addr &&& -4#64) s (by rw [BitVec.and_assoc]; simp)
      
    . simp_all
  . simp only
