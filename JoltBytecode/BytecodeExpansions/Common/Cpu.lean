import Mathlib.Tactic

-- This models a general object that stores data
-- The locations are of type α; and the values are of type β
abbrev DataStore α β := α → β

-- In Jolt Memory has
-- α : BitVec 64
-- β : Bitvec 8
abbrev Memory := DataStore (BitVec 64) (BitVec 8)

-- The RISC-V ISA has 32 general purpose registers
-- α : BitVec 64
-- β : Bitvec 8
abbrev RegFile := DataStore (BitVec 5) (BitVec 64)


-- This models a data store where the input is a bit vector and the output
-- is a byte of data (more specifically a bit vector of size 8).
abbrev ByteDataStore addr_bits := BitVec addr_bits → BitVec 8

-- Given a location of type α, return what is stored in the store at the location α.
def read {α β : Type} [DecidableEq α] (a : α) (datastore : DataStore α β) : β :=
  datastore a

-- takes a datastore, an address a, and a new value b (to be written at address a)
-- returns a new datastore that returns the same values as the origianl datastore at
-- all addresses except a, where it returns b
def write {α β : Type} [DecidableEq α] (a : α) (b : β) (datastore : DataStore α β) : DataStore α β :=
  fun x => if x = a then b else (datastore x)

-- The simplified state of a computer
-- Memory
-- Register
-- Prpgram Counter
-- Flags
@[ext]
structure State where
  mem : Memory
  reg : RegFile
  error : Bool := false
  -- pc

-- Read 8 Bytes from memory
def read_mem (addr : BitVec 64) (s : State) : BitVec 8 :=
  read addr s.mem

-- Write 8 Bytes To memory
def write_mem (addr : BitVec 64) (val : BitVec 8) (s : State) : State :=
  let new_mem := write addr val s.mem
  { s with mem := new_mem }


-- Read n bytes from memory (defined recursively)
def read_mem_bytes (n : Nat) (addr : BitVec 64) (s : State) : BitVec (n * 8) :=
  match n with
  | 0 => 0#0
  | n' + 1 =>
    let byte := read_mem addr s
    let rest := read_mem_bytes n' (addr + 1#64) s
    (rest ++ byte).cast (by omega)

-- Write n bytes to memory (defined recursively)
def write_mem_bytes (n : Nat) (addr : BitVec 64) (val : BitVec (n * 8)) (s : State) : State :=
  match n with
  | 0 => s
  | n' + 1 =>
    let byte := BitVec.extractLsb' 0 8 val
    let s := write_mem addr byte s
    let val_rest := BitVec.setWidth (n' * 8) (val >>> 8)
    write_mem_bytes n' (addr + 1#64) val_rest s
