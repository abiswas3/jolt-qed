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

-- CSR address space is 12-bit in RISC-V (4096 possible CSRs)
abbrev CsrFile := DataStore (BitVec 12) (BitVec 64)


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
-- Componentwise equality -> Equality Of State
@[ext]
structure State where
  mem : Memory
  reg : RegFile
  csr : CsrFile := fun _ => 0#64
  error : Bool := false

-- ============================================================================
-- DataStore read/write interaction lemmas
-- ============================================================================

@[simp] lemma read_write_eq {α β : Type} [DecidableEq α] (a : α) (b : β) (ds : DataStore α β) :
    _root_.read a (_root_.write a b ds) = b := by
  unfold _root_.read _root_.write; simp only [↓reduceIte]

@[simp] lemma read_write_ne {α β : Type} [DecidableEq α] (a₁ a₂ : α) (b : β) (ds : DataStore α β)
    (h : a₂ ≠ a₁) :
    _root_.read a₂ (_root_.write a₁ b ds) = _root_.read a₂ ds := by
  unfold _root_.read _root_.write; simp [h]

lemma write_read_id {α β : Type} [DecidableEq α] (a : α) (ds : DataStore α β) :
    _root_.write a (_root_.read a ds) ds = ds := by
  unfold _root_.write _root_.read; funext x; simp; intro h; rw [h]

-- ============================================================================
-- Memory read/write operations
-- ============================================================================

-- Read a byte from memory
def read_mem (addr : BitVec 64) (s : State) : BitVec 8 :=
  read addr s.mem

-- Write a byte to memory
def write_mem (addr : BitVec 64) (val : BitVec 8) (s : State) : State :=
  let new_mem := write addr val s.mem
  { s with mem := new_mem }

-- write_mem preserves reg and error
@[simp] lemma write_mem_reg (a : BitVec 64) (v : BitVec 8) (s : State) :
    (write_mem a v s).reg = s.reg := by unfold write_mem; simp only

@[simp] lemma write_mem_error (a : BitVec 64) (v : BitVec 8) (s : State) :
    (write_mem a v s).error = s.error := by unfold write_mem; simp only

-- read_mem / write_mem interaction
@[simp] lemma read_mem_write_mem_eq (a : BitVec 64) (v : BitVec 8) (s : State) :
    read_mem a (write_mem a v s) = v := by
  unfold read_mem write_mem; simp [read_write_eq]

@[simp] lemma read_mem_write_mem_ne (a₁ a₂ : BitVec 64) (v : BitVec 8) (s : State)
    (h : a₂ ≠ a₁) :
    read_mem a₂ (write_mem a₁ v s) = read_mem a₂ s := by
  unfold read_mem write_mem; simp [read_write_ne _ _ _ _ h]

-- Writing back the same byte is identity
lemma write_mem_id (addr : BitVec 64) (s : State) :
    write_mem addr (read_mem addr s) s = s := by
  unfold write_mem read_mem
  simp [write_read_id]


-- ============================================================================
-- CSR read/write operations
-- ============================================================================

-- Read a CSR value
def read_csr (addr : BitVec 12) (s : State) : BitVec 64 :=
  read addr s.csr

-- Write a CSR value
def write_csr (addr : BitVec 12) (val : BitVec 64) (s : State) : State :=
  { s with csr := write addr val s.csr }

-- write_csr preserves reg, mem, error
@[simp] lemma write_csr_reg (a : BitVec 12) (v : BitVec 64) (s : State) :
    (write_csr a v s).reg = s.reg := by unfold write_csr; simp only

@[simp] lemma write_csr_mem (a : BitVec 12) (v : BitVec 64) (s : State) :
    (write_csr a v s).mem = s.mem := by unfold write_csr; simp only

@[simp] lemma write_csr_error (a : BitVec 12) (v : BitVec 64) (s : State) :
    (write_csr a v s).error = s.error := by unfold write_csr; simp only

-- read_csr / write_csr interaction
@[simp] lemma read_csr_write_csr_eq (a : BitVec 12) (v : BitVec 64) (s : State) :
    read_csr a (write_csr a v s) = v := by
  unfold read_csr write_csr; simp [read_write_eq]

@[simp] lemma read_csr_write_csr_ne (a₁ a₂ : BitVec 12) (v : BitVec 64) (s : State)
    (h : a₂ ≠ a₁) :
    read_csr a₂ (write_csr a₁ v s) = read_csr a₂ s := by
  unfold read_csr write_csr; simp [read_write_ne _ _ _ _ h]

-- write_mem preserves csr
@[simp] lemma write_mem_csr (a : BitVec 64) (v : BitVec 8) (s : State) :
    (write_mem a v s).csr = s.csr := by unfold write_mem; simp only

-- ============================================================================
-- CSR address constants (supported by Jolt)
-- ============================================================================

def CSR_MSTATUS  : BitVec 12 := 0x300#12
def CSR_MTVEC    : BitVec 12 := 0x305#12
def CSR_MSCRATCH : BitVec 12 := 0x340#12
def CSR_MEPC     : BitVec 12 := 0x341#12
def CSR_MCAUSE   : BitVec 12 := 0x342#12
def CSR_MTVAL    : BitVec 12 := 0x343#12

-- NOTE: Currently not used in the code
-- Read n bytes from memory (defined recursively)
def read_mem_bytes (n : Nat) (addr : BitVec 64) (s : State) : BitVec (n * 8) :=
  match n with
  | 0 => 0#0
  | n' + 1 =>
    let byte := read_mem addr s
    let rest := read_mem_bytes n' (addr + 1#64) s
    (rest ++ byte).cast (by omega)

-- NOTE: Currently not used in the code
-- Write n bytes to memory (defined recursively)
def write_mem_bytes (n : Nat) (addr : BitVec 64) (val : BitVec (n * 8)) (s : State) : State :=
  match n with
  | 0 => s
  | n' + 1 =>
    let byte := BitVec.extractLsb' 0 8 val
    let s := write_mem addr byte s
    let val_rest := BitVec.setWidth (n' * 8) (val >>> 8)
    write_mem_bytes n' (addr + 1#64) val_rest s

-- write_mem_bytes preserves reg and error
@[simp] lemma write_mem_bytes_reg (n : Nat) (addr : BitVec 64) (val : BitVec (n * 8)) (s : State) :
    (write_mem_bytes n addr val s).reg = s.reg := by
  induction n generalizing addr s with
  | zero => unfold write_mem_bytes; rfl
  | succ n ih => unfold write_mem_bytes; simp [ih]

@[simp] lemma write_mem_bytes_error (n : Nat) (addr : BitVec 64) (val : BitVec (n * 8)) (s : State) :
    (write_mem_bytes n addr val s).error = s.error := by
  induction n generalizing addr s with
  | zero => unfold write_mem_bytes; rfl
  | succ n ih => unfold write_mem_bytes; simp [ih]

@[simp] lemma write_mem_bytes_csr (n : Nat) (addr : BitVec 64) (val : BitVec (n * 8)) (s : State) :
    (write_mem_bytes n addr val s).csr = s.csr := by
  induction n generalizing addr s with
  | zero => unfold write_mem_bytes; rfl
  | succ n ih => unfold write_mem_bytes; simp [ih]

-- Reading outside the write range returns the original value.
lemma read_mem_write_mem_bytes_outside (n : Nat) (addr : BitVec 64) (val : BitVec (n * 8))
    (s : State) (a : BitVec 64)
    (h : ∀ (k : Nat), k < n → a ≠ addr + BitVec.ofNat 64 k) :
    read_mem a (write_mem_bytes n addr val s) = read_mem a s := by
  induction n generalizing addr s with
  | zero => unfold write_mem_bytes; rfl
  | succ n ih =>
    unfold write_mem_bytes
    dsimp only
    have h0 : a ≠ addr := by have := h 0 (Nat.zero_lt_succ n); simpa using this
    trans (read_mem a (write_mem addr (BitVec.extractLsb' 0 8 val) s))
    · apply ih
      intro k hk
      have hk1 := h (k + 1) (by omega)
      intro heq; apply hk1
      rw [heq]; bv_omega
    · exact read_mem_write_mem_ne addr a _ s h0
