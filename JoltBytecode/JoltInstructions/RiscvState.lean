import JoltBytecode.JoltInstructions.JoltState

/-!
# RiscvState: RISC-V State Matching Jolt's Register Layout

Same structure as JoltState — CSRs live in registers 34-39,
no separate CsrFile. This avoids the round-trip mismatch
`s.toJoltState.toState.csr ≠ s.csr` for unsupported CSRs.

`JoltState.toRiscvState` projects by keeping persistent registers (0-39)
and zeroing transient temporaries (40-127).
-/

/-- RISC-V state matching Jolt's register layout.
    CSRs embedded in registers 34-39, no separate CsrFile. -/
@[ext]
structure RiscvState where
  mem   : Memory
  reg   : JoltRegFile := fun _ => 0#64
  pc    : BitVec 64 := 0#64
  error : Bool := false

-- ============================================================================
-- Projection: JoltState → RiscvState
-- ============================================================================

/-- Project JoltState to RiscvState: keep persistent registers (0-39),
    zero out transient temporaries (40-127). -/
def JoltState.toRiscvState (js : JoltState) : RiscvState where
  mem   := js.mem
  reg   := fun r => if r.toNat < 40 then read r js.reg else 0#64
  pc    := js.pc
  error := js.error

-- ============================================================================
-- Simp lemmas for toRiscvState projections
-- ============================================================================

@[simp] lemma toRiscvState_mem (js : JoltState) :
    js.toRiscvState.mem = js.mem := rfl

@[simp] lemma toRiscvState_pc (js : JoltState) :
    js.toRiscvState.pc = js.pc := rfl

@[simp] lemma toRiscvState_error (js : JoltState) :
    js.toRiscvState.error = js.error := rfl

@[simp] lemma toRiscvState_reg_embedReg (js : JoltState) (r : BitVec 5) :
    js.toRiscvState.reg (embedReg r) = read (embedReg r) js.reg := by
  simp only [JoltState.toRiscvState, embedReg_toNat_lt]
  have : (embedReg r).toNat < 40 := by have := embedReg_toNat_lt r; omega
  simp [this]

@[simp] lemma toRiscvState_reg_lt40 (js : JoltState) (r : BitVec 7) (h : r.toNat < 40) :
    js.toRiscvState.reg r = read r js.reg := by
  simp [JoltState.toRiscvState, h]

@[simp] lemma toRiscvState_reg_ge40 (js : JoltState) (r : BitVec 7) (h : r.toNat ≥ 40) :
    js.toRiscvState.reg r = 0#64 := by
  simp only [JoltState.toRiscvState]
  have : ¬ (r.toNat < 40) := by omega
  simp [this]

-- ============================================================================
-- Memory helpers on RiscvState
-- ============================================================================

def riscv_read_mem (addr : BitVec 64) (s : RiscvState) : BitVec 8 :=
  read addr s.mem

def riscv_read_word_val (addr : BitVec 64) (s : RiscvState) : Nat :=
  (riscv_read_mem addr s).toNat +
  (riscv_read_mem (addr + 1) s).toNat * 2^8 +
  (riscv_read_mem (addr + 2) s).toNat * 2^16 +
  (riscv_read_mem (addr + 3) s).toNat * 2^24

def riscv_read_word (addr : BitVec 64) (s : RiscvState) : BitVec 32 :=
  BitVec.ofNat 32 (riscv_read_word_val addr s)

def riscv_read_dword_val (addr : BitVec 64) (s : RiscvState) : Nat :=
  riscv_read_word_val addr s + riscv_read_word_val (addr + 4) s * 2^32

def riscv_read_dword (addr : BitVec 64) (s : RiscvState) : BitVec 64 :=
  BitVec.ofNat 64 (riscv_read_dword_val addr s)

-- ============================================================================
-- Bridge: memory reads on toRiscvState = memory reads on JoltState
-- ============================================================================

@[simp] lemma riscv_read_mem_toRiscvState (addr : BitVec 64) (js : JoltState) :
    riscv_read_mem addr js.toRiscvState = jolt_read_mem addr js := by
  simp [riscv_read_mem, jolt_read_mem, JoltState.toRiscvState, _root_.read]

@[simp] lemma riscv_read_word_val_toRiscvState (addr : BitVec 64) (js : JoltState) :
    riscv_read_word_val addr js.toRiscvState = jolt_read_word_val addr js := by
  simp [riscv_read_word_val, jolt_read_word_val, riscv_read_mem_toRiscvState]

@[simp] lemma riscv_read_word_toRiscvState (addr : BitVec 64) (js : JoltState) :
    riscv_read_word addr js.toRiscvState = jolt_read_word addr js := by
  simp [riscv_read_word, jolt_read_word, riscv_read_word_val_toRiscvState]

@[simp] lemma riscv_read_dword_val_toRiscvState (addr : BitVec 64) (js : JoltState) :
    riscv_read_dword_val addr js.toRiscvState = jolt_read_dword_val addr js := by
  simp [riscv_read_dword_val, jolt_read_dword_val, riscv_read_word_val_toRiscvState]

@[simp] lemma riscv_read_dword_toRiscvState (addr : BitVec 64) (js : JoltState) :
    riscv_read_dword addr js.toRiscvState = jolt_read_dword addr js := by
  simp [riscv_read_dword, jolt_read_dword, riscv_read_dword_val_toRiscvState]
