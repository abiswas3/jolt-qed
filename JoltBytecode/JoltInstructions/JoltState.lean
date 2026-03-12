import JoltBytecode.BytecodeExpansions.Common.Cpu
import JoltBytecode.BytecodeExpansions.Common.Riscv

/-!
# Jolt VM State

Models the Jolt virtual machine state with 128 registers (7-bit index),
faithfully representing the Jolt Rust tracer's CPU model.

## Register Layout (from Rust `VirtualRegisterAllocator`)

| Registers | Purpose                                                        |
|-----------|----------------------------------------------------------------|
| 0–31      | Standard RISC-V GPRs                                          |
| 32        | Reservation address for LR.W/SC.W                             |
| 33        | Reservation address for LR.D/SC.D                             |
| 34        | mtvec (trap handler address)                                  |
| 35        | mscratch (trap scratch register)                              |
| 36        | mepc (exception program counter)                              |
| 37        | mcause (trap cause)                                           |
| 38        | mtval (trap value)                                            |
| 39        | mstatus (machine status)                                      |
| 40–46     | Instruction temporaries (allocated per inline sequence)        |
| 47–127    | Inline temporaries (for larger decompositions)                 |

## Rust Reference (common/src/constants.rs)

```rust
pub const RISCV_REGISTER_COUNT: u8 = 32;
pub const VIRTUAL_REGISTER_COUNT: u8 = 96;
pub const REGISTER_COUNT: u8 = 128; // must be a power of 2
```
-/

-- Jolt register file: 128 registers addressed by 7-bit index
abbrev JoltRegFile := DataStore (BitVec 7) (BitVec 64)

-- Jolt VM state: same memory model as RISC-V, but with 128 registers.
-- No separate CSR file — CSRs live in virtual registers 34–39.
@[ext]
structure JoltState where
  mem   : Memory
  reg   : JoltRegFile := fun _ => 0#64
  pc    : BitVec 64 := 0#64
  error : Bool := false

-- ============================================================================
-- Register index embedding
-- ============================================================================

/-- Embed a 5-bit RISC-V register index into the 7-bit Jolt register space.
    Zero-extends: register k (5-bit) maps to register k (7-bit). -/
def embedReg (r : BitVec 5) : BitVec 7 := r.setWidth 7

-- ============================================================================
-- Virtual register constants
-- ============================================================================

-- Reserved virtual registers (persistent across instructions)
def vr_reservation_w : BitVec 7 := 32#7  -- LR.W/SC.W reservation address
def vr_reservation_d : BitVec 7 := 33#7  -- LR.D/SC.D reservation address
def vr_mtvec     : BitVec 7 := 34#7  -- CSR 0x305: trap handler address
def vr_mscratch  : BitVec 7 := 35#7  -- CSR 0x340: trap scratch register
def vr_mepc      : BitVec 7 := 36#7  -- CSR 0x341: exception program counter
def vr_mcause    : BitVec 7 := 37#7  -- CSR 0x342: trap cause
def vr_mtval     : BitVec 7 := 38#7  -- CSR 0x343: trap value
def vr_mstatus   : BitVec 7 := 39#7  -- CSR 0x300: machine status

-- Instruction temporaries (allocated per inline sequence)
def v0_reg : BitVec 7 := 40#7  -- first allocatable temporary

-- ============================================================================
-- CSR ↔ Virtual Register mapping (used by CSRRW/CSRRS instructions)
-- ============================================================================

/-- Map a CSR address to its Jolt virtual register (Option).
    Returns `some vr` for supported CSRs, `none` for unsupported.

    From Rust `VirtualRegisterAllocator::csr_to_virtual_register`. -/
def csrToVReg (csr_addr : BitVec 12) : Option (BitVec 7) :=
  if csr_addr = CSR_MSTATUS  then some vr_mstatus
  else if csr_addr = CSR_MTVEC    then some vr_mtvec
  else if csr_addr = CSR_MSCRATCH then some vr_mscratch
  else if csr_addr = CSR_MEPC     then some vr_mepc
  else if csr_addr = CSR_MCAUSE   then some vr_mcause
  else if csr_addr = CSR_MTVAL    then some vr_mtval
  else none

-- ============================================================================
-- Projection: JoltState → State
-- ============================================================================

/-- Project Jolt state to RISC-V state.
    - Registers 0–31 → RISC-V register file
    - Virtual registers 34–39 → CSR file (for supported CSRs)
    - Unsupported CSRs default to 0. -/
def JoltState.toState (js : JoltState) : State where
  mem   := js.mem
  reg   := fun (r : BitVec 5) => read (embedReg r) js.reg
  csr   := fun (csr_addr : BitVec 12) =>
    match csrToVReg csr_addr with
    | some vr => read vr js.reg
    | none    => 0#64
  pc    := js.pc
  error := js.error

-- ============================================================================
-- Lifting: State → JoltState
-- ============================================================================

/-- Lift RISC-V state to Jolt state.
    - Registers 0–31 from RISC-V register file
    - Registers 34–39 from CSR file
    - All other virtual registers initialized to zero -/
def State.toJoltState (s : State) : JoltState where
  mem   := s.mem
  reg   := fun (r : BitVec 7) =>
    if r.toNat < 32 then read (r.setWidth 5) s.reg
    else if r = vr_mtvec    then read_csr CSR_MTVEC s
    else if r = vr_mscratch then read_csr CSR_MSCRATCH s
    else if r = vr_mepc     then read_csr CSR_MEPC s
    else if r = vr_mcause   then read_csr CSR_MCAUSE s
    else if r = vr_mtval    then read_csr CSR_MTVAL s
    else if r = vr_mstatus  then read_csr CSR_MSTATUS s
    else 0#64
  pc    := s.pc
  error := s.error

-- ============================================================================
-- JoltState read/write operations
-- ============================================================================

def jolt_read_mem (addr : BitVec 64) (js : JoltState) : BitVec 8 :=
  read addr js.mem

def jolt_write_mem (addr : BitVec 64) (val : BitVec 8) (js : JoltState) : JoltState :=
  { js with mem := write addr val js.mem }

-- ============================================================================
-- Roundtrip and projection lemmas
-- ============================================================================

@[simp] lemma embedReg_toNat_lt (r : BitVec 5) : (embedReg r).toNat < 32 := by
  unfold embedReg; simp [BitVec.toNat_setWidth]; omega

private lemma setWidth_7_5_eq (r : BitVec 5) : (r.setWidth 7).setWidth 5 = r := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth]

private lemma setWidth_7_toNat_lt (r : BitVec 5) : (r.setWidth 7).toNat < 32 := by
  simp [BitVec.toNat_setWidth]; omega

@[simp] lemma toJoltState_read_embedReg (s : State) (r : BitVec 5) :
    _root_.read (embedReg r) s.toJoltState.reg = _root_.read r s.reg := by
  simp only [State.toJoltState, embedReg, _root_.read]
  simp only [setWidth_7_toNat_lt, ↓reduceIte, setWidth_7_5_eq]

lemma toState_toJoltState_reg (s : State) (r : BitVec 5) :
    s.toJoltState.toState.reg r = s.reg r := by
  simp only [JoltState.toState, State.toJoltState, embedReg, _root_.read]
  simp only [setWidth_7_toNat_lt, ↓reduceIte, setWidth_7_5_eq]

@[simp] lemma toJoltState_mem (s : State) : s.toJoltState.mem = s.mem := rfl
@[simp] lemma toJoltState_pc (s : State) : s.toJoltState.pc = s.pc := rfl
@[simp] lemma toJoltState_error (s : State) : s.toJoltState.error = s.error := rfl

lemma toState_toJoltState_mem (s : State) :
    s.toJoltState.toState.mem = s.mem := rfl

lemma toState_toJoltState_pc (s : State) :
    s.toJoltState.toState.pc = s.pc := rfl

lemma toState_toJoltState_error (s : State) :
    s.toJoltState.toState.error = s.error := rfl

-- ============================================================================
-- embedReg injectivity and distinctness from virtual registers
-- ============================================================================

lemma embedReg_injective : Function.Injective embedReg := by
  intro a b h; unfold embedReg at h
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt; have hb := b.isLt
  have := congr_arg BitVec.toNat h
  simp [BitVec.toNat_setWidth] at this; omega

lemma embedReg_toNat (r : BitVec 5) : (embedReg r).toNat = r.toNat := by
  unfold embedReg; simp [BitVec.toNat_setWidth]; omega

lemma embedReg_ne_of_ge32 (r : BitVec 5) (vr : BitVec 7) (h : vr.toNat ≥ 32) :
    embedReg r ≠ vr := by
  intro heq; have := embedReg_toNat_lt r; rw [heq] at this; omega

@[simp] lemma embedReg_ne_v0 (r : BitVec 5) : embedReg r ≠ v0_reg :=
  embedReg_ne_of_ge32 r v0_reg (by unfold v0_reg; simp)

@[simp] lemma v0_ne_embedReg (r : BitVec 5) : v0_reg ≠ embedReg r :=
  Ne.symm (embedReg_ne_v0 r)

/-- csrToVReg always returns a register with toNat ≥ 32 (when supported). -/
lemma csrToVReg_ge32 (csr_addr : BitVec 12) (vr : BitVec 7)
    (h : csrToVReg csr_addr = some vr) : vr.toNat ≥ 32 := by
  unfold csrToVReg CSR_MSTATUS CSR_MTVEC CSR_MSCRATCH CSR_MEPC CSR_MCAUSE CSR_MTVAL at h
  split at h <;> (try split at h) <;> (try split at h)
    <;> (try split at h) <;> (try split at h) <;> (try split at h)
  all_goals (
    first
    | (injection h with h; rw [← h]; simp [vr_mstatus, vr_mtvec, vr_mscratch, vr_mepc, vr_mcause, vr_mtval])
    | (exact absurd h (by simp))
  )

/-- Writing to a GPR (embedReg r) doesn't change the CSR projection. -/
lemma toState_csr_write_embedReg (js : JoltState) (r : BitVec 5) (v : BitVec 64) :
    ({ js with reg := write (embedReg r) v js.reg } : JoltState).toState.csr = js.toState.csr := by
  funext csr_addr
  simp only [JoltState.toState, _root_.read, write]
  cases h : csrToVReg csr_addr with
  | none => rfl
  | some vr =>
    have : vr ≠ embedReg r := by
      intro heq
      have h1 := csrToVReg_ge32 csr_addr vr h
      have h2 := embedReg_toNat_lt r
      rw [heq] at h1; omega
    simp [this]

-- ============================================================================
-- Projection after register write: the key compositionality lemmas
-- ============================================================================

/-- Writing to a RISC-V register in JoltState, then projecting,
    equals projecting first then writing to the same RISC-V register. -/
lemma toState_write_embedReg (js : JoltState) (r : BitVec 5) (v : BitVec 64) :
    ({ js with reg := write (embedReg r) v js.reg } : JoltState).toState =
    { js.toState with reg := write r v js.toState.reg } := by
  have h_reg : (fun x => _root_.read (embedReg x) (write (embedReg r) v js.reg)) =
               write r v (fun x => _root_.read (embedReg x) js.reg) := by
    funext x; unfold write
    simp only [_root_.read, write]
    by_cases hx : embedReg x = embedReg r
    · have := embedReg_injective hx; simp [this]
    · have hx' : x ≠ r := fun h => hx (congrArg embedReg h)
      simp [hx, hx']
  have h_csr : (fun csr_addr =>
      match csrToVReg csr_addr with
      | some vr => _root_.read vr (write (embedReg r) v js.reg)
      | none => 0#64) =
    (fun csr_addr =>
      match csrToVReg csr_addr with
      | some vr => _root_.read vr js.reg
      | none => 0#64) := by
    funext csr_addr
    cases hc : csrToVReg csr_addr with
    | none => rfl
    | some vr =>
      simp only [_root_.read, write]
      have : vr ≠ embedReg r := by
        intro heq; have h1 := csrToVReg_ge32 csr_addr vr hc
        have h2 := embedReg_toNat_lt r; rw [heq] at h1; omega
      simp [this]
  simp only [JoltState.toState, h_reg, h_csr]

/-- Writing to a virtual register (≥ 32) doesn't affect projected registers. -/
lemma toState_reg_write_virtual (js : JoltState) (vr : BitVec 7) (v : BitVec 64)
    (h : vr.toNat ≥ 32) :
    ({ js with reg := write vr v js.reg } : JoltState).toState.reg = js.toState.reg := by
  funext x
  simp only [JoltState.toState, _root_.read, write]
  have : embedReg x ≠ vr := by
    intro heq; have := embedReg_toNat_lt x; rw [heq] at this; omega
  simp [this]

/-- Writing to v0_reg doesn't affect the projected RISC-V register file. -/
lemma toState_reg_write_v0 (js : JoltState) (v : BitVec 64) :
    ({ js with reg := write v0_reg v js.reg } : JoltState).toState.reg = js.toState.reg :=
  toState_reg_write_virtual js v0_reg v (by unfold v0_reg; simp)

-- ============================================================================
-- DataStore write interaction lemmas
-- ============================================================================

/-- Writing twice to the same address: the second write wins. -/
@[simp] lemma write_write_eq {α β : Type} [DecidableEq α] (a : α) (v1 v2 : β) (ds : DataStore α β) :
    write a v2 (write a v1 ds) = write a v2 ds := by
  funext x; unfold write; split <;> simp_all

/-- Writing to different addresses: order doesn't matter for reads. -/
lemma write_write_ne {α β : Type} [DecidableEq α] (a1 a2 : α) (v1 v2 : β) (ds : DataStore α β)
    (h : a1 ≠ a2) :
    _root_.read a1 (write a2 v2 (write a1 v1 ds)) = v1 := by
  unfold _root_.read write; simp [h, Ne.symm h]

-- ============================================================================
-- Simp lemmas for JoltState field access after register writes
-- ============================================================================

@[simp] lemma joltState_with_reg_mem (js : JoltState) (f : JoltRegFile) :
    { js with reg := f }.mem = js.mem := rfl

@[simp] lemma joltState_with_reg_pc (js : JoltState) (f : JoltRegFile) :
    { js with reg := f }.pc = js.pc := rfl

@[simp] lemma joltState_with_reg_error (js : JoltState) (f : JoltRegFile) :
    { js with reg := f }.error = js.error := rfl

@[simp] lemma joltState_with_error_mem (js : JoltState) (b : Bool) :
    { js with error := b }.mem = js.mem := rfl

@[simp] lemma joltState_with_error_reg (js : JoltState) (b : Bool) :
    { js with error := b }.reg = js.reg := rfl

@[simp] lemma joltState_with_error_pc (js : JoltState) (b : Bool) :
    { js with error := b }.pc = js.pc := rfl

-- ============================================================================
-- Memory helpers on JoltState
-- ============================================================================

def jolt_read_word_val (addr : BitVec 64) (js : JoltState) : Nat :=
  (jolt_read_mem addr js).toNat +
  (jolt_read_mem (addr + 1) js).toNat * 2^8 +
  (jolt_read_mem (addr + 2) js).toNat * 2^16 +
  (jolt_read_mem (addr + 3) js).toNat * 2^24

def jolt_read_word (addr : BitVec 64) (js : JoltState) : BitVec 32 :=
  BitVec.ofNat 32 (jolt_read_word_val addr js)

def jolt_read_dword_val (addr : BitVec 64) (js : JoltState) : Nat :=
  jolt_read_word_val addr js + jolt_read_word_val (addr + 4) js * 2^32

def jolt_read_dword (addr : BitVec 64) (js : JoltState) : BitVec 64 :=
  BitVec.ofNat 64 (jolt_read_dword_val addr js)

-- ============================================================================
-- Memory equivalence: JoltState ↔ projected State
-- ============================================================================

@[simp] lemma jolt_read_mem_eq_read_mem (addr : BitVec 64) (js : JoltState) :
    jolt_read_mem addr js = read_mem addr js.toState := by
  unfold jolt_read_mem read_mem JoltState.toState _root_.read; rfl

@[simp] lemma jolt_read_word_val_eq (addr : BitVec 64) (js : JoltState) :
    jolt_read_word_val addr js = read_word_val addr js.toState := by
  unfold jolt_read_word_val read_word_val; simp [jolt_read_mem_eq_read_mem]

@[simp] lemma jolt_read_word_eq (addr : BitVec 64) (js : JoltState) :
    jolt_read_word addr js = read_word addr js.toState := by
  unfold jolt_read_word read_word; simp [jolt_read_word_val_eq]

/-- jolt_read_dword only depends on memory, not registers. -/
@[simp] lemma jolt_read_dword_with_reg (addr : BitVec 64) (js : JoltState) (f : JoltRegFile) :
    jolt_read_dword addr { js with reg := f } = jolt_read_dword addr js := rfl
