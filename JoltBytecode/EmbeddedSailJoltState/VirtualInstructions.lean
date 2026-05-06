import JoltBytecode.EmbeddedSailJoltState.JoltISA.Values

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

/-!
# Virtual-register RISC-V primitives

Each `vreg_<INSTR>` mirrors the corresponding RISC-V instruction but
reads/writes `js.vregs` rather than `js.sail.regs`. The arithmetic and
shift operations reuse the exact Sail functions (`shift_bits_left`,
`shift_bits_right`, bitwise operators) that Sail's own `execute_ITYPE`,
`execute_RTYPE`, `execute_SHIFTIOP` use — so the only difference is which
register file the reads and writes target.
-/

def vreg_ANDI (vd vs1 : BitVec 7) (imm : BitVec 12) : JoltMonad ExecutionResult := do
  let x ← readVReg vs1
  writeVReg vd (x &&& sign_extend (m := 64) imm)
  pure RETIRE_SUCCESS

def vreg_XORI (vd vs1 : BitVec 7) (imm : BitVec 12) : JoltMonad ExecutionResult := do
  let x ← readVReg vs1
  writeVReg vd (x ^^^ sign_extend (m := 64) imm)
  pure RETIRE_SUCCESS

-- Sail's SLLI applies extractLsb shamt (log2_xlen-1) 0 before shifting.
-- For BitVec 6 with bounds [5:0] this is identity.
-- Sail's shift instructions apply `extractLsb shamt (log2_xlen-1) 0` to the
-- shift amount before using it. For RV64, log2_xlen = 6, so this extracts
-- bits [5:0] from a 6-bit value — which is identity. Our vreg shift helpers
-- skip this step for simplicity; this lemma bridges the gap so we can rewrite
-- `extractLsb shamt 5 0` to `shamt` when connecting vreg ops to Sail.
@[simp]
theorem extractLsb_6_5_0_id (shamt : BitVec 6) :
    Sail.BitVec.extractLsb shamt 5 0 = shamt := by
  apply BitVec.eq_of_toNat_eq
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
        BitVec.toNat_setWidth, shamt.isLt]

-- Our vreg_SLLI uses `shift_bits_left x shamt` directly.
-- Sail's SLLI uses `shift_bits_left x (extractLsb shamt 5 0)`.
-- These are equal because extractLsb on a 6-bit value with bounds [5:0]
-- is identity (see extractLsb_6_5_0_id above).
@[simp]
theorem shift_bits_left_extractLsb_id (x : BitVec 64) (shamt : BitVec 6) :
    shift_bits_left x (Sail.BitVec.extractLsb shamt 5 0) = shift_bits_left x shamt := by
  rw [extractLsb_6_5_0_id]

-- Same for shift_bits_right: our vreg_SRLI skips the extractLsb that
-- Sail's SRLI applies, but the result is identical.
@[simp]
theorem shift_bits_right_extractLsb_id (x : BitVec 64) (shamt : BitVec 6) :
    shift_bits_right x (Sail.BitVec.extractLsb shamt 5 0) = shift_bits_right x shamt := by
  rw [extractLsb_6_5_0_id]

def vreg_SLLI (vd vs1 : BitVec 7) (shamt : BitVec 6) : JoltMonad ExecutionResult := do
  let x ← readVReg vs1
  writeVReg vd (shift_bits_left x shamt)
  pure RETIRE_SUCCESS

def vreg_SRL (vd vs1 vs2 : BitVec 7) : JoltMonad ExecutionResult := do
  let x ← readVReg vs1
  let y ← readVReg vs2
  writeVReg vd (shift_bits_right x (Sail.BitVec.extractLsb y 5 0))
  pure RETIRE_SUCCESS

def vreg_SRLI (vd vs1 : BitVec 7) (shamt : BitVec 6) : JoltMonad ExecutionResult := do
  let x ← readVReg vs1
  writeVReg vd (shift_bits_right x shamt)
  pure RETIRE_SUCCESS

def vreg_SLL (vd vs1 vs2 : BitVec 7) : JoltMonad ExecutionResult := do
  let x ← readVReg vs1
  let y ← readVReg vs2
  writeVReg vd (shift_bits_left x (Sail.BitVec.extractLsb y 5 0))
  pure RETIRE_SUCCESS

-- LD into a virtual register: reads effective address from vs1, adds the
-- sign-extended offset, invokes Sail's vmem_read_addr pipeline at width 8,
-- and parks the dword in vd. Traps from the pipeline propagate as the
-- returned ExecutionResult.
def vreg_LD (vd vs1 : BitVec 7) (imm : BitVec 12) : JoltMonad ExecutionResult := do
  let base ← readVReg vs1
  let addr := base + sign_extend (m := 64) imm
  match ← liftSail (vmem_read_addr (Virtaddr addr) 0 8 (Load Data) false false false) with
  | .Ok dword =>
      writeVReg vd dword
      pure RETIRE_SUCCESS
  | .Err e => pure e

def vreg_ADDI (vd vs1 : BitVec 7) (imm : BitVec 12) : JoltMonad ExecutionResult := do
  let x ← readVReg vs1
  writeVReg vd (x + sign_extend (m := 64) imm)
  pure RETIRE_SUCCESS

def vreg_ORI (vd vs1 : BitVec 7) (imm : BitVec 12) : JoltMonad ExecutionResult := do
  let x ← readVReg vs1
  writeVReg vd (x ||| sign_extend (m := 64) imm)
  pure RETIRE_SUCCESS

def vreg_XOR (vd vs1 vs2 : BitVec 7) : JoltMonad ExecutionResult := do
  let x ← readVReg vs1
  let y ← readVReg vs2
  writeVReg vd (x ^^^ y)
  pure RETIRE_SUCCESS

def vreg_AND (vd vs1 vs2 : BitVec 7) : JoltMonad ExecutionResult := do
  let x ← readVReg vs1
  let y ← readVReg vs2
  writeVReg vd (x &&& y)
  pure RETIRE_SUCCESS

-- SD from a virtual register: reads effective address from vs1, adds the
-- sign-extended offset, writes the dword from vs2 to memory via Sail's
-- vmem pipeline. Traps propagate as the returned ExecutionResult.
def vreg_SD (vs1 vs2 : BitVec 7) (imm : BitVec 12) : JoltMonad ExecutionResult := do
  let base ← readVReg vs1
  let addr := base + sign_extend (m := 64) imm
  let value ← readVReg vs2
  match ← liftSail (vmem_write_addr (Virtaddr addr) 8 value (Store Data) false false false) with
  | .Ok _ => pure RETIRE_SUCCESS
  | .Err e => pure e

-- ============================================================================
-- Simp lemmas: each pure-arithmetic vreg op unfolds to an explicit
-- `.ok RETIRE_SUCCESS` result where only `vregs` changes and `sail` is
-- preserved. Marked `@[simp]` so the monadic plumbing collapses automatically.
-- ============================================================================

@[simp]
theorem vreg_ANDI_run (vd vs1 : BitVec 7) (imm : BitVec 12) (js : SailJoltState) :
    vreg_ANDI vd vs1 imm js = .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r => if r = vd then
                            js.vregs vs1 &&& sign_extend (m := 64) imm
                          else js.vregs r } := by
  unfold vreg_ANDI
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, writeVReg, get, modify, modifyGet,
             getThe, MonadStateOf.get, MonadStateOf.modifyGet,
             EStateM.get, EStateM.modifyGet]

@[simp]
theorem vreg_XORI_run (vd vs1 : BitVec 7) (imm : BitVec 12) (js : SailJoltState) :
    vreg_XORI vd vs1 imm js = .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r => if r = vd then
                            js.vregs vs1 ^^^ sign_extend (m := 64) imm
                          else js.vregs r } := by
  unfold vreg_XORI
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, writeVReg, get, modify, modifyGet,
             getThe, MonadStateOf.get, MonadStateOf.modifyGet,
             EStateM.get, EStateM.modifyGet]

@[simp]
theorem vreg_SLLI_run (vd vs1 : BitVec 7) (shamt : BitVec 6) (js : SailJoltState) :
    vreg_SLLI vd vs1 shamt js = .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r => if r = vd then
                            shift_bits_left (js.vregs vs1) shamt
                          else js.vregs r } := by
  unfold vreg_SLLI
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, writeVReg, get, modify, modifyGet,
             getThe, MonadStateOf.get, MonadStateOf.modifyGet,
             EStateM.get, EStateM.modifyGet]

@[simp]
theorem vreg_SLL_run (vd vs1 vs2 : BitVec 7) (js : SailJoltState) :
    vreg_SLL vd vs1 vs2 js = .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r => if r = vd then
                            shift_bits_left (js.vregs vs1)
                              (Sail.BitVec.extractLsb (js.vregs vs2) 5 0)
                          else js.vregs r } := by
  unfold vreg_SLL
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, writeVReg, get, modify, modifyGet,
             getThe, MonadStateOf.get, MonadStateOf.modifyGet,
             EStateM.get, EStateM.modifyGet]

@[simp]
theorem vreg_SRLI_run (vd vs1 : BitVec 7) (shamt : BitVec 6) (js : SailJoltState) :
    vreg_SRLI vd vs1 shamt js = .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r => if r = vd then
                            shift_bits_right (js.vregs vs1) shamt
                          else js.vregs r } := by
  unfold vreg_SRLI
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, writeVReg, get, modify, modifyGet,
             getThe, MonadStateOf.get, MonadStateOf.modifyGet,
             EStateM.get, EStateM.modifyGet]

@[simp]
theorem vreg_SRL_run (vd vs1 vs2 : BitVec 7) (js : SailJoltState) :
    vreg_SRL vd vs1 vs2 js = .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r => if r = vd then
                            shift_bits_right (js.vregs vs1)
                              (Sail.BitVec.extractLsb (js.vregs vs2) 5 0)
                          else js.vregs r } := by
  unfold vreg_SRL
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, writeVReg, get, modify, modifyGet,
             getThe, MonadStateOf.get, MonadStateOf.modifyGet,
             EStateM.get, EStateM.modifyGet]

@[simp]
theorem vreg_ORI_run (vd vs1 : BitVec 7) (imm : BitVec 12) (js : SailJoltState) :
    vreg_ORI vd vs1 imm js = .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r => if r = vd then
                            js.vregs vs1 ||| sign_extend (m := 64) imm
                          else js.vregs r } := by
  unfold vreg_ORI
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, writeVReg, get, modify, modifyGet,
             getThe, MonadStateOf.get, MonadStateOf.modifyGet,
             EStateM.get, EStateM.modifyGet]

@[simp]
theorem vreg_XOR_run (vd vs1 vs2 : BitVec 7) (js : SailJoltState) :
    vreg_XOR vd vs1 vs2 js = .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r => if r = vd then
                            js.vregs vs1 ^^^ js.vregs vs2
                          else js.vregs r } := by
  unfold vreg_XOR
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, writeVReg, get, modify, modifyGet,
             getThe, MonadStateOf.get, MonadStateOf.modifyGet,
             EStateM.get, EStateM.modifyGet]

@[simp]
theorem vreg_AND_run (vd vs1 vs2 : BitVec 7) (js : SailJoltState) :
    vreg_AND vd vs1 vs2 js = .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r => if r = vd then
                            js.vregs vs1 &&& js.vregs vs2
                          else js.vregs r } := by
  unfold vreg_AND
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, writeVReg, get, modify, modifyGet,
             getThe, MonadStateOf.get, MonadStateOf.modifyGet,
             EStateM.get, EStateM.modifyGet]

-- Conditional unfold for vreg_LD: under JoltConfig, the Sail pipeline
-- collapses to a direct hashmap dword read. Not @[simp] because it needs
-- hcfg and the pipeline-reduces lemma — clients must rewrite manually.
-- Statement relies on `vmem_read_addr_dword_reduces` defined in Lb.lean
-- (or wherever the pipeline collapse lives).
theorem vreg_LD_run_of_read (vd vs1 : BitVec 7) (imm : BitVec 12)
    (js : SailJoltState) (value : BitVec 64)
    (h :
      vmem_read_addr (Virtaddr (js.vregs vs1 + sign_extend (m := 64) imm)) 0 8 (Load Data) false false false js.sail =
        .ok (Ok value) js.sail) :
    vreg_LD vd vs1 imm js = .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r => if r = vd then value else js.vregs r } := by
  unfold vreg_LD liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, writeVReg, get, modify, modifyGet,
             getThe, MonadStateOf.get, MonadStateOf.modifyGet,
             EStateM.get, EStateM.modifyGet]
  rw [h]
  simp only [EStateM.bind, EStateM.pure, writeVReg, modify, modifyGet,
             MonadStateOf.modifyGet, EStateM.modifyGet]

theorem vreg_SD_run_of_write (vs1 vs2 : BitVec 7) (imm : BitVec 12)
    (js : SailJoltState)
    (h :
      vmem_write_addr (Virtaddr (js.vregs vs1 + sign_extend (m := 64) imm)) 8
        (js.vregs vs2) (Store Data) false false false js.sail =
        .ok (Ok true) js.sail) :
    vreg_SD vs1 vs2 imm js = .ok RETIRE_SUCCESS js := by
  unfold vreg_SD liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, get, getThe, MonadStateOf.get, EStateM.get]
  rw [h]
  simp only [EStateM.bind, EStateM.pure]

theorem vreg_SD_run_of_write_to_state (vs1 vs2 : BitVec 7) (imm : BitVec 12)
    (js : SailJoltState) (s' : SailState)
    (h :
      vmem_write_addr (Virtaddr (js.vregs vs1 + sign_extend (m := 64) imm)) 8
        (js.vregs vs2) (Store Data) false false false js.sail =
        .ok (Ok true) s') :
    vreg_SD vs1 vs2 imm js = .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold vreg_SD liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, get, getThe, MonadStateOf.get, EStateM.get]
  rw [h]
  simp only [EStateM.bind, EStateM.pure]

-- ============================================================================
-- Boundary-crossing combinators (real-register ↔ virtual-register mixes)
-- ============================================================================
-- The pure `vreg_*` ops above all live entirely in virtual-register space.
-- The Jolt load/store bytecode sequences open with one instruction that
-- reads a real source register and writes a virtual register, and close
-- with one that reads virtual and writes a real destination. These two
-- boundary-crossing ops are collected here so the `jolt_*` programs can
-- read one line per bytecode line.

/-- `ADDI vd, rs1, imm`: read the *real* register `rs1`, write the
    virtual register `vd` with `rs1_val + sign_extend imm`. Used as the
    first step of every Jolt load/store sequence. -/
def vreg_ADDI_from_real (vd : BitVec 7) (rs1 : regidx) (imm : BitVec 12) :
    JoltMonad ExecutionResult := do
  let rs1_val ← liftSail (rX_bits rs1)
  writeVReg vd (rs1_val + sign_extend (m := 64) imm)
  pure RETIRE_SUCCESS

/-- `SRAI rd, vs1, shamt`: read the virtual register `vs1`, arithmetic-
    shift right by `shamt`, write the *real* register `rd`. Used as the
    closing step of `jolt_lb` (signed byte load). -/
def vreg_SRAI_to_real (rd : regidx) (vs1 : BitVec 7) (shamt : BitVec 6) :
    JoltMonad ExecutionResult := do
  let v ← readVReg vs1
  liftSail (wX_bits rd (shift_bits_right_arith v shamt))
  pure RETIRE_SUCCESS

/-- `SRLI rd, vs1, shamt`: read the virtual register `vs1`, logical-
    shift right by `shamt`, write the *real* register `rd`. Used as the
    closing step of `jolt_lbu` (unsigned byte load) — differs from
    `vreg_SRAI_to_real` only in the shift direction (zero-fill vs
    sign-fill). -/
def vreg_SRLI_to_real (rd : regidx) (vs1 : BitVec 7) (shamt : BitVec 6) :
    JoltMonad ExecutionResult := do
  let v ← readVReg vs1
  liftSail (wX_bits rd (shift_bits_right v shamt))
  pure RETIRE_SUCCESS

/-- `SRL rd, vs1, vs2`: read virtual `vs1` (the value) and virtual `vs2`
    (the shift register, whose low 6 bits are the shift amount), logical-
    shift right, write the *real* register `rd`. Used in `jolt_lw`,
    between the logic phase's SLLI and the final `VirtualSignExtendWord`. -/
def vreg_SRL_to_real (rd : regidx) (vs1 vs2 : BitVec 7) :
    JoltMonad ExecutionResult := do
  let v ← readVReg vs1
  let shamt ← readVReg vs2
  liftSail (wX_bits rd
    (shift_bits_right v (Sail.BitVec.extractLsb shamt 5 0)))
  pure RETIRE_SUCCESS

/-- `SRAI vd, rs1, shamt`: read the *real* register `rs1`, arithmetic-
    shift right by `shamt`, write the virtual register `vd`. Mirror of
    `vreg_SRAI_to_real` for sequences that start with an SRAI on a real
    source. -/
def vreg_SRAI_from_real (vd : BitVec 7) (rs1 : regidx) (shamt : BitVec 6) :
    JoltMonad ExecutionResult := do
  let v ← liftSail (rX_bits rs1)
  writeVReg vd (shift_bits_right_arith v shamt)
  pure RETIRE_SUCCESS

/-- `ADDI rd, vs1, imm`: read the virtual register `vs1`, add the sign-
    extended immediate, write the *real* register `rd`. Used to move a
    virtual-register result into a real destination register. -/
def vreg_ADDI_to_real (rd : regidx) (vs1 : BitVec 7) (imm : BitVec 12) :
    JoltMonad ExecutionResult := do
  let v ← readVReg vs1
  liftSail (wX_bits rd (v + sign_extend (m := 64) imm))
  pure RETIRE_SUCCESS

/-- `VirtualMovsign vd, rs1, 0`: read real `rs1`, write virtual `vd`. -/
def vreg_movsign_from_real (vd : BitVec 7) (rs1 : regidx) : JoltMonad ExecutionResult := do
  let x ← liftSail (rX_bits rs1)
  writeVReg vd (jolt_movsign_value x)
  pure RETIRE_SUCCESS

theorem vreg_movsign_from_real_run (vd : BitVec 7) (rs1 : regidx)
    (js : SailJoltState) (x : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok x js.sail) :
    vreg_movsign_from_real vd rs1 js = .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r => if r = vd then jolt_movsign_value x else js.vregs r } := by
  unfold vreg_movsign_from_real liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run, hrs1,
    readVReg, writeVReg, get, modify, modifyGet, getThe,
    MonadStateOf.get, MonadStateOf.modifyGet, EStateM.get, EStateM.modifyGet]

/-- `ADD vd, vs1, vs2`: virtual-register two-operand 64-bit add. -/
def vreg_ADD (vd vs1 vs2 : BitVec 7) : JoltMonad ExecutionResult := do
  let x ← readVReg vs1
  let y ← readVReg vs2
  writeVReg vd (x + y)
  pure RETIRE_SUCCESS

/-- `SUB vd, vs1, vs2`: virtual-register two-operand 64-bit subtract. -/
def vreg_SUB (vd vs1 vs2 : BitVec 7) : JoltMonad ExecutionResult := do
  let x ← readVReg vs1
  let y ← readVReg vs2
  writeVReg vd (x - y)
  pure RETIRE_SUCCESS

/-- `MUL vd, vs1, vs2`: virtual-register two-operand 64-bit multiply
    (low half). -/
def vreg_MUL (vd vs1 vs2 : BitVec 7) : JoltMonad ExecutionResult := do
  let x ← readVReg vs1
  let y ← readVReg vs2
  writeVReg vd (x * y)
  pure RETIRE_SUCCESS

/-- `XOR vd, rs1, vs2`: read real `rs1` and virtual `vs2`, write virtual `vd`. -/
def vreg_XOR_from_real_vs1 (vd : BitVec 7) (rs1 : regidx) (vs2 : BitVec 7) :
    JoltMonad ExecutionResult := do
  let x ← liftSail (rX_bits rs1)
  let y ← readVReg vs2
  writeVReg vd (x ^^^ y)
  pure RETIRE_SUCCESS

/-- `MUL vd, vs1, rs2`: multiply virtual `vs1` by *real* `rs2`, write
    virtual `vd`. Used by DIVU's `quotient * divisor` step. -/
def vreg_MUL_from_real_vs2 (vd vs1 : BitVec 7) (rs2 : regidx) :
    JoltMonad ExecutionResult := do
  let x ← readVReg vs1
  let y ← liftSail (rX_bits rs2)
  writeVReg vd (x * y)
  pure RETIRE_SUCCESS

/-- `MULHU vd, rs1, rs2`: read real sources, write virtual `vd`. -/
def vreg_MULHU_from_real (vd : BitVec 7) (rs1 rs2 : regidx) : JoltMonad ExecutionResult := do
  let x ← liftSail (rX_bits rs1)
  let y ← liftSail (rX_bits rs2)
  writeVReg vd (jolt_mulhu_value x y)
  pure RETIRE_SUCCESS

theorem vreg_MULHU_from_real_run (vd : BitVec 7) (rs1 rs2 : regidx)
    (js : SailJoltState) (x y : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok x js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok y js.sail) :
    vreg_MULHU_from_real vd rs1 rs2 js = .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r => if r = vd then jolt_mulhu_value x y else js.vregs r } := by
  unfold vreg_MULHU_from_real liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run, hrs1, hrs2,
    readVReg, writeVReg, get, modify, modifyGet, getThe,
    MonadStateOf.get, MonadStateOf.modifyGet, EStateM.get, EStateM.modifyGet]

/-- `MULHU vd, vs1, rs2`: unsigned-high multiply of virtual `vs1` and real
    `rs2`, write virtual `vd`. -/
def vreg_MULHU_from_real_vs2 (vd vs1 : BitVec 7) (rs2 : regidx) :
    JoltMonad ExecutionResult := do
  let x ← readVReg vs1
  let y ← liftSail (rX_bits rs2)
  writeVReg vd (jolt_mulhu_value x y)
  pure RETIRE_SUCCESS

/-- `SUB vd, rs1, vs2`: subtract virtual `vs2` from *real* `rs1`, write
    virtual `vd`. Used by DIVU's `dividend - q*d` step. -/
def vreg_SUB_from_real_vs1 (vd : BitVec 7) (rs1 : regidx) (vs2 : BitVec 7) :
    JoltMonad ExecutionResult := do
  let x ← liftSail (rX_bits rs1)
  let y ← readVReg vs2
  writeVReg vd (x - y)
  pure RETIRE_SUCCESS

/-- `MULH vd, vs1, vs2`: virtual-register signed high multiply — upper
    64 bits of the 128-bit signed product. -/
def vreg_MULH (vd vs1 vs2 : BitVec 7) : JoltMonad ExecutionResult := do
  let x ← readVReg vs1
  let y ← readVReg vs2
  writeVReg vd (mulhs x y)
  pure RETIRE_SUCCESS

/-- `SLTU vd, vs1, vs2`: virtual-register unsigned less-than. -/
def vreg_SLTU (vd vs1 vs2 : BitVec 7) : JoltMonad ExecutionResult := do
  let x ← readVReg vs1
  let y ← readVReg vs2
  writeVReg vd (jolt_sltu_value x y)
  pure RETIRE_SUCCESS

/-- `ADD rd, vs1, vs2`: read virtual sources, write real `rd`. -/
def vreg_ADD_to_real (rd : regidx) (vs1 vs2 : BitVec 7) : JoltMonad ExecutionResult := do
  let x ← readVReg vs1
  let y ← readVReg vs2
  liftSail (wX_bits rd (x + y))
  pure RETIRE_SUCCESS

theorem vreg_ADD_to_real_run (rd : regidx) (vs1 vs2 : BitVec 7)
    (js : SailJoltState) (s' : SailState)
    (hw : wX_bits rd (js.vregs vs1 + js.vregs vs2) js.sail = .ok () s') :
    (vreg_ADD_to_real rd vs1 vs2).run js = .ok RETIRE_SUCCESS
      { sail := s'
        vregs := js.vregs } := by
  unfold vreg_ADD_to_real liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    readVReg, writeVReg, get, modify, modifyGet, getThe,
    MonadStateOf.get, MonadStateOf.modifyGet, EStateM.get, EStateM.modifyGet]
  rw [hw]

/-- `SRAI vd, vs1, shamt`: virtual-register arithmetic right shift by
    immediate. -/
def vreg_SRAI (vd vs1 : BitVec 7) (shamt : BitVec 6) :
    JoltMonad ExecutionResult := do
  let x ← readVReg vs1
  writeVReg vd (shift_bits_right_arith x shamt)
  pure RETIRE_SUCCESS

-- ============================================================================
-- Generic constraint / advice-load primitives
-- ============================================================================
-- These aren't RISC-V arithmetic ops; they're Jolt-ISA control-plane
-- primitives used by constraint-verified expansions (advice-verified
-- DIV, equality checks between intermediate values, etc.). They are
-- generic — usable by any expansion, not just the DIV family — so they
-- live alongside the hardware ops rather than under a family-specific
-- directory.

/-- `VirtualAdvice vd, advice`: write an oracle-provided value into a
    virtual register. No failure path. -/
def vreg_advice (vd : BitVec 7) (advice : BitVec 64) : JoltMonad ExecutionResult := do
  writeVReg vd advice
  pure RETIRE_SUCCESS

/-- `VirtualAssertEQ va, vb`: asserts two virtual registers are equal.
    Throws `Error.Assertion` otherwise. -/
def vreg_assert_eq (va vb : BitVec 7) : JoltMonad ExecutionResult := do
  let a ← readVReg va
  let b ← readVReg vb
  if a = b then pure RETIRE_SUCCESS
  else throw (Error.Assertion "VirtualAssertEQ")

/-- `VirtualAssertEQ va, rb`: asserts a virtual register equals a real
    register. -/
def vreg_assert_eq_real (va : BitVec 7) (rb : regidx) : JoltMonad ExecutionResult := do
  let a ← readVReg va
  let b ← liftSail (rX_bits rb)
  if a = b then pure RETIRE_SUCCESS
  else throw (Error.Assertion "VirtualAssertEQ (vreg vs real)")

end
