import JoltBytecode.EmbeddedSailJoltState.Defs

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

def vreg_SLLI (vd vs1 : BitVec 7) (shamt : BitVec 6) : JoltMonad ExecutionResult := do
  let x ← readVReg vs1
  writeVReg vd (shift_bits_left x shamt)
  pure RETIRE_SUCCESS

def vreg_SRL (vd vs1 vs2 : BitVec 7) : JoltMonad ExecutionResult := do
  let x ← readVReg vs1
  let y ← readVReg vs2
  writeVReg vd (shift_bits_right x (Sail.BitVec.extractLsb y 5 0))
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

end
