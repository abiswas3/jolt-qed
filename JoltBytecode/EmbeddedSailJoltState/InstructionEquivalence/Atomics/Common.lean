import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
import JoltBytecode.EmbeddedSailJoltState.MemoryUtils
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Primitives

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace Atomics

/-!
# Shared helpers for atomic instruction expansions

The definitions in this file are shared by AMO bytecode proofs. They separate
the normal load/store assumptions used by Jolt's expansion from the atomic
access assumptions used by Sail's native AMO semantics.
-/

/-- Bare virtual-memory translation for the normal store used by Jolt bytecode
expansions. -/
structure StoreBareTranslation (addr : BitVec 64) (s : SailState) : Prop where
  translate : translateAddr (Virtaddr addr) (Store Data) s =
    .ok (Ok (physaddr.Physaddr addr, init_ext_ptw)) s

/-- Ordinary non-MMIO physical store memory for the normal store used by Jolt
bytecode expansions. -/
structure FlatStoreMem (addr : BitVec 64) (width : Nat) (s : SailState) : Prop where
  pmp : phys_access_check (Store Data) Privilege.Machine
    (physaddr.Physaddr addr) width false s = .ok none s
  mmio : within_mmio_writable (physaddr.Physaddr addr) width s = .ok false s

/-- Bare virtual-memory translation for Sail's native AMO access. -/
structure AtomicBareTranslation (op : amoop) (addr : BitVec 64) (s : SailState) :
    Prop where
  translate : translateAddr (Virtaddr addr) (Atomic (op, Data, Data)) s =
    .ok (Ok (physaddr.Physaddr addr, init_ext_ptw)) s

/-- Ordinary non-MMIO physical memory for Sail's native AMO read and write.
The final Boolean passed to `phys_access_check` is `true`, matching the
reservation/conditional flag used by `execute_AMO`. -/
structure FlatAtomicMem (op : amoop) (addr : BitVec 64) (width : Nat)
    (s : SailState) : Prop where
  pmp : phys_access_check (Atomic (op, Data, Data)) Privilege.Machine
    (physaddr.Physaddr addr) width true s = .ok none s
  readable : within_mmio_readable (physaddr.Physaddr addr) width s = .ok false s
  writable : within_mmio_writable (physaddr.Physaddr addr) width s = .ok false s

/-- `LD vd, imm(rs1)`, where `rs1` is a real register and `vd` is virtual. -/
def vreg_LD_from_real (vd : BitVec 7) (rs1 : regidx) (imm : BitVec 12) :
    JoltMonad ExecutionResult := do
  let base ← liftSail (rX_bits rs1)
  let addr := base + sign_extend (m := 64) imm
  match ← liftSail (vmem_read_addr (Virtaddr addr) 0 8 (Load Data) false false false) with
  | .Ok dword =>
      writeVReg vd dword
      pure RETIRE_SUCCESS
  | .Err e => pure e

/-- `SD vs2, imm(rs1)`, where `rs1` is a real base register and `vs2` is
virtual. -/
def vreg_SD_from_real (rs1 : regidx) (vs2 : BitVec 7) (imm : BitVec 12) :
    JoltMonad ExecutionResult := do
  let base ← liftSail (rX_bits rs1)
  let addr := base + sign_extend (m := 64) imm
  let value ← readVReg vs2
  match ← liftSail (vmem_write_addr (Virtaddr addr) 8 value (Store Data) false false false) with
  | .Ok _ => pure RETIRE_SUCCESS
  | .Err e => pure e

/-- `ADD vd, vs1, rs2`, with a virtual left operand and real right operand. -/
def vreg_ADD_from_real_vs2 (vd vs1 : BitVec 7) (rs2 : regidx) :
    JoltMonad ExecutionResult := do
  let x ← readVReg vs1
  let y ← liftSail (rX_bits rs2)
  writeVReg vd (x + y)
  pure RETIRE_SUCCESS

/-- `AND vd, vs1, rs2`, with a virtual left operand and real right operand. -/
def vreg_AND_from_real_vs2 (vd vs1 : BitVec 7) (rs2 : regidx) :
    JoltMonad ExecutionResult := do
  let x ← readVReg vs1
  let y ← liftSail (rX_bits rs2)
  writeVReg vd (x &&& y)
  pure RETIRE_SUCCESS

/-- `OR vd, vs1, vs2`, entirely in virtual registers. -/
def vreg_OR (vd vs1 vs2 : BitVec 7) : JoltMonad ExecutionResult := do
  let x ← readVReg vs1
  let y ← readVReg vs2
  writeVReg vd (x ||| y)
  pure RETIRE_SUCCESS

/-- `OR vd, vs1, rs2`, with a virtual left operand and real right operand. -/
def vreg_OR_from_real_vs2 (vd vs1 : BitVec 7) (rs2 : regidx) :
    JoltMonad ExecutionResult := do
  let x ← readVReg vs1
  let y ← liftSail (rX_bits rs2)
  writeVReg vd (x ||| y)
  pure RETIRE_SUCCESS

/-- `XOR vd, vs1, rs2`, with a virtual left operand and real right operand. -/
def vreg_XOR_from_real_vs2 (vd vs1 : BitVec 7) (rs2 : regidx) :
    JoltMonad ExecutionResult := do
  let x ← readVReg vs1
  let y ← liftSail (rX_bits rs2)
  writeVReg vd (x ^^^ y)
  pure RETIRE_SUCCESS

/-- `SLT vd, rs1, vs2`, with a real left operand and virtual right operand. -/
def vreg_SLT_from_real_vs1 (vd : BitVec 7) (rs1 : regidx) (vs2 : BitVec 7) :
    JoltMonad ExecutionResult := do
  let x ← liftSail (rX_bits rs1)
  let y ← readVReg vs2
  writeVReg vd (zero_extend (m := 64) (bool_to_bit (zopz0zI_s x y)))
  pure RETIRE_SUCCESS

/-- `SLTU vd, rs1, vs2`, with a real left operand and virtual right operand. -/
def vreg_SLTU_from_real_vs1 (vd : BitVec 7) (rs1 : regidx) (vs2 : BitVec 7) :
    JoltMonad ExecutionResult := do
  let x ← liftSail (rX_bits rs1)
  let y ← readVReg vs2
  writeVReg vd (zero_extend (m := 64) (bool_to_bit (zopz0zI_u x y)))
  pure RETIRE_SUCCESS

/-- `SLT vd, vs1, rs2`, with a virtual left operand and real right operand. -/
def vreg_SLT_vs1_real (vd vs1 : BitVec 7) (rs2 : regidx) :
    JoltMonad ExecutionResult := do
  let x ← readVReg vs1
  let y ← liftSail (rX_bits rs2)
  writeVReg vd (zero_extend (m := 64) (bool_to_bit (zopz0zI_s x y)))
  pure RETIRE_SUCCESS

/-- `SLTU vd, vs1, rs2`, with a virtual left operand and real right operand. -/
def vreg_SLTU_vs1_real (vd vs1 : BitVec 7) (rs2 : regidx) :
    JoltMonad ExecutionResult := do
  let x ← readVReg vs1
  let y ← liftSail (rX_bits rs2)
  writeVReg vd (zero_extend (m := 64) (bool_to_bit (zopz0zI_u x y)))
  pure RETIRE_SUCCESS

/-- `SLT vd, vs1, vs2`, entirely in virtual registers. -/
def vreg_SLT (vd vs1 vs2 : BitVec 7) : JoltMonad ExecutionResult := do
  let x ← readVReg vs1
  let y ← readVReg vs2
  writeVReg vd (zero_extend (m := 64) (bool_to_bit (zopz0zI_s x y)))
  pure RETIRE_SUCCESS

/-- `SLTU vd, vs1, vs2`, entirely in virtual registers. -/
def vreg_SLTU (vd vs1 vs2 : BitVec 7) : JoltMonad ExecutionResult := do
  let x ← readVReg vs1
  let y ← readVReg vs2
  writeVReg vd (zero_extend (m := 64) (bool_to_bit (zopz0zI_u x y)))
  pure RETIRE_SUCCESS

/-- `VirtualZeroExtendWord vd, vs1`: zero-extend virtual `vs1`'s low word. -/
def vreg_zero_extend_word (vd vs1 : BitVec 7) : JoltMonad ExecutionResult := do
  let v ← readVReg vs1
  writeVReg vd (zero_extend (m := 64) (Sail.BitVec.extractLsb v 31 0))
  pure RETIRE_SUCCESS

/-- `SLLI vd, rs1, shamt`, with a real source and virtual destination. -/
def vreg_SLLI_from_real (vd : BitVec 7) (rs1 : regidx) (shamt : BitVec 6) :
    JoltMonad ExecutionResult := do
  let x ← liftSail (rX_bits rs1)
  writeVReg vd (shift_bits_left x shamt)
  pure RETIRE_SUCCESS

/-- `SLL vd, rs1, vs2`, with a real value source and virtual shift source. -/
def vreg_SLL_from_real_vs1 (vd : BitVec 7) (rs1 : regidx) (vs2 : BitVec 7) :
    JoltMonad ExecutionResult := do
  let x ← liftSail (rX_bits rs1)
  let y ← readVReg vs2
  writeVReg vd (shift_bits_left x (Sail.BitVec.extractLsb y 5 0))
  pure RETIRE_SUCCESS

/-- `SD rs2, imm(rs1)`, with both base and value read from real registers. -/
def vreg_SD_from_real_value (rs1 rs2 : regidx) (imm : BitVec 12) :
    JoltMonad ExecutionResult := do
  let base ← liftSail (rX_bits rs1)
  let addr := base + sign_extend (m := 64) imm
  let value ← liftSail (rX_bits rs2)
  match ← liftSail (vmem_write_addr (Virtaddr addr) 8 value (Store Data) false false false) with
  | .Ok _ => pure RETIRE_SUCCESS
  | .Err e => pure e

/-- Common doubleword AMO shape:

```text
LD   old, rs1, 0
op   new, old, rs2
SD   rs1, new, 0
ADDI rd, old, 0
```
-/
def jolt_amo_d_binop
    (op : BitVec 7 → BitVec 7 → regidx → JoltMonad ExecutionResult)
    (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  match ← vreg_LD_from_real 1 rs1 0 with
  | .Retire_Success () =>
      let _ ← op 0 1 rs2
      match ← vreg_SD_from_real rs1 0 0 with
      | .Retire_Success () => vreg_ADDI_to_real rd 1 0
      | other => pure other
  | other => pure other

/-- Common RV64 `amo_pre64` helper from `tracer/src/instruction/amo.rs`.
It extracts the target word from the containing doubleword. -/
def jolt_amo_word_pre64
    (rs1 : regidx) (v_rd v_dword v_shift : BitVec 7) :
    JoltMonad ExecutionResult := do
  let addr ← liftSail (rX_bits rs1)
  if addr &&& 3 ≠ 0 then
    throw (Error.Assertion "AMO.W: address not word-aligned")
  else do
    writeVReg v_shift addr
    let _ ← vreg_ANDI v_shift v_shift (-8 : BitVec 12)
    match ← vreg_LD v_dword v_shift 0 with
    | .Retire_Success () =>
        let _ ← vreg_SLLI_from_real v_shift rs1 3
        vreg_SRL v_rd v_dword v_shift
    | other => pure other

/-- Common RV64 `amo_post64` helper from `tracer/src/instruction/amo.rs`.
It splices the new word into the containing doubleword and sign-extends the old
word into `rd`. -/
def jolt_amo_word_post64
    (rs1 rd : regidx) (v_rs2 v_dword v_shift v_mask v_rd : BitVec 7) :
    JoltMonad ExecutionResult := do
  writeVReg v_mask 0
  let _ ← vreg_ORI v_mask v_mask (-1 : BitVec 12)
  let _ ← vreg_SRLI v_mask v_mask 32
  let _ ← vreg_SLL v_mask v_mask v_shift
  let _ ← vreg_SLL v_shift v_rs2 v_shift
  let _ ← vreg_XOR v_shift v_dword v_shift
  let _ ← vreg_AND v_shift v_shift v_mask
  let _ ← vreg_XOR v_dword v_dword v_shift
  let addr ← liftSail (rX_bits rs1)
  writeVReg v_mask addr
  let _ ← vreg_ANDI v_mask v_mask (-8 : BitVec 12)
  match ← vreg_SD v_mask v_dword 0 with
  | .Retire_Success () => vreg_sign_extend_word_to_real rd v_rd
  | other => pure other

/-- RV64 AMO word post-processing where the new word comes directly from real
`rs2`, as in `AMOSWAP.W`. -/
def jolt_amo_word_post64_from_real
    (rs1 rs2 rd : regidx) (v_dword v_shift v_mask v_rd : BitVec 7) :
    JoltMonad ExecutionResult := do
  writeVReg v_mask 0
  let _ ← vreg_ORI v_mask v_mask (-1 : BitVec 12)
  let _ ← vreg_SRLI v_mask v_mask 32
  let _ ← vreg_SLL v_mask v_mask v_shift
  let _ ← vreg_SLL_from_real_vs1 v_shift rs2 v_shift
  let _ ← vreg_XOR v_shift v_dword v_shift
  let _ ← vreg_AND v_shift v_shift v_mask
  let _ ← vreg_XOR v_dword v_dword v_shift
  let addr ← liftSail (rX_bits rs1)
  writeVReg v_mask addr
  let _ ← vreg_ANDI v_mask v_mask (-8 : BitVec 12)
  match ← vreg_SD v_mask v_dword 0 with
  | .Retire_Success () => vreg_sign_extend_word_to_real rd v_rd
  | other => pure other

/-- Common RV64 AMO.W shape using `amo_pre64`, one virtual/real operation, and
`amo_post64`. -/
def jolt_amo_w_binop
    (op : BitVec 7 → BitVec 7 → regidx → JoltMonad ExecutionResult)
    (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  match ← jolt_amo_word_pre64 rs1 0 3 4 with
  | .Retire_Success () =>
      let _ ← op 1 0 rs2
      jolt_amo_word_post64 rs1 rd 1 3 4 2 0
  | other => pure other

end Atomics
