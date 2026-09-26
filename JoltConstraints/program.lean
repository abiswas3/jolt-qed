import JoltBytecode.JoltISA.Instruction
import JoltConstraints.register_encoding
import JoltBytecode.JoltISA.Semantics
import JoltBytecode.JoltISA.DeviceMemory
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false

set_option maxRecDepth 4096 in
deriving instance Fintype for Register

private def initialRegisterValue (entryAddress : BitVec 64)
    (r : Register) : RegisterType r :=
  match r with
  | .PC | .nextPC => entryAddress
  | .misa => 0x800000008014312f
  | .cur_privilege => .Machine
  | .hart_state => .HART_ACTIVE ()
  | r => by cases r <;> exact default

noncomputable def init_state (entryAddress : BitVec 64)
    (ram : Array (BitVec 8)) (io : JoltIOState)
    (adviceTape : JoltAdviceTape) : SailJoltState :=
  { sail :=
      { regs := (Finset.univ.toList : List Register).foldl
          (fun regs r => regs.insert r (initialRegisterValue entryAddress r)) {}
        mem := ram.toList.zipIdx.foldl
          (fun mem (byte, offset) => mem.insert (0x80000000 + offset) byte) {}
        choiceState := ()
        tags := ()
        cycleCount := 0
        sailOutput := #[] }
    vregs := fun _ => 0
    io := io
    adviceTape := adviceTape }

namespace JoltISA.Instr

def RuntimeAdvice : JoltISA.Instr → Type
  | .VirtualAdvice .. => BitVec 64
  | _ => Unit

def withRuntimeAdvice (instruction : JoltISA.Instr)
    (advice : instruction.RuntimeAdvice) : JoltISA.Instr :=
  match instruction with
  | .VirtualAdvice dst _ imm => .VirtualAdvice dst advice imm
  | instruction => instruction

def IsBytecodeTemplate : JoltISA.Instr → Prop
  | .VirtualAdvice _ value _ => value = 0
  | _ => True

end JoltISA.Instr

def finalProgramRowInstruction (inputInstruction : JoltISA.Instr)
    (virtualSequenceRemaining : Option (BitVec 16)) : JoltISA.Instr :=
  if virtualSequenceRemaining.isNone then inputInstruction.rewriteNative
  else inputInstruction

structure JoltProgramRow where
  inputInstruction : JoltISA.Instr
  address : BitVec 64
  virtualSequenceRemaining : Option (BitVec 16)
  isFirstInSequence : Bool
  isCompressed : Bool
  -- Use `.xreg` for Sail registers and `.vreg` for virtual registers.
  registerOperandsCanonical :
    JoltRegisterEncoding.instructionIsCanonical
      (finalProgramRowInstruction inputInstruction virtualSequenceRemaining) = true
  -- Store zero for VirtualAdvice; each trace visit supplies its runtime value.
  isBytecodeTemplate :
    (finalProgramRowInstruction inputInstruction virtualSequenceRemaining).IsBytecodeTemplate
  operandsRepresentable :
    (finalProgramRowInstruction inputInstruction virtualSequenceRemaining).OperandsRepresentable := by
      exact True.intro

def JoltProgramRow.expandedInstruction (row : JoltProgramRow) : JoltISA.Instr :=
  finalProgramRowInstruction row.inputInstruction row.virtualSequenceRemaining

def JoltISA.Dst.NotX0 : JoltISA.Dst → Prop
  | .xreg rd => JoltISA.isX0 rd = false
  | .vreg _ => True

-- TODO: We have to show this is true. In Jolt JAL can never
structure JoltProgramRow.Valid (row : JoltProgramRow) : Prop where
  jumpDestinationWritable :
    match row.expandedInstruction with
    | .JAL dst _ => dst.NotX0
    | .JALR dst _ _ => dst.NotX0
    | _ => True
  x0DestinationIsNoOp :
    ∀ rd, row.expandedInstruction.destination? = some (.xreg rd) →
      JoltISA.isX0 rd = true →
      row.expandedInstruction = JoltISA.Instr.canonicalNoOp

theorem JoltProgramRow.Valid.jal {row : JoltProgramRow} (valid : row.Valid)
    {dst : JoltISA.Dst} {imm : BitVec 64}
    (hinst : row.expandedInstruction = .JAL dst imm) :
    dst.NotX0 := by
  have h := valid.jumpDestinationWritable
  rw [hinst] at h
  exact h

theorem JoltProgramRow.Valid.jalr {row : JoltProgramRow} (valid : row.Valid)
    {dst : JoltISA.Dst} {base : JoltISA.Src} {imm : BitVec 64}
    (hinst : row.expandedInstruction = .JALR dst base imm) :
    dst.NotX0 := by
  have h := valid.jumpDestinationWritable
  rw [hinst] at h
  exact h

structure JoltProgram where
  expandedBytecode : Array JoltProgramRow
  initialState : SailJoltState

namespace JoltProgramRow

def continues (row : JoltProgramRow) : Bool :=
  row.virtualSequenceRemaining.getD 0 != 0

def isEntry (row : JoltProgramRow) : Prop :=
  row.virtualSequenceRemaining = none ∨ row.isFirstInSequence = true

end JoltProgramRow

namespace JoltProgram

-- FIXME: This is false for arbitrary JoltProgram arrays. Link program rows to
-- their source-instruction translation, then prove validity for its output.
theorem rowValid (program : JoltProgram)
    (i : Fin program.expandedBytecode.size) :
    program.expandedBytecode[i].Valid := by
  sorry

def NoEarlyNextPCChange (program : JoltProgram) : Prop :=
  ∀ i : Fin program.expandedBytecode.size,
    program.expandedBytecode[i].continues = true →
    ∀ advice : program.expandedBytecode[i].expandedInstruction.RuntimeAdvice,
      ∀ preState postState : SailJoltState,
        JoltISA.execInstr
          (program.expandedBytecode[i].expandedInstruction.withRuntimeAdvice advice) preState =
            .ok (.Retire_Success ()) postState →
          postState.sail.regs.get? Register.nextPC =
            preState.sail.regs.get? Register.nextPC

-- FIXME: This is false for arbitrary JoltProgram values in the working tree
-- based on commit 132435ad231d853e056215630495520894ca27fb. Model the
-- source-to-Jolt-ISA translations in JoltProgram, then prove this for their output.
theorem noEarlyNextPCChange (program : JoltProgram) :
    program.NoEarlyNextPCChange := by
  sorry

def JumpAtSourceEnd (program : JoltProgram) : Prop :=
  ∀ i : Fin program.expandedBytecode.size,
    match program.expandedBytecode[i].expandedInstruction with
    | .JAL .. | .JALR .. => program.expandedBytecode[i].continues = false
    | _ => True

-- TODO: Prove this for translated JoltProgram values once their source-to-Jolt-ISA
-- structure is modeled.
theorem jumpAtSourceEnd (program : JoltProgram) :
    program.JumpAtSourceEnd := by
  sorry

structure SequenceLayout (program : JoltProgram) : Prop where
  endInBounds : ∀ i : Fin program.expandedBytecode.size,
    i.val + (program.expandedBytecode[i].virtualSequenceRemaining.getD 0).toNat <
      program.expandedBytecode.size
  -- WARNING: Check whether Rust accepts a program whose source PC advance wraps past u64::MAX.
  addressAdvanceNoWrap : ∀ i : Fin program.expandedBytecode.size,
    let last := i.val + (program.expandedBytecode[i].virtualSequenceRemaining.getD 0).toNat
    program.expandedBytecode[i].address.toNat +
      (if (program.expandedBytecode[last]'(endInBounds i)).isCompressed then 2 else 4) < 2 ^ 64
  ordinary : ∀ i : Fin program.expandedBytecode.size,
    program.expandedBytecode[i].virtualSequenceRemaining = none →
      program.expandedBytecode[i].isFirstInSequence = false
  firstEntry : ∀ h : 0 < program.expandedBytecode.size,
    (program.expandedBytecode[0]'h).isEntry
  afterEnd : ∀ i j : Fin program.expandedBytecode.size,
    j.val = i.val + 1 → program.expandedBytecode[i].continues = false →
      program.expandedBytecode[j].isEntry
  next : ∀ i j : Fin program.expandedBytecode.size,
    j.val = i.val + 1 → program.expandedBytecode[i].continues = true →
      program.expandedBytecode[j].address = program.expandedBytecode[i].address ∧
      program.expandedBytecode[j].virtualSequenceRemaining =
        some (program.expandedBytecode[i].virtualSequenceRemaining.getD 0 - 1) ∧
      program.expandedBytecode[j].isFirstInSequence = false ∧
      program.expandedBytecode[i].isCompressed = false

def sourceLength (program : JoltProgram) (layout : program.SequenceLayout)
    (i : Fin program.expandedBytecode.size) : Nat :=
  let last := i.val + (program.expandedBytecode[i].virtualSequenceRemaining.getD 0).toNat
  if (program.expandedBytecode[last]'(layout.endInBounds i)).isCompressed then 2 else 4

noncomputable def prepareSource (program : JoltProgram) (layout : program.SequenceLayout)
    (i : Fin program.expandedBytecode.size) (state : SailJoltState) : SailJoltState :=
  let address := program.expandedBytecode[i].address
  let regs := (state.sail.regs.insert Register.PC address).insert Register.nextPC
    (address + BitVec.ofNat 64 (program.sourceLength layout i))
  { state with sail := { state.sail with regs := regs } }

end JoltProgram
