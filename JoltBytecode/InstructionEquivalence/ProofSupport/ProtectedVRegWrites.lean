import JoltBytecode.JoltISA.Instruction

/-!
# Protected virtual-register write footprints

Some registers like control status registers are present both as virtual registers,
and as keyed registers in the sail hash map.
This makes the final projection lemma a little complicated.
However, most instructions and jolt programs do not write to these registers.
This would simply system project a great deal.
Here we prove which instructions, write and do not write to these protected virtual registers.
-/

namespace JoltISA

/-- A destination writes a protected virtual register when it is a protected
virtual-register destination. -/
def Dst.WritesProtectedVReg : Dst → Prop
  | .vreg vr => IsProtectedJoltRegister vr
  | .xreg _ => False

/-- Determine whether a Jolt instruction can write a protected virtual
register. -/
def Instr.WritesProtectedVReg : Instr → Prop
  | .ADDI dst _ _
  | .ADDIW dst _ _
  | .ANDI dst _ _
  | .ORI dst _ _
  | .XORI dst _ _
  | .SLTI dst _ _
  | .SLTIU dst _ _
  | .LUI dst _
  | .AUIPC dst _
  | .JAL dst _
  | .JALR dst _ _
  | .ADD dst _ _
  | .ADDW dst _ _
  | .SUB dst _ _
  | .SUBW dst _ _
  | .MUL dst _ _
  | .MULW dst _ _
  | .MULHU dst _ _
  | .ANDN dst _ _
  | .VirtualMULI dst _ _
  | .VirtualMULIW dst _ _
  | .VirtualPow2 dst _
  | .VirtualPow2W dst _
  | .VirtualPow2I dst _
  | .VirtualPow2IW dst _
  | .VirtualShiftRightBitmask dst _
  | .VirtualShiftRightBitmaskI dst _
  | .VirtualShiftRightBitmaskW dst _
  | .VirtualSRLI dst _ _
  | .VirtualSRAI dst _ _
  | .VirtualSRLIW dst _ _
  | .VirtualSRAIW dst _ _
  | .VirtualSRL dst _ _
  | .VirtualSRA dst _ _
  | .VirtualSRLW dst _ _
  | .VirtualSRAW dst _ _
  | .VirtualROTRI dst _ _
  | .VirtualROTRIW dst _ _
  | .VirtualRev8W dst _
  | .VirtualXORROT32 dst _ _
  | .VirtualXORROT24 dst _ _
  | .VirtualXORROT16 dst _ _
  | .VirtualXORROT63 dst _ _
  | .VirtualXORROTW16 dst _ _
  | .VirtualXORROTW12 dst _ _
  | .VirtualXORROTW8 dst _ _
  | .VirtualXORROTW7 dst _ _
  | .VirtualXORROTW22 dst _ _
  | .VirtualXORROTW19 dst _ _
  | .VirtualXORROTW6 dst _ _
  | .OR dst _ _
  | .XOR dst _ _
  | .AND dst _ _
  | .SLT dst _ _
  | .SLTU dst _ _
  | .VirtualAlignAddr dst _ _
  | .VirtualWindowMaskB dst _ _
  | .VirtualWindowMaskH dst _ _
  | .VirtualWindowMaskW dst _ _
  | .VirtualPext dst _ _
  | .VirtualPextSigned dst _ _
  | .VirtualShiftDataB dst _ _
  | .VirtualShiftDataH dst _ _
  | .VirtualShiftDataW dst _ _
  | .VirtualSignExtendWord dst _
  | .VirtualZeroExtendWord dst _
  | .VirtualMovsign dst _
  | .VirtualAdvice dst _
  | .VirtualAdviceLoad dst _
  | .VirtualAdviceLen dst _
  | .VirtualNegateIf dst _ _ => dst.WritesProtectedVReg
  | .LD _ dst _ _ => (sideEffectingDst dst).WritesProtectedVReg
  | .BEQ _ _ _
  | .BNE _ _ _
  | .BLT _ _ _
  | .BGE _ _ _
  | .BLTU _ _ _
  | .BGEU _ _ _
  | .FENCE
  | .VirtualAssertHalfwordAlignment _ _ _
  | .VirtualAssertWordAlignment _ _ _
  | .SD _ _ _
  | .VirtualHostIO
  | .VirtualAssertEQ _ _ _
  | .VirtualAssertValidDiv0 _ _
  | .VirtualAssertValidUnsignedRemainder _ _
  | .VirtualAssertMulUNoOverflow _ _
  | .VirtualAssertLTE _ _ => False

/-- A program writes a protected virtual register when one of its instructions
does. -/
def Program.WritesProtectedVReg : Program → Prop
  | .done _ => False
  | .instr instruction rest =>
      instruction.WritesProtectedVReg ∨ rest.WritesProtectedVReg

/-- This destination does not write a protected virtual register. -/
def Dst.DoesNotWriteProtectedVRegs (dst : Dst) : Prop :=
  ¬ dst.WritesProtectedVReg

/-- This instruction does not write a protected virtual register. -/
def Instr.DoesNotWriteProtectedVRegs (instr : Instr) : Prop :=
  ¬ instr.WritesProtectedVReg

/-- This program does not write a protected virtual register. -/
def Program.DoesNotWriteProtectedVRegs (program : Program) : Prop :=
  ¬ program.WritesProtectedVReg

/-- If `rd` is an `xreg`, then it is not a protected virtual register. -/
@[simp] theorem Dst.xreg_doesNotWriteProtectedVRegs (rd : regidx) :
    (Dst.xreg rd).DoesNotWriteProtectedVRegs := by
  unfold DoesNotWriteProtectedVRegs WritesProtectedVReg
  intro h
  exact h

/-- A virtual-register destination does not write a protected virtual register
exactly when its register is not protected. -/
@[simp] theorem Dst.vreg_doesNotWriteProtectedVRegs_iff (vr : VReg) :
    (Dst.vreg vr).DoesNotWriteProtectedVRegs ↔
      ¬ IsProtectedJoltRegister vr := by
  unfold DoesNotWriteProtectedVRegs WritesProtectedVReg
  rfl

/-- A completed program performs no protected virtual-register writes. -/
@[simp] theorem Program.done_doesNotWriteProtectedVRegs
    (result : ExecutionResult) :
    (Program.done result).DoesNotWriteProtectedVRegs := by
  unfold DoesNotWriteProtectedVRegs WritesProtectedVReg
  intro h
  exact h

/-- A program does not write a protected virtual register if its current
instruction and the rest of the program do not. -/
@[simp] theorem Program.instr_doesNotWriteProtectedVRegs_iff
    (instr : Instr) (rest : Program) :
    (Program.instr instr rest).DoesNotWriteProtectedVRegs ↔
      instr.DoesNotWriteProtectedVRegs ∧
        rest.DoesNotWriteProtectedVRegs := by
  simp only [Program.DoesNotWriteProtectedVRegs,
    Program.WritesProtectedVReg, Instr.DoesNotWriteProtectedVRegs, not_or]

/-- If every instruction in a list does not write a protected virtual
register, then the composed program does not either. -/
theorem Program.seq_doesNotWriteProtectedVRegs
    {instrs : List Instr}
    (h : ∀ instr ∈ instrs, instr.DoesNotWriteProtectedVRegs) :
    (Program.seq instrs).DoesNotWriteProtectedVRegs := by
  induction instrs with
  | nil =>
      change
        (Program.done (.Retire_Success ())).DoesNotWriteProtectedVRegs
      exact Program.done_doesNotWriteProtectedVRegs (.Retire_Success ())
  | cons instr rest ih =>
      simp only [Program.seq, List.foldr_cons,
        Program.instr_doesNotWriteProtectedVRegs_iff]
      have hhead : instr.DoesNotWriteProtectedVRegs :=
        h instr List.mem_cons_self
      have htail : ∀ i ∈ rest, i.DoesNotWriteProtectedVRegs := by
        intro i hi
        exact h i (List.mem_cons_of_mem instr hi)
      exact ⟨hhead, ih htail⟩

/-- If two programs do not write a protected register, then neither does
their composition.-/
theorem Program.append_doesNotWriteProtectedVRegs
    {first second : Program}
    (hfirst : first.DoesNotWriteProtectedVRegs)
    (hsecond : second.DoesNotWriteProtectedVRegs) :
    (first.append second).DoesNotWriteProtectedVRegs := by
  induction first with
  | done result =>
      cases result <;>
        simp only [Program.append,
          Program.done_doesNotWriteProtectedVRegs, hsecond]
  | instr instr rest ih =>
      rw [Program.instr_doesNotWriteProtectedVRegs_iff] at hfirst
      change
        (Program.instr instr
          (Program.append rest second)).DoesNotWriteProtectedVRegs
      rw [Program.instr_doesNotWriteProtectedVRegs_iff]
      exact ⟨hfirst.1, ih hfirst.2⟩

end JoltISA
