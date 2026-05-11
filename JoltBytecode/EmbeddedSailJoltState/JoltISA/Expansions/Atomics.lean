import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics

/-!
# Atomic Jolt expansion programs

These are RV64 data-level Jolt programs for the AMO expansion family.  The
definitions follow the Rust sources in
`/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/instruction`.

The `.W` programs deliberately share Rust's `amo_pre64` / `amo_post64` shape:
extract the target word from the containing doubleword, compute the new word,
splice it back, and sign-extend the old word into `rd`.
-/

open Sail PreSail LeanRV64D.Functions

namespace JoltISA

def amoOldVReg : VReg := 0
def amoNewVReg : VReg := 1
def amoTmpVReg : VReg := 2
def amoDwordVReg : VReg := 3
def amoShiftVReg : VReg := 4
def amoMaskVReg : VReg := 5

/-- Shared Rust `amo_pre64`: assert word alignment, load the containing
doubleword, then extract the addressed word into `old`. -/
def amoPre64Program (rs1 : regidx) (old dword shift : VReg) (tail : Program) :
    Program :=
  .instr (.AssertStoreAlign rs1 (0 : BitVec 12) (3 : BitVec 64)) <|
  .instr (.ANDI (.vreg shift) (.xreg rs1) (-8 : BitVec 12)) <|
  .instr (.LD dword shift (0 : BitVec 12)) <|
  .instr (.SLLI (.vreg shift) (.xreg rs1) (3 : BitVec 6)) <|
  .instr (.SRL (.vreg old) (.vreg dword) (.vreg shift)) <|
  tail

/-- Shared Rust `amo_post64`: splice `newValue` into the containing doubleword,
store it back, and sign-extend the old word into `rd`. -/
def amoPost64Program
    (rs1 rd : regidx) (newValue : Src) (dword shift mask old : VReg) : Program :=
  .instr (.ORI (.vreg mask) (.xreg (regidx.Regidx 0)) (-1 : BitVec 12)) <|
  .instr (.SRLI (.vreg mask) (.vreg mask) (32 : BitVec 6)) <|
  .instr (.SLL (.vreg mask) (.vreg mask) (.vreg shift)) <|
  .instr (.SLL (.vreg shift) newValue (.vreg shift)) <|
  .instr (.XOR (.vreg shift) (.vreg dword) (.vreg shift)) <|
  .instr (.AND (.vreg shift) (.vreg shift) (.vreg mask)) <|
  .instr (.XOR (.vreg dword) (.vreg dword) (.vreg shift)) <|
  .instr (.ANDI (.vreg mask) (.xreg rs1) (-8 : BitVec 12)) <|
  .instr (.SD mask dword (0 : BitVec 12)) <|
  .instr (.SExtW (.xreg rd) (.vreg old)) <|
  .done RETIRE_SUCCESS

def amoDoubleBinopProgram
    (op : Dst → Src → Src → Instr) (rs2 rs1 rd : regidx) : Program :=
  .instr (.LDFrom amoOldVReg (.xreg rs1) (0 : BitVec 12)) <|
  .instr (op (.vreg amoNewVReg) (.vreg amoOldVReg) (.xreg rs2)) <|
  .instr (.SDFrom (.xreg rs1) (.vreg amoNewVReg) (0 : BitVec 12)) <|
  .instr (.ADDI (.xreg rd) (.vreg amoOldVReg) (0 : BitVec 12)) <|
  .done RETIRE_SUCCESS

def amoDoubleSelectProgram
    (cmpInstr : Dst → Src → Src → Instr) (cmpLhs cmpRhs : Src)
    (rs2 rs1 rd : regidx) : Program :=
  .instr (.LDFrom amoOldVReg (.xreg rs1) (0 : BitVec 12)) <|
  .instr (cmpInstr (.vreg amoNewVReg) cmpLhs cmpRhs) <|
  .instr (.SUB (.vreg amoTmpVReg) (.xreg rs2) (.vreg amoOldVReg)) <|
  .instr (.MUL (.vreg amoTmpVReg) (.vreg amoTmpVReg) (.vreg amoNewVReg)) <|
  .instr (.ADD (.vreg amoNewVReg) (.vreg amoOldVReg) (.vreg amoTmpVReg)) <|
  .instr (.SDFrom (.xreg rs1) (.vreg amoNewVReg) (0 : BitVec 12)) <|
  .instr (.ADDI (.xreg rd) (.vreg amoOldVReg) (0 : BitVec 12)) <|
  .done RETIRE_SUCCESS

def amoWordBinopProgram
    (op : Dst → Src → Src → Instr) (rs2 rs1 rd : regidx) : Program :=
  amoPre64Program rs1 amoOldVReg amoDwordVReg amoShiftVReg <|
  .instr (op (.vreg amoNewVReg) (.vreg amoOldVReg) (.xreg rs2)) <|
  amoPost64Program rs1 rd (.vreg amoNewVReg)
    amoDwordVReg amoShiftVReg amoMaskVReg amoOldVReg

def amoWordSelectProgram
    (extend : Dst → Src → Instr) (cmpInstr : Dst → Src → Src → Instr)
    (cmpLhs cmpRhs : Src) (rs2 rs1 rd : regidx) : Program :=
  amoPre64Program rs1 amoOldVReg amoDwordVReg amoShiftVReg <|
  .instr (extend (.vreg amoNewVReg) (.xreg rs2)) <|
  .instr (extend (.vreg amoMaskVReg) (.vreg amoOldVReg)) <|
  .instr (cmpInstr (.vreg amoMaskVReg) cmpLhs cmpRhs) <|
  .instr (.SUB (.vreg amoNewVReg) (.xreg rs2) (.vreg amoOldVReg)) <|
  .instr (.MUL (.vreg amoNewVReg) (.vreg amoNewVReg) (.vreg amoMaskVReg)) <|
  .instr (.ADD (.vreg amoNewVReg) (.vreg amoNewVReg) (.vreg amoOldVReg)) <|
  amoPost64Program rs1 rd (.vreg amoNewVReg)
    amoDwordVReg amoShiftVReg amoMaskVReg amoOldVReg

def amoadddProgram (rs2 rs1 rd : regidx) : Program :=
  amoDoubleBinopProgram (fun dst lhs rhs => .ADD dst lhs rhs) rs2 rs1 rd

def amoanddProgram (rs2 rs1 rd : regidx) : Program :=
  amoDoubleBinopProgram (fun dst lhs rhs => .AND dst lhs rhs) rs2 rs1 rd

def amoordProgram (rs2 rs1 rd : regidx) : Program :=
  amoDoubleBinopProgram (fun dst lhs rhs => .OR dst lhs rhs) rs2 rs1 rd

def amoxordProgram (rs2 rs1 rd : regidx) : Program :=
  amoDoubleBinopProgram (fun dst lhs rhs => .XOR dst lhs rhs) rs2 rs1 rd

def amoswapdProgram (rs2 rs1 rd : regidx) : Program :=
  .instr (.LDFrom amoOldVReg (.xreg rs1) (0 : BitVec 12)) <|
  .instr (.SDFrom (.xreg rs1) (.xreg rs2) (0 : BitVec 12)) <|
  .instr (.ADDI (.xreg rd) (.vreg amoOldVReg) (0 : BitVec 12)) <|
  .done RETIRE_SUCCESS

def amomindProgram (rs2 rs1 rd : regidx) : Program :=
  amoDoubleSelectProgram (fun dst lhs rhs => .SLT dst lhs rhs)
    (.xreg rs2) (.vreg amoOldVReg) rs2 rs1 rd

def amomaxdProgram (rs2 rs1 rd : regidx) : Program :=
  amoDoubleSelectProgram (fun dst lhs rhs => .SLT dst lhs rhs)
    (.vreg amoOldVReg) (.xreg rs2) rs2 rs1 rd

def amominudProgram (rs2 rs1 rd : regidx) : Program :=
  amoDoubleSelectProgram (fun dst lhs rhs => .SLTU dst lhs rhs)
    (.xreg rs2) (.vreg amoOldVReg) rs2 rs1 rd

def amomaxudProgram (rs2 rs1 rd : regidx) : Program :=
  amoDoubleSelectProgram (fun dst lhs rhs => .SLTU dst lhs rhs)
    (.vreg amoOldVReg) (.xreg rs2) rs2 rs1 rd

def amoaddwProgram (rs2 rs1 rd : regidx) : Program :=
  amoWordBinopProgram (fun dst lhs rhs => .ADD dst lhs rhs) rs2 rs1 rd

def amoandwProgram (rs2 rs1 rd : regidx) : Program :=
  amoWordBinopProgram (fun dst lhs rhs => .AND dst lhs rhs) rs2 rs1 rd

def amoorwProgram (rs2 rs1 rd : regidx) : Program :=
  amoWordBinopProgram (fun dst lhs rhs => .OR dst lhs rhs) rs2 rs1 rd

def amoxorwProgram (rs2 rs1 rd : regidx) : Program :=
  amoWordBinopProgram (fun dst lhs rhs => .XOR dst lhs rhs) rs2 rs1 rd

def amoswapwProgram (rs2 rs1 rd : regidx) : Program :=
  amoPre64Program rs1 amoOldVReg amoDwordVReg amoShiftVReg <|
  amoPost64Program rs1 rd (.xreg rs2)
    amoDwordVReg amoShiftVReg amoMaskVReg amoOldVReg

def amominwProgram (rs2 rs1 rd : regidx) : Program :=
  amoWordSelectProgram (fun dst src => .SExtW dst src)
    (fun dst lhs rhs => .SLT dst lhs rhs)
    (.vreg amoNewVReg) (.vreg amoMaskVReg) rs2 rs1 rd

def amomaxwProgram (rs2 rs1 rd : regidx) : Program :=
  amoWordSelectProgram (fun dst src => .SExtW dst src)
    (fun dst lhs rhs => .SLT dst lhs rhs)
    (.vreg amoMaskVReg) (.vreg amoNewVReg) rs2 rs1 rd

def amominuwProgram (rs2 rs1 rd : regidx) : Program :=
  amoWordSelectProgram (fun dst src => .ZExtW dst src)
    (fun dst lhs rhs => .SLTU dst lhs rhs)
    (.vreg amoNewVReg) (.vreg amoMaskVReg) rs2 rs1 rd

def amomaxuwProgram (rs2 rs1 rd : regidx) : Program :=
  amoWordSelectProgram (fun dst src => .ZExtW dst src)
    (fun dst lhs rhs => .SLTU dst lhs rhs)
    (.vreg amoMaskVReg) (.vreg amoNewVReg) rs2 rs1 rd

end JoltISA
