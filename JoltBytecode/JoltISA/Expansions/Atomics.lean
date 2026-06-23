import JoltBytecode.JoltISA.Instruction
import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.JoltISA.VirtualRegisters

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

/-- Rust `v_rd`/`v0`: old AMO value for dword select and word binop paths. -/
def amoOldVReg : VReg := inlineTmp0

/-- Rust `v1`/`v_rs2`: computed AMO value for dword select and word binop paths. -/
def amoNewVReg : VReg := inlineTmp1

/-- Rust `v2`: temporary delta/product register in dword select paths. -/
def amoTmpVReg : VReg := inlineTmp2

/-- Rust `v_mask` for word binop paths. -/
def amoMaskVReg : VReg := inlineTmp2

/-- Rust `v_dword` for word binop paths. -/
def amoDwordVReg : VReg := inlineTmp3

/-- Rust `v_shift` for word binop paths. -/
def amoShiftVReg : VReg := inlineTmp4

/-- Recursive `SRL`/`SLL` scratch after the word-binop outer registers. -/
def amoInlineTmpVReg : VReg := inlineTmp5

/-- Rust `v_rs2`: computed result register for dword binop paths. -/
def amoDoubleBinopNewVReg : VReg := inlineTmp0

/-- Rust `v_rd`: loaded old value register for dword binop paths. -/
def amoDoubleBinopOldVReg : VReg := inlineTmp1

/-- Rust `v_mask` for `AMOSWAP.W` RV64. -/
def amoWordSwapMaskVReg : VReg := inlineTmp0

/-- Rust `v_dword` for `AMOSWAP.W` RV64. -/
def amoWordSwapDwordVReg : VReg := inlineTmp1

/-- Rust `v_shift` for `AMOSWAP.W` RV64. -/
def amoWordSwapShiftVReg : VReg := inlineTmp2

/-- Rust `v_rd` for `AMOSWAP.W` RV64. -/
def amoWordSwapOldVReg : VReg := inlineTmp3

/-- Recursive `SRL`/`SLL` scratch after the `AMOSWAP.W` RV64 outer registers. -/
def amoWordSwapInlineTmpVReg : VReg := inlineTmp4

/-- Rust `v_rd` for word min/max RV64 paths. -/
def amoWordSelectOldVReg : VReg := inlineTmp0

/-- Rust `v_dword` for word min/max RV64 paths. -/
def amoWordSelectDwordVReg : VReg := inlineTmp1

/-- Rust `v_shift` for word min/max RV64 paths. -/
def amoWordSelectShiftVReg : VReg := inlineTmp2

/-- Rust `v_rs2` for word min/max RV64 paths. -/
def amoWordSelectNewVReg : VReg := inlineTmp3

/-- Rust `v0`, reused as the postlude mask, for word min/max RV64 paths. -/
def amoWordSelectMaskVReg : VReg := inlineTmp4

/-- Recursive `SRL`/`SLL` scratch after the word-select outer registers. -/
def amoWordSelectInlineTmpVReg : VReg := inlineTmp5

/-- Rust allocation layout for `AMOSWAP.D`: one old-value guard. -/
theorem amoSwapDouble_allocate_layout :
    allocateInstructionRegister [] = some (amoOldVReg, [0]) := by
  decide

/-- Rust allocation layout for dword binop atomics: `v_rs2`, then `v_rd`. -/
theorem amoDoubleBinop_allocate_layout :
    allocateInstructionRegister [] = some (amoDoubleBinopNewVReg, [0]) ∧
    allocateInstructionRegister [0] = some (amoDoubleBinopOldVReg, [1, 0]) := by
  decide

/-- Rust allocation layout for dword min/max atomics: `v0`, `v1`, `v2`. -/
theorem amoDoubleSelect_allocate_layout :
    allocateInstructionRegister [] = some (amoOldVReg, [0]) ∧
    allocateInstructionRegister [0] = some (amoNewVReg, [1, 0]) ∧
    allocateInstructionRegister [1, 0] = some (amoTmpVReg, [2, 1, 0]) := by
  decide

/-- Rust allocation layout for word binop atomics on RV64, including the
recursive shift helper scratch while the five outer guards are live. -/
theorem amoWordBinop_allocate_layout :
    allocateInstructionRegister [] = some (amoOldVReg, [0]) ∧
    allocateInstructionRegister [0] = some (amoNewVReg, [1, 0]) ∧
    allocateInstructionRegister [1, 0] = some (amoMaskVReg, [2, 1, 0]) ∧
    allocateInstructionRegister [2, 1, 0] = some (amoDwordVReg, [3, 2, 1, 0]) ∧
    allocateInstructionRegister [3, 2, 1, 0] =
      some (amoShiftVReg, [4, 3, 2, 1, 0]) ∧
    allocateInstructionRegister [4, 3, 2, 1, 0] =
      some (amoInlineTmpVReg, [5, 4, 3, 2, 1, 0]) := by
  decide

/-- Rust allocation layout for `AMOSWAP.W` on RV64, including recursive shift
helper scratch while the four outer guards are live. -/
theorem amoWordSwap_allocate_layout :
    allocateInstructionRegister [] = some (amoWordSwapMaskVReg, [0]) ∧
    allocateInstructionRegister [0] = some (amoWordSwapDwordVReg, [1, 0]) ∧
    allocateInstructionRegister [1, 0] = some (amoWordSwapShiftVReg, [2, 1, 0]) ∧
    allocateInstructionRegister [2, 1, 0] =
      some (amoWordSwapOldVReg, [3, 2, 1, 0]) ∧
    allocateInstructionRegister [3, 2, 1, 0] =
      some (amoWordSwapInlineTmpVReg, [4, 3, 2, 1, 0]) := by
  decide

/-- Rust allocation layout for word min/max atomics on RV64.  The prelude's
recursive `SRL` scratch is freed before Rust allocates `v_rs2`; the postlude's
recursive shifts then use the next free register while `v_rd,v_dword,v_shift,
v_rs2,v0` are live. -/
theorem amoWordSelect_allocate_layout :
    allocateInstructionRegister [] = some (amoWordSelectOldVReg, [0]) ∧
    allocateInstructionRegister [0] = some (amoWordSelectDwordVReg, [1, 0]) ∧
    allocateInstructionRegister [1, 0] = some (amoWordSelectShiftVReg, [2, 1, 0]) ∧
    allocateInstructionRegister [2, 1, 0] =
      some (amoWordSelectNewVReg, [3, 2, 1, 0]) ∧
    allocateInstructionRegister [3, 2, 1, 0] =
      some (amoWordSelectMaskVReg, [4, 3, 2, 1, 0]) ∧
    allocateInstructionRegister [4, 3, 2, 1, 0] =
      some (amoWordSelectInlineTmpVReg, [5, 4, 3, 2, 1, 0]) := by
  decide

/-- Shared Rust `amo_pre64`: assert word alignment, load the containing
doubleword, then extract the addressed word into `old`.

The final argument is the scratch register allocated by the recursive `SRL`
inline expansion at that call site. -/
def amoPre64ProgramWithScratch
    (rs1 : regidx) (old dword shift inlineTmp : VReg) (tail : Program) :
    Program :=
  .instr (.VirtualAssertWordAlignment rs1 (0 : BitVec 12) (ExceptionType.E_SAMO_Addr_Align ())) <|
  .instr (.ANDI (.vreg shift) (.xreg rs1) (-8 : BitVec 12)) <|
  .instr (.LD (.vreg dword) (.vreg shift) (0 : BitVec 12)) <|
  .instr (.VirtualMULI (.vreg shift) (.xreg rs1) (8 : BitVec 64)) <|
  .instr (.VirtualShiftRightBitmask (.vreg inlineTmp) (.vreg shift)) <|
  .instr (.VirtualSRL (.vreg old) (.vreg dword) (.vreg inlineTmp)) <|
  tail

/-- Word-binop instance of Rust `amo_pre64`, where the recursive `SRL`
scratch is the first register after `v_rd`, `v_rs2`, `v_mask`, `v_dword`, and
`v_shift`. -/
def amoPre64Program (rs1 : regidx) (old dword shift : VReg) (tail : Program) :
    Program :=
  amoPre64ProgramWithScratch rs1 old dword shift amoInlineTmpVReg tail

/-- Shared Rust `amo_post64`: splice `newValue` into the containing doubleword,
store it back, and sign-extend the old word into `rd`.

The final argument is the scratch register allocated by each recursive `SLL`
inline expansion inside the postlude. -/
def amoPost64ProgramWithScratch
    (rs1 rd : regidx) (newValue : Src) (dword shift mask old inlineTmp : VReg) :
    Program :=
  .instr (.ORI (.vreg mask) (.xreg (regidx.Regidx 0)) (-1 : BitVec 12)) <|
  .instr (.VirtualSRLI (.vreg mask) (.vreg mask) (srliBitmask (32 : BitVec 6))) <|
  .instr (.VirtualPow2 (.vreg inlineTmp) (.vreg shift)) <|
  .instr (.MUL (.vreg mask) (.vreg mask) (.vreg inlineTmp)) <|
  .instr (.VirtualPow2 (.vreg inlineTmp) (.vreg shift)) <|
  .instr (.MUL (.vreg shift) newValue (.vreg inlineTmp)) <|
  .instr (.XOR (.vreg shift) (.vreg dword) (.vreg shift)) <|
  .instr (.AND (.vreg shift) (.vreg shift) (.vreg mask)) <|
  .instr (.XOR (.vreg dword) (.vreg dword) (.vreg shift)) <|
  .instr (.ANDI (.vreg mask) (.xreg rs1) (-8 : BitVec 12)) <|
  .instr (.SD (.vreg mask) (.vreg dword) (0 : BitVec 12)) <|
  .instr (.VirtualSignExtendWord (.xreg rd) (.vreg old)) <|
  .done RETIRE_SUCCESS

/-- Word-binop instance of Rust `amo_post64`, where recursive `SLL` calls reuse
the first register after the word-binop outer temporaries. -/
def amoPost64Program
    (rs1 rd : regidx) (newValue : Src) (dword shift mask old : VReg) : Program :=
  amoPost64ProgramWithScratch rs1 rd newValue dword shift mask old
    amoInlineTmpVReg

def amoDoubleBinopProgram
    (op : Dst → Src → Src → Instr) (rs2 rs1 rd : regidx) : Program :=
  .instr (.LD (.vreg amoDoubleBinopOldVReg) (.xreg rs1) (0 : BitVec 12)) <|
  .instr (op (.vreg amoDoubleBinopNewVReg) (.vreg amoDoubleBinopOldVReg) (.xreg rs2)) <|
  .instr (.SD (.xreg rs1) (.vreg amoDoubleBinopNewVReg) (0 : BitVec 12)) <|
  .instr (.ADDI (.xreg rd) (.vreg amoDoubleBinopOldVReg) (0 : BitVec 12)) <|
  .done RETIRE_SUCCESS

def amoDoubleSelectProgram
    (cmpInstr : Dst → Src → Src → Instr) (cmpLhs cmpRhs : Src)
    (rs2 rs1 rd : regidx) : Program :=
  .instr (.LD (.vreg amoOldVReg) (.xreg rs1) (0 : BitVec 12)) <|
  .instr (cmpInstr (.vreg amoNewVReg) cmpLhs cmpRhs) <|
  .instr (.SUB (.vreg amoTmpVReg) (.xreg rs2) (.vreg amoOldVReg)) <|
  .instr (.MUL (.vreg amoTmpVReg) (.vreg amoTmpVReg) (.vreg amoNewVReg)) <|
  .instr (.ADD (.vreg amoNewVReg) (.vreg amoOldVReg) (.vreg amoTmpVReg)) <|
  .instr (.SD (.xreg rs1) (.vreg amoNewVReg) (0 : BitVec 12)) <|
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

/-- Rust-shaped RV64 word min/max helper.

Rust allocates `v_rd`, `v_dword`, and `v_shift`, runs `amo_pre64`, then reuses
the recursive prelude scratch as `v_rs2` and allocates `v0` for the comparison
flag and later postlude mask. -/
def amoWordSelectRustProgram
    (extend : Dst → Src → Instr) (cmpInstr : Dst → Src → Src → Instr)
    (cmpLhs cmpRhs : Src) (rs2 rs1 rd : regidx) : Program :=
  amoPre64ProgramWithScratch rs1
    amoWordSelectOldVReg amoWordSelectDwordVReg amoWordSelectShiftVReg
    amoWordSelectNewVReg <|
  .instr (extend (.vreg amoWordSelectNewVReg) (.xreg rs2)) <|
  .instr (extend (.vreg amoWordSelectMaskVReg)
    (.vreg amoWordSelectOldVReg)) <|
  .instr (cmpInstr (.vreg amoWordSelectMaskVReg) cmpLhs cmpRhs) <|
  .instr (.SUB (.vreg amoWordSelectNewVReg)
    (.xreg rs2) (.vreg amoWordSelectOldVReg)) <|
  .instr (.MUL (.vreg amoWordSelectNewVReg)
    (.vreg amoWordSelectNewVReg) (.vreg amoWordSelectMaskVReg)) <|
  .instr (.ADD (.vreg amoWordSelectNewVReg)
    (.vreg amoWordSelectNewVReg) (.vreg amoWordSelectOldVReg)) <|
  amoPost64ProgramWithScratch rs1 rd (.vreg amoWordSelectNewVReg)
    amoWordSelectDwordVReg amoWordSelectShiftVReg amoWordSelectMaskVReg
    amoWordSelectOldVReg amoWordSelectInlineTmpVReg

def amoadddProgram (rs2 rs1 rd : regidx) : Program :=
  amoDoubleBinopProgram (fun dst lhs rhs => .ADD dst lhs rhs) rs2 rs1 rd

def amoanddProgram (rs2 rs1 rd : regidx) : Program :=
  amoDoubleBinopProgram (fun dst lhs rhs => .AND dst lhs rhs) rs2 rs1 rd

def amoordProgram (rs2 rs1 rd : regidx) : Program :=
  amoDoubleBinopProgram (fun dst lhs rhs => .OR dst lhs rhs) rs2 rs1 rd

def amoxordProgram (rs2 rs1 rd : regidx) : Program :=
  amoDoubleBinopProgram (fun dst lhs rhs => .XOR dst lhs rhs) rs2 rs1 rd

def amoswapdProgram (rs2 rs1 rd : regidx) : Program :=
  .instr (.LD (.vreg amoOldVReg) (.xreg rs1) (0 : BitVec 12)) <|
  .instr (.SD (.xreg rs1) (.xreg rs2) (0 : BitVec 12)) <|
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
  amoPre64ProgramWithScratch rs1
    amoWordSwapOldVReg amoWordSwapDwordVReg amoWordSwapShiftVReg
    amoWordSwapInlineTmpVReg <|
  amoPost64ProgramWithScratch rs1 rd (.xreg rs2)
    amoWordSwapDwordVReg amoWordSwapShiftVReg amoWordSwapMaskVReg
    amoWordSwapOldVReg amoWordSwapInlineTmpVReg

def amominwProgram (rs2 rs1 rd : regidx) : Program :=
  amoWordSelectRustProgram (fun dst src => .VirtualSignExtendWord dst src)
    (fun dst lhs rhs => .SLT dst lhs rhs)
    (.vreg amoWordSelectNewVReg) (.vreg amoWordSelectMaskVReg) rs2 rs1 rd

def amomaxwProgram (rs2 rs1 rd : regidx) : Program :=
  amoWordSelectRustProgram (fun dst src => .VirtualSignExtendWord dst src)
    (fun dst lhs rhs => .SLT dst lhs rhs)
    (.vreg amoWordSelectMaskVReg) (.vreg amoWordSelectNewVReg) rs2 rs1 rd

def amominuwProgram (rs2 rs1 rd : regidx) : Program :=
  amoWordSelectRustProgram (fun dst src => .VirtualZeroExtendWord dst src)
    (fun dst lhs rhs => .SLTU dst lhs rhs)
    (.vreg amoWordSelectNewVReg) (.vreg amoWordSelectMaskVReg) rs2 rs1 rd

def amomaxuwProgram (rs2 rs1 rd : regidx) : Program :=
  amoWordSelectRustProgram (fun dst src => .VirtualZeroExtendWord dst src)
    (fun dst lhs rhs => .SLTU dst lhs rhs)
    (.vreg amoWordSelectMaskVReg) (.vreg amoWordSelectNewVReg) rs2 rs1 rd

end JoltISA
