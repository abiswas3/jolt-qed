import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics
import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions

/-!
# Compatibility with hand-written virtual instructions

These lemmas connect the typed `JoltISA.Instr` interpreter to the existing
`vreg_*` primitives used by the current instruction-equivalence proofs.  They
are intentionally small definitional equalities: generated expansion proofs can
rewrite from `execInstr`/`execProgram` to the legacy primitives while the proof
tree migrates toward the ISA interpreter.
-/

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- Legacy bridge: typed virtual-register `ADDI` is definitionally the old
`vreg_ADDI` primitive. -/
@[simp] theorem execInstr_vreg_ADDI (vd vs1 : BitVec 7) (imm : BitVec 12) :
    execInstr (.ADDI (.vreg vd) (.vreg vs1) imm) = vreg_ADDI vd vs1 imm := rfl

/-- Legacy bridge: typed virtual-register `ANDI` is definitionally the old
`vreg_ANDI` primitive. -/
@[simp] theorem execInstr_vreg_ANDI (vd vs1 : BitVec 7) (imm : BitVec 12) :
    execInstr (.ANDI (.vreg vd) (.vreg vs1) imm) = vreg_ANDI vd vs1 imm := rfl

/-- Legacy bridge: typed virtual-register `ORI` is definitionally the old
`vreg_ORI` primitive. -/
@[simp] theorem execInstr_vreg_ORI (vd vs1 : BitVec 7) (imm : BitVec 12) :
    execInstr (.ORI (.vreg vd) (.vreg vs1) imm) = vreg_ORI vd vs1 imm := rfl

/-- Legacy bridge: typed virtual-register `XORI` is definitionally the old
`vreg_XORI` primitive. -/
@[simp] theorem execInstr_vreg_XORI (vd vs1 : BitVec 7) (imm : BitVec 12) :
    execInstr (.XORI (.vreg vd) (.vreg vs1) imm) = vreg_XORI vd vs1 imm := rfl

/-- Legacy bridge: typed virtual-register `ADD` is definitionally the old
`vreg_ADD` primitive. -/
@[simp] theorem execInstr_vreg_ADD (vd vs1 vs2 : BitVec 7) :
    execInstr (.ADD (.vreg vd) (.vreg vs1) (.vreg vs2)) = vreg_ADD vd vs1 vs2 := rfl

/-- Legacy bridge: typed virtual-register `SUB` is definitionally the old
`vreg_SUB` primitive. -/
@[simp] theorem execInstr_vreg_SUB (vd vs1 vs2 : BitVec 7) :
    execInstr (.SUB (.vreg vd) (.vreg vs1) (.vreg vs2)) = vreg_SUB vd vs1 vs2 := rfl

/-- Legacy bridge: typed virtual-register `MUL` is definitionally the old
`vreg_MUL` primitive. -/
@[simp] theorem execInstr_vreg_MUL (vd vs1 vs2 : BitVec 7) :
    execInstr (.MUL (.vreg vd) (.vreg vs1) (.vreg vs2)) = vreg_MUL vd vs1 vs2 := rfl

/-- Legacy bridge: typed virtual-register `MULH` is definitionally the old
`vreg_MULH` primitive. -/
@[simp] theorem execInstr_vreg_MULH (vd vs1 vs2 : BitVec 7) :
    execInstr (.MULH (.vreg vd) (.vreg vs1) (.vreg vs2)) = vreg_MULH vd vs1 vs2 := rfl

/-- Legacy bridge: typed virtual-register `XOR` is definitionally the old
`vreg_XOR` primitive. -/
@[simp] theorem execInstr_vreg_XOR (vd vs1 vs2 : BitVec 7) :
    execInstr (.XOR (.vreg vd) (.vreg vs1) (.vreg vs2)) = vreg_XOR vd vs1 vs2 := rfl

/-- Legacy bridge: typed virtual-register `AND` is definitionally the old
`vreg_AND` primitive. -/
@[simp] theorem execInstr_vreg_AND (vd vs1 vs2 : BitVec 7) :
    execInstr (.AND (.vreg vd) (.vreg vs1) (.vreg vs2)) = vreg_AND vd vs1 vs2 := rfl

/-- Legacy bridge: typed virtual-register `SLTU` is definitionally the old
`vreg_SLTU` primitive. -/
@[simp] theorem execInstr_vreg_SLTU (vd vs1 vs2 : BitVec 7) :
    execInstr (.SLTU (.vreg vd) (.vreg vs1) (.vreg vs2)) = vreg_SLTU vd vs1 vs2 := rfl

/-- Legacy bridge: typed virtual-register `SLLI` is definitionally the old
`vreg_SLLI` primitive. -/
@[simp] theorem execInstr_vreg_SLLI (vd vs1 : BitVec 7) (shamt : BitVec 6) :
    execInstr (.SLLI (.vreg vd) (.vreg vs1) shamt) = vreg_SLLI vd vs1 shamt := rfl

/-- Legacy bridge: typed virtual-register `SRLI` is definitionally the old
`vreg_SRLI` primitive. -/
@[simp] theorem execInstr_vreg_SRLI (vd vs1 : BitVec 7) (shamt : BitVec 6) :
    execInstr (.SRLI (.vreg vd) (.vreg vs1) shamt) = vreg_SRLI vd vs1 shamt := rfl

/-- Legacy bridge: typed virtual-register `SRAI` is definitionally the old
`vreg_SRAI` primitive. -/
@[simp] theorem execInstr_vreg_SRAI (vd vs1 : BitVec 7) (shamt : BitVec 6) :
    execInstr (.SRAI (.vreg vd) (.vreg vs1) shamt) = vreg_SRAI vd vs1 shamt := rfl

/-- Legacy bridge: typed virtual-register `SLL` is definitionally the old
`vreg_SLL` primitive. -/
@[simp] theorem execInstr_vreg_SLL (vd vs1 vs2 : BitVec 7) :
    execInstr (.SLL (.vreg vd) (.vreg vs1) (.vreg vs2)) = vreg_SLL vd vs1 vs2 := rfl

/-- Legacy bridge: typed virtual-register `SRL` is definitionally the old
`vreg_SRL` primitive. -/
@[simp] theorem execInstr_vreg_SRL (vd vs1 vs2 : BitVec 7) :
    execInstr (.SRL (.vreg vd) (.vreg vs1) (.vreg vs2)) = vreg_SRL vd vs1 vs2 := rfl

/-- Legacy bridge: typed virtual load is definitionally the old `vreg_LD`
primitive. -/
@[simp] theorem execInstr_vreg_LD (vd vs1 : BitVec 7) (imm : BitVec 12) :
    execInstr (.LD vd vs1 imm) = vreg_LD vd vs1 imm := rfl

/-- Legacy bridge: typed virtual store is definitionally the old `vreg_SD`
primitive. -/
@[simp] theorem execInstr_vreg_SD (vs1 vs2 : BitVec 7) (imm : BitVec 12) :
    execInstr (.SD vs1 vs2 imm) = vreg_SD vs1 vs2 imm := rfl

/-- Legacy bridge: real-source virtual-destination `ADDI` is definitionally the
old `vreg_ADDI_from_real` primitive. -/
@[simp] theorem execInstr_vreg_ADDI_from_real (vd : BitVec 7) (rs1 : regidx) (imm : BitVec 12) :
    execInstr (.ADDI (.vreg vd) (.xreg rs1) imm) = vreg_ADDI_from_real vd rs1 imm := rfl

/-- Legacy bridge: virtual-source real-destination `ADDI` is definitionally the
old `vreg_ADDI_to_real` primitive. -/
@[simp] theorem execInstr_vreg_ADDI_to_real (rd : regidx) (vs1 : BitVec 7) (imm : BitVec 12) :
    execInstr (.ADDI (.xreg rd) (.vreg vs1) imm) = vreg_ADDI_to_real rd vs1 imm := rfl

/-- Legacy bridge: real-source virtual-destination `SRAI` is definitionally the
old `vreg_SRAI_from_real` primitive. -/
@[simp] theorem execInstr_vreg_SRAI_from_real (vd : BitVec 7) (rs1 : regidx) (shamt : BitVec 6) :
    execInstr (.SRAI (.vreg vd) (.xreg rs1) shamt) = vreg_SRAI_from_real vd rs1 shamt := rfl

/-- Legacy bridge: virtual-source real-destination `SRAI` is definitionally the
old `vreg_SRAI_to_real` primitive. -/
@[simp] theorem execInstr_vreg_SRAI_to_real (rd : regidx) (vs1 : BitVec 7) (shamt : BitVec 6) :
    execInstr (.SRAI (.xreg rd) (.vreg vs1) shamt) = vreg_SRAI_to_real rd vs1 shamt := rfl

/-- Legacy bridge: virtual-source real-destination `SRLI` is definitionally the
old `vreg_SRLI_to_real` primitive. -/
@[simp] theorem execInstr_vreg_SRLI_to_real (rd : regidx) (vs1 : BitVec 7) (shamt : BitVec 6) :
    execInstr (.SRLI (.xreg rd) (.vreg vs1) shamt) = vreg_SRLI_to_real rd vs1 shamt := rfl

/-- Legacy bridge: virtual-source real-destination `SRL` is definitionally the
old `vreg_SRL_to_real` primitive. -/
@[simp] theorem execInstr_vreg_SRL_to_real (rd : regidx) (vs1 vs2 : BitVec 7) :
    execInstr (.SRL (.xreg rd) (.vreg vs1) (.vreg vs2)) = vreg_SRL_to_real rd vs1 vs2 := rfl

/-- Legacy bridge: real-source `Movsign` is definitionally the old
`vreg_movsign_from_real` primitive. -/
@[simp] theorem execInstr_vreg_movsign_from_real (vd : BitVec 7) (rs1 : regidx) :
    execInstr (.Movsign (.vreg vd) (.xreg rs1)) = vreg_movsign_from_real vd rs1 := rfl

/-- Legacy bridge: real/virtual-source `XOR` is definitionally the old
`vreg_XOR_from_real_vs1` primitive. -/
@[simp] theorem execInstr_vreg_XOR_from_real_vs1 (vd : BitVec 7) (rs1 : regidx) (vs2 : BitVec 7) :
    execInstr (.XOR (.vreg vd) (.xreg rs1) (.vreg vs2)) = vreg_XOR_from_real_vs1 vd rs1 vs2 := rfl

/-- Legacy bridge: virtual/real-source `MUL` is definitionally the old
`vreg_MUL_from_real_vs2` primitive. -/
@[simp] theorem execInstr_vreg_MUL_from_real_vs2 (vd vs1 : BitVec 7) (rs2 : regidx) :
    execInstr (.MUL (.vreg vd) (.vreg vs1) (.xreg rs2)) = vreg_MUL_from_real_vs2 vd vs1 rs2 := rfl

/-- Legacy bridge: real/real-source `MULHU` is definitionally the old
`vreg_MULHU_from_real` primitive. -/
@[simp] theorem execInstr_vreg_MULHU_from_real (vd : BitVec 7) (rs1 rs2 : regidx) :
    execInstr (.MULHU (.vreg vd) (.xreg rs1) (.xreg rs2)) = vreg_MULHU_from_real vd rs1 rs2 := rfl

/-- Legacy bridge: virtual/real-source `MULHU` is definitionally the old
`vreg_MULHU_from_real_vs2` primitive. -/
@[simp] theorem execInstr_vreg_MULHU_from_real_vs2 (vd vs1 : BitVec 7) (rs2 : regidx) :
    execInstr (.MULHU (.vreg vd) (.vreg vs1) (.xreg rs2)) = vreg_MULHU_from_real_vs2 vd vs1 rs2 := rfl

/-- Legacy bridge: real/virtual-source `SUB` is definitionally the old
`vreg_SUB_from_real_vs1` primitive. -/
@[simp] theorem execInstr_vreg_SUB_from_real_vs1 (vd : BitVec 7) (rs1 : regidx) (vs2 : BitVec 7) :
    execInstr (.SUB (.vreg vd) (.xreg rs1) (.vreg vs2)) = vreg_SUB_from_real_vs1 vd rs1 vs2 := rfl

/-- Legacy bridge: virtual-source real-destination `ADD` is definitionally the
old `vreg_ADD_to_real` primitive. -/
@[simp] theorem execInstr_vreg_ADD_to_real (rd : regidx) (vs1 vs2 : BitVec 7) :
    execInstr (.ADD (.xreg rd) (.vreg vs1) (.vreg vs2)) = vreg_ADD_to_real rd vs1 vs2 := rfl

/-- Legacy bridge: typed advice writes are definitionally the old `vreg_advice`
primitive. -/
@[simp] theorem execInstr_vreg_advice (vd : BitVec 7) (value : BitVec 64) :
    execInstr (.Advice vd value) = vreg_advice vd value := rfl

/-- Legacy bridge: typed virtual equality assertions are definitionally the old
`vreg_assert_eq` primitive. -/
@[simp] theorem execInstr_vreg_assert_eq (va vb : BitVec 7) :
    execInstr (.AssertEq va vb) = vreg_assert_eq va vb := rfl

/-- Legacy bridge: typed virtual-vs-real equality assertions are definitionally
the old `vreg_assert_eq_real` primitive. -/
@[simp] theorem execInstr_vreg_assert_eq_real (va : BitVec 7) (rb : regidx) :
    execInstr (.AssertEqReal va rb) = vreg_assert_eq_real va rb := rfl

end JoltISA

end
