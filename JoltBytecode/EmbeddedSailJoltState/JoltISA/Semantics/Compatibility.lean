import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics
import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions

/-!
# Compatibility with hand-written virtual instructions
TODO: Not fully clear how this is helpign me clean up the proofs
-- I am not sure I will keep this. 

It seems like bridge between the new world of describing how to describe a progra
and the old do block for an instruction.

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

/-- Direct bridge: real/real-source `MUL` writes the product to a real
destination. -/
@[simp] theorem execInstr_MUL_xreg_xreg_xreg (rd rs1 rs2 : regidx) :
    execInstr (.MUL (.xreg rd) (.xreg rs1) (.xreg rs2)) = (do
      let x ← liftSail (rX_bits rs1)
      let y ← liftSail (rX_bits rs2)
      liftSail (wX_bits rd (x * y))
      pure RETIRE_SUCCESS) := rfl

/-- Direct bridge: real/virtual-source `MUL` writes the product to a real
destination. -/
@[simp] theorem execInstr_MUL_xreg_xreg_vreg (rd rs1 : regidx) (vs2 : BitVec 7) :
    execInstr (.MUL (.xreg rd) (.xreg rs1) (.vreg vs2)) = (do
      let x ← liftSail (rX_bits rs1)
      let y ← readVReg vs2
      liftSail (wX_bits rd (x * y))
      pure RETIRE_SUCCESS) := rfl

/-- Direct bridge: real/real-source `ADD` writes the sum to a real
destination. -/
@[simp] theorem execInstr_ADD_xreg_xreg_xreg (rd rs1 rs2 : regidx) :
    execInstr (.ADD (.xreg rd) (.xreg rs1) (.xreg rs2)) = (do
      let x ← liftSail (rX_bits rs1)
      let y ← liftSail (rX_bits rs2)
      liftSail (wX_bits rd (x + y))
      pure RETIRE_SUCCESS) := rfl

/-- Direct bridge: real/real-source `SUB` writes the difference to a real
destination. -/
@[simp] theorem execInstr_SUB_xreg_xreg_xreg (rd rs1 rs2 : regidx) :
    execInstr (.SUB (.xreg rd) (.xreg rs1) (.xreg rs2)) = (do
      let x ← liftSail (rX_bits rs1)
      let y ← liftSail (rX_bits rs2)
      liftSail (wX_bits rd (x - y))
      pure RETIRE_SUCCESS) := rfl

/-- Direct bridge: real-source `ADDI` writes the immediate sum to a real
destination. -/
@[simp] theorem execInstr_ADDI_xreg_xreg (rd rs1 : regidx) (imm : BitVec 12) :
    execInstr (.ADDI (.xreg rd) (.xreg rs1) imm) = (do
      let x ← liftSail (rX_bits rs1)
      liftSail (wX_bits rd (x + sign_extend (m := 64) imm))
      pure RETIRE_SUCCESS) := rfl

/-- Direct bridge: real-source `SLLI` writes the shifted value to a virtual
destination. -/
@[simp] theorem execInstr_SLLI_vreg_xreg (vd : BitVec 7) (rs1 : regidx) (shamt : BitVec 6) :
    execInstr (.SLLI (.vreg vd) (.xreg rs1) shamt) = (do
      let x ← liftSail (rX_bits rs1)
      writeVReg vd (shift_bits_left x shamt)
      pure RETIRE_SUCCESS) := rfl

/-- Direct bridge: real-source `ORI` writes the immediate-or value to a
virtual destination. -/
@[simp] theorem execInstr_ORI_vreg_xreg (vd : BitVec 7) (rs1 : regidx) (imm : BitVec 12) :
    execInstr (.ORI (.vreg vd) (.xreg rs1) imm) = (do
      let x ← liftSail (rX_bits rs1)
      writeVReg vd (x ||| sign_extend (m := 64) imm)
      pure RETIRE_SUCCESS) := rfl

/-- Direct bridge: real-source `ANDI` writes the immediate-and value to a
virtual destination. -/
@[simp] theorem execInstr_ANDI_vreg_xreg (vd : BitVec 7) (rs1 : regidx) (imm : BitVec 12) :
    execInstr (.ANDI (.vreg vd) (.xreg rs1) imm) = (do
      let x ← liftSail (rX_bits rs1)
      writeVReg vd (x &&& sign_extend (m := 64) imm)
      pure RETIRE_SUCCESS) := rfl

/-- Direct bridge: real-source `SExtW` writes the sign-extended low word to a
virtual destination. -/
@[simp] theorem execInstr_SExtW_vreg_xreg (vd : BitVec 7) (rs1 : regidx) :
    execInstr (.SExtW (.vreg vd) (.xreg rs1)) = (do
      let x ← liftSail (rX_bits rs1)
      writeVReg vd (sign_extend (m := 64) (Sail.BitVec.extractLsb x 31 0))
      pure RETIRE_SUCCESS) := rfl

/-- Direct bridge: real-source `SExtW` writes the sign-extended low word to a
real destination. -/
@[simp] theorem execInstr_SExtW_xreg_xreg_direct (rd rs1 : regidx) :
    execInstr (.SExtW (.xreg rd) (.xreg rs1)) = (do
      let x ← liftSail (rX_bits rs1)
      liftSail (wX_bits rd (sign_extend (m := 64) (Sail.BitVec.extractLsb x 31 0)))
      pure RETIRE_SUCCESS) := rfl

/-- Direct bridge: `VirtualMULI` from a real source to a real destination. -/
@[simp] theorem execInstr_VirtualMULI_xreg_xreg (rd rs1 : regidx) (imm : BitVec 64) :
    execInstr (.VirtualMULI (.xreg rd) (.xreg rs1) imm) = (do
      let x ← liftSail (rX_bits rs1)
      liftSail (wX_bits rd (jolt_virtual_muli_value x imm))
      pure RETIRE_SUCCESS) := rfl

/-- Direct bridge: `VirtualPow2` from a real source to a virtual destination. -/
@[simp] theorem execInstr_VirtualPow2_vreg_xreg (vd : BitVec 7) (rs1 : regidx) :
    execInstr (.VirtualPow2 (.vreg vd) (.xreg rs1)) = (do
      let x ← liftSail (rX_bits rs1)
      writeVReg vd (jolt_virtual_pow2_value x)
      pure RETIRE_SUCCESS) := rfl

/-- Direct bridge: `VirtualPow2W` from a real source to a virtual destination. -/
@[simp] theorem execInstr_VirtualPow2W_vreg_xreg (vd : BitVec 7) (rs1 : regidx) :
    execInstr (.VirtualPow2W (.vreg vd) (.xreg rs1)) = (do
      let x ← liftSail (rX_bits rs1)
      writeVReg vd (jolt_virtual_pow2w_value x)
      pure RETIRE_SUCCESS) := rfl

/-- Direct bridge: `VirtualShiftRightBitmask` from a real source to a virtual
destination. -/
@[simp] theorem execInstr_VirtualShiftRightBitmask_vreg_xreg (vd : BitVec 7) (rs1 : regidx) :
    execInstr (.VirtualShiftRightBitmask (.vreg vd) (.xreg rs1)) = (do
      let x ← liftSail (rX_bits rs1)
      writeVReg vd (jolt_virtual_shift_right_bitmask_value x)
      pure RETIRE_SUCCESS) := rfl

/-- Direct bridge: `VirtualShiftRightBitmask` from a virtual source to a
virtual destination. -/
@[simp] theorem execInstr_VirtualShiftRightBitmask_vreg_vreg (vd vs1 : BitVec 7) :
    execInstr (.VirtualShiftRightBitmask (.vreg vd) (.vreg vs1)) = (do
      let x ← readVReg vs1
      writeVReg vd (jolt_virtual_shift_right_bitmask_value x)
      pure RETIRE_SUCCESS) := rfl

/-- Direct bridge: `VirtualSRLI` from a real source to a real destination. -/
@[simp] theorem execInstr_VirtualSRLI_xreg_xreg (rd rs1 : regidx) (bitmask : Nat) :
    execInstr (.VirtualSRLI (.xreg rd) (.xreg rs1) bitmask) = (do
      let x ← liftSail (rX_bits rs1)
      liftSail (wX_bits rd (jolt_virtual_srli_value x bitmask))
      pure RETIRE_SUCCESS) := rfl

/-- Direct bridge: `VirtualSRLI` from a virtual source to a real destination. -/
@[simp] theorem execInstr_VirtualSRLI_xreg_vreg (rd : regidx) (vs1 : BitVec 7) (bitmask : Nat) :
    execInstr (.VirtualSRLI (.xreg rd) (.vreg vs1) bitmask) = (do
      let x ← readVReg vs1
      liftSail (wX_bits rd (jolt_virtual_srli_value x bitmask))
      pure RETIRE_SUCCESS) := rfl

/-- Direct bridge: `VirtualSRAI` from a real source to a real destination. -/
@[simp] theorem execInstr_VirtualSRAI_xreg_xreg (rd rs1 : regidx) (bitmask : Nat) :
    execInstr (.VirtualSRAI (.xreg rd) (.xreg rs1) bitmask) = (do
      let x ← liftSail (rX_bits rs1)
      liftSail (wX_bits rd (jolt_virtual_srai_value x bitmask))
      pure RETIRE_SUCCESS) := rfl

/-- Direct bridge: `VirtualSRAI` from a virtual source to a real destination. -/
@[simp] theorem execInstr_VirtualSRAI_xreg_vreg (rd : regidx) (vs1 : BitVec 7) (bitmask : Nat) :
    execInstr (.VirtualSRAI (.xreg rd) (.vreg vs1) bitmask) = (do
      let x ← readVReg vs1
      liftSail (wX_bits rd (jolt_virtual_srai_value x bitmask))
      pure RETIRE_SUCCESS) := rfl

/-- Direct bridge: `VirtualSRL` from real value and virtual bitmask to a real
destination. -/
@[simp] theorem execInstr_VirtualSRL_xreg_xreg_vreg (rd rs1 : regidx) (vbitmask : BitVec 7) :
    execInstr (.VirtualSRL (.xreg rd) (.xreg rs1) (.vreg vbitmask)) = (do
      let x ← liftSail (rX_bits rs1)
      let b ← readVReg vbitmask
      liftSail (wX_bits rd (jolt_virtual_srl_value x b))
      pure RETIRE_SUCCESS) := rfl

/-- Direct bridge: `VirtualSRL` from virtual value and virtual bitmask to a
real destination. -/
@[simp] theorem execInstr_VirtualSRL_xreg_vreg_vreg (rd : regidx) (vvalue vbitmask : BitVec 7) :
    execInstr (.VirtualSRL (.xreg rd) (.vreg vvalue) (.vreg vbitmask)) = (do
      let x ← readVReg vvalue
      let b ← readVReg vbitmask
      liftSail (wX_bits rd (jolt_virtual_srl_value x b))
      pure RETIRE_SUCCESS) := rfl

/-- Direct bridge: `VirtualSRA` from real value and virtual bitmask to a real
destination. -/
@[simp] theorem execInstr_VirtualSRA_xreg_xreg_vreg (rd rs1 : regidx) (vbitmask : BitVec 7) :
    execInstr (.VirtualSRA (.xreg rd) (.xreg rs1) (.vreg vbitmask)) = (do
      let x ← liftSail (rX_bits rs1)
      let b ← readVReg vbitmask
      liftSail (wX_bits rd (jolt_virtual_sra_value x b))
      pure RETIRE_SUCCESS) := rfl

/-- Direct bridge: `VirtualSRA` from virtual value and virtual bitmask to a
real destination. -/
@[simp] theorem execInstr_VirtualSRA_xreg_vreg_vreg (rd : regidx) (vvalue vbitmask : BitVec 7) :
    execInstr (.VirtualSRA (.xreg rd) (.vreg vvalue) (.vreg vbitmask)) = (do
      let x ← readVReg vvalue
      let b ← readVReg vbitmask
      liftSail (wX_bits rd (jolt_virtual_sra_value x b))
      pure RETIRE_SUCCESS) := rfl

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
