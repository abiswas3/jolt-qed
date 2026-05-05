import JoltBytecode.EmbeddedSailJoltState.JoltISA.Core

/-!
# Jolt ISA operands

Jolt virtual instructions read from and write to either the architectural
register file or the virtual-register file.  The typed source/destination
operands here make those flavours explicit.
-/

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

def readVReg (vr : BitVec 7) : JoltMonad (BitVec 64) := do
  let js ← get
  pure (js.vregs vr)

def writeVReg (vr : BitVec 7) (val : BitVec 64) : JoltMonad Unit :=
  modify fun js => { js with vregs := fun r => if r = vr then val else js.vregs r }

/-- Running a virtual-register read returns the value currently stored at that
virtual register and leaves the whole Jolt state unchanged. -/
@[simp] theorem readVReg_run (vr : BitVec 7) (js : SailJoltState) :
    readVReg vr js = .ok (js.vregs vr) js := by
  unfold readVReg get
  rfl

namespace JoltISA

abbrev VReg := BitVec 7

inductive Src where
  | vreg : VReg → Src
  | xreg : regidx → Src
  deriving Repr

inductive Dst where
  | vreg : VReg → Dst
  | xreg : regidx → Dst
  deriving Repr

def readSrc : Src → JoltMonad (BitVec 64)
  | .vreg vr => readVReg vr
  | .xreg rs => liftSail (rX_bits rs)

def writeDst : Dst → BitVec 64 → JoltMonad Unit
  | .vreg vr, value => writeVReg vr value
  | .xreg rd, value => liftSail (wX_bits rd value)

/-- Reading a virtual-register source is exactly `readVReg`. -/
@[simp] theorem readSrc_vreg (vr : VReg) :
    readSrc (.vreg vr) = readVReg vr := rfl

/-- Reading an architectural-register source is exactly a lifted Sail
`rX_bits` read. -/
@[simp] theorem readSrc_xreg (rs : regidx) :
    readSrc (.xreg rs) = liftSail (rX_bits rs) := rfl

/-- Writing a virtual-register destination is exactly `writeVReg`. -/
@[simp] theorem writeDst_vreg (vr : VReg) (value : BitVec 64) :
    writeDst (.vreg vr) value = writeVReg vr value := rfl

/-- Writing an architectural-register destination is exactly a lifted Sail
`wX_bits` write. -/
@[simp] theorem writeDst_xreg (rd : regidx) (value : BitVec 64) :
    writeDst (.xreg rd) value = liftSail (wX_bits rd value) := rfl

end JoltISA

end
