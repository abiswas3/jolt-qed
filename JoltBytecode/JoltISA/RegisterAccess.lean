import JoltBytecode.JoltISA.Core
import JoltBytecode.JoltISA.Instruction
/-
# Accessing Data In Registers

Definitions and theorems about accessing data in registers.

when the def/theorem names have the suffix _run this implies we feed it an 
initial state. 
Otherwise, we are defining terms of arrow types.
-/

set_option linter.unusedVariables true

open Sail PreSail LeanRV64D.Functions


noncomputable section

-- Get the value in vr as a monadic computation
def readVReg (vr : BitVec 7) : JoltMonad (BitVec 64) := do
  let js ← get
  pure (js.vregs vr)

-- The general purpose registers are in the Sail hashmap already
-- so we should never write to vr 0-31
def WritableVReg (vr : BitVec 7) : Prop :=
  ¬ vr.toNat < 32

-- We cannot write the to the first 32 registers, as we use xreg for them.
def writeVReg (vr : BitVec 7) (val : BitVec 64) : JoltMonad Unit :=
  if vr.toNat < 32 then
    throw (Error.Assertion "writeVReg: architectural xreg address")
  else
    modify fun js => { js with vregs := fun r => if r = vr then val else js.vregs r }

-- Writing to vr leaves final state as 
theorem writeVReg_run
    (vr : BitVec 7) (val : BitVec 64) (js : SailJoltState) :
    (writeVReg vr val).run js =
      if vr.toNat < 32 then
        .error (Error.Assertion "writeVReg: architectural xreg address") js
      else
        .ok () { js with vregs := fun r => if r = vr then val else js.vregs r } := by
  unfold writeVReg
  by_cases h : vr.toNat < 32
  · simp only [h]
    simp only [↓reduceIte]
    simp only [EStateM.run]
    -- need this full recipe to get rid of the throw
    simp only [throw, throwThe, MonadExceptOf.throw, EStateM.throw]
  · simp only [h, ↓reduceIte]
    simp only [EStateM.run]
    simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

-- Writing to vr when vr is wriable leaves final state as 
-- (this just kills the if statement above)
theorem writeVReg_run_of_writable
    (vr : BitVec 7) (val : BitVec 64) (js : SailJoltState)
    (h : WritableVReg vr) :
    (writeVReg vr val).run js =
      .ok () { js with vregs := fun r => if r = vr then val else js.vregs r } := by
  unfold WritableVReg at h
  rw [writeVReg_run vr val js]
  simp only [h, ↓reduceIte]

/-- Running a virtual-register read returns the value currently stored at that
virtual register and leaves the whole Jolt state unchanged. -/
@[simp] theorem readVReg_run (vr : BitVec 7) (js : SailJoltState) :
    readVReg vr js = .ok (js.vregs vr) js := by
  unfold readVReg get
  rfl

namespace JoltISA

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
