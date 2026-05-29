import JoltBytecode.JoltISA.Operands

/-!
# Rust virtual-register allocation layout

The Lean Jolt-ISA programs use the same absolute virtual-register numbers as
`tracer/src/utils/virtual_registers.rs`.

Rust reserves virtual registers `32..39` for persistent architectural state,
uses `40..47` for the per-instruction `allocate()` scratch pool, and starts
larger inline allocations at `48`.
-/

namespace JoltISA

/-- Number of architectural RISC-V integer registers; virtual registers start
immediately after this base. -/
def riscvRegisterBase : Nat := 32

/-- First virtual register reserved for instruction-local temporaries. -/
def inlineRegisterBase : Nat := riscvRegisterBase + 8

/-- First virtual register reserved for larger inline allocations. -/
def largeInlineRegisterBase : Nat := inlineRegisterBase + 8

/-- Rust allocator's word-reservation virtual register, register 32. -/
def reservationWReg : VReg := BitVec.ofNat 7 (riscvRegisterBase + 0)

/-- Rust allocator's dword-reservation virtual register, register 33. -/
def reservationDReg : VReg := BitVec.ofNat 7 (riscvRegisterBase + 1)

/-- Rust allocator's trap-handler/`mtvec` virtual register, register 34. -/
def trapHandlerVReg : VReg := BitVec.ofNat 7 (riscvRegisterBase + 2)

/-- Rust allocator's `mscratch` virtual register, register 35. -/
def mscratchVReg : VReg := BitVec.ofNat 7 (riscvRegisterBase + 3)

/-- Rust allocator's `mepc` virtual register, register 36. -/
def mepcVReg : VReg := BitVec.ofNat 7 (riscvRegisterBase + 4)

/-- Rust allocator's `mcause` virtual register, register 37. -/
def mcauseVReg : VReg := BitVec.ofNat 7 (riscvRegisterBase + 5)

/-- Rust allocator's `mtval` virtual register, register 38. -/
def mtvalVReg : VReg := BitVec.ofNat 7 (riscvRegisterBase + 6)

/-- Rust allocator's `mstatus` virtual register, register 39. -/
def mstatusVReg : VReg := BitVec.ofNat 7 (riscvRegisterBase + 7)

/-- The `n`th register returned by Rust `allocate()`, starting at register 40. -/
def inlineTmp (n : Nat) : VReg := BitVec.ofNat 7 (inlineRegisterBase + n)

/-- The `n`th register returned by Rust `allocate_for_inline()`, starting at
register 48. -/
def largeInlineTmp (n : Nat) : VReg := BitVec.ofNat 7 (largeInlineRegisterBase + n)

/-!
## Tiny model of Rust virtual-register allocation

Rust's `VirtualRegisterAllocator::allocate()` scans the instruction-local pool
`40..47` and returns the first non-live register.  `VirtualRegisterGuard::drop`
marks that register free again, which is why nested inline expansions can reuse
the same scratch after the recursive call returns.

The model below tracks live indices relative to each Rust pool:
`0` denotes register `40` for `allocate()` and register `48` for
`allocate_for_inline()`.
-/

/-- Rust's `NUM_VIRTUAL_INSTRUCTION_REGISTERS`. -/
def numVirtualInstructionRegisters : Nat := 8

/-- Live indices for Rust `allocate()`, relative to register 40. -/
abbrev InstructionLiveSet := List Nat

/-- Live indices for Rust `allocate_for_inline()`, relative to register 48. -/
abbrev LargeInlineLiveSet := List Nat

/-- First free instruction-local index, matching Rust `allocate()`'s scan. -/
def firstFreeInstructionIndex (live : InstructionLiveSet) : Option Nat :=
  (List.range numVirtualInstructionRegisters).find? fun n =>
    !live.contains n

/-- Rust `allocate()` on the small instruction-local pool. -/
def allocateInstructionRegister
    (live : InstructionLiveSet) : Option (VReg × InstructionLiveSet) :=
  match firstFreeInstructionIndex live with
  | some n => some (inlineTmp n, n :: live)
  | none => none

/-- Rust `VirtualRegisterGuard::drop` for a small instruction-local register. -/
def dropInstructionRegister (n : Nat) (live : InstructionLiveSet) :
    InstructionLiveSet :=
  live.erase n

/-- Rust `allocate_for_inline()` scans the large inline pool from register 48. -/
def firstFreeLargeInlineIndex (live : LargeInlineLiveSet) : Nat :=
  (List.range live.length).foldl (fun candidate n =>
    if live.contains candidate then n + 1 else candidate) 0

/-- Rust `allocate_for_inline()` on the large inline pool. -/
def allocateLargeInlineRegister
    (live : LargeInlineLiveSet) : VReg × LargeInlineLiveSet :=
  let n := firstFreeLargeInlineIndex live
  (largeInlineTmp n, n :: live)

/-- Rust `VirtualRegisterGuard::drop` for a large inline register. -/
def dropLargeInlineRegister (n : Nat) (live : LargeInlineLiveSet) :
    LargeInlineLiveSet :=
  live.erase n

/-- With no live temporaries, Rust `allocate()` returns register 40. -/
theorem allocateInstructionRegister_nil :
    allocateInstructionRegister [] = some (inlineTmp 0, [0]) := by
  decide

/-- With `v0` live, Rust `allocate()` returns register 41. -/
theorem allocateInstructionRegister_live_0 :
    allocateInstructionRegister [0] = some (inlineTmp 1, [1, 0]) := by
  decide

/-- With `v0,v1` live, Rust `allocate()` returns register 42. -/
theorem allocateInstructionRegister_live_0_1 :
    allocateInstructionRegister [0, 1] = some (inlineTmp 2, [2, 0, 1]) := by
  decide

/-- With `v0..v2` live, Rust `allocate()` returns register 43. -/
theorem allocateInstructionRegister_live_0_1_2 :
    allocateInstructionRegister [0, 1, 2] =
      some (inlineTmp 3, [3, 0, 1, 2]) := by
  decide

/-- With `v0..v3` live, Rust `allocate()` returns register 44. -/
theorem allocateInstructionRegister_live_0_1_2_3 :
    allocateInstructionRegister [0, 1, 2, 3] =
      some (inlineTmp 4, [4, 0, 1, 2, 3]) := by
  decide

/-- With `v0..v4` live, Rust `allocate()` returns register 45. -/
theorem allocateInstructionRegister_live_0_1_2_3_4 :
    allocateInstructionRegister [0, 1, 2, 3, 4] =
      some (inlineTmp 5, [5, 0, 1, 2, 3, 4]) := by
  decide

/-- Dropping the nested scratch from a live `v0..v4,v5` set exposes `v5`
for the next recursive inline expansion. -/
theorem dropInstructionRegister_5_after_live_0_to_5 :
    dropInstructionRegister 5 [5, 0, 1, 2, 3, 4] =
      [0, 1, 2, 3, 4] := by
  decide

/-- First Rust `allocate()` scratch register, register 40. -/
def inlineTmp0 : VReg := inlineTmp 0

/-- Second Rust `allocate()` scratch register, register 41. -/
def inlineTmp1 : VReg := inlineTmp 1

/-- Third Rust `allocate()` scratch register, register 42. -/
def inlineTmp2 : VReg := inlineTmp 2

/-- Fourth Rust `allocate()` scratch register, register 43. -/
def inlineTmp3 : VReg := inlineTmp 3

/-- Fifth Rust `allocate()` scratch register, register 44. -/
def inlineTmp4 : VReg := inlineTmp 4

/-- Sixth Rust `allocate()` scratch register, register 45. -/
def inlineTmp5 : VReg := inlineTmp 5

/-- Seventh Rust `allocate()` scratch register, register 46. -/
def inlineTmp6 : VReg := inlineTmp 6

/-- Eighth Rust `allocate()` scratch register, register 47. -/
def inlineTmp7 : VReg := inlineTmp 7

/- The Rust `allocate()` scratch aliases denote distinct physical virtual
registers.  These small facts let proof code talk in names instead of raw
numbers while still discharging preservation side conditions directly. -/
@[simp] theorem inlineTmp0_ne_inlineTmp1 : inlineTmp0 ≠ inlineTmp1 := by decide
@[simp] theorem inlineTmp1_ne_inlineTmp0 : inlineTmp1 ≠ inlineTmp0 := by decide
@[simp] theorem inlineTmp0_ne_inlineTmp2 : inlineTmp0 ≠ inlineTmp2 := by decide
@[simp] theorem inlineTmp2_ne_inlineTmp0 : inlineTmp2 ≠ inlineTmp0 := by decide
@[simp] theorem inlineTmp0_ne_inlineTmp3 : inlineTmp0 ≠ inlineTmp3 := by decide
@[simp] theorem inlineTmp3_ne_inlineTmp0 : inlineTmp3 ≠ inlineTmp0 := by decide
@[simp] theorem inlineTmp0_ne_inlineTmp4 : inlineTmp0 ≠ inlineTmp4 := by decide
@[simp] theorem inlineTmp4_ne_inlineTmp0 : inlineTmp4 ≠ inlineTmp0 := by decide
@[simp] theorem inlineTmp0_ne_inlineTmp5 : inlineTmp0 ≠ inlineTmp5 := by decide
@[simp] theorem inlineTmp5_ne_inlineTmp0 : inlineTmp5 ≠ inlineTmp0 := by decide
@[simp] theorem inlineTmp0_ne_inlineTmp6 : inlineTmp0 ≠ inlineTmp6 := by decide
@[simp] theorem inlineTmp6_ne_inlineTmp0 : inlineTmp6 ≠ inlineTmp0 := by decide
@[simp] theorem inlineTmp0_ne_inlineTmp7 : inlineTmp0 ≠ inlineTmp7 := by decide
@[simp] theorem inlineTmp7_ne_inlineTmp0 : inlineTmp7 ≠ inlineTmp0 := by decide

@[simp] theorem inlineTmp1_ne_inlineTmp2 : inlineTmp1 ≠ inlineTmp2 := by decide
@[simp] theorem inlineTmp2_ne_inlineTmp1 : inlineTmp2 ≠ inlineTmp1 := by decide
@[simp] theorem inlineTmp1_ne_inlineTmp3 : inlineTmp1 ≠ inlineTmp3 := by decide
@[simp] theorem inlineTmp3_ne_inlineTmp1 : inlineTmp3 ≠ inlineTmp1 := by decide
@[simp] theorem inlineTmp1_ne_inlineTmp4 : inlineTmp1 ≠ inlineTmp4 := by decide
@[simp] theorem inlineTmp4_ne_inlineTmp1 : inlineTmp4 ≠ inlineTmp1 := by decide
@[simp] theorem inlineTmp1_ne_inlineTmp5 : inlineTmp1 ≠ inlineTmp5 := by decide
@[simp] theorem inlineTmp5_ne_inlineTmp1 : inlineTmp5 ≠ inlineTmp1 := by decide
@[simp] theorem inlineTmp1_ne_inlineTmp6 : inlineTmp1 ≠ inlineTmp6 := by decide
@[simp] theorem inlineTmp6_ne_inlineTmp1 : inlineTmp6 ≠ inlineTmp1 := by decide
@[simp] theorem inlineTmp1_ne_inlineTmp7 : inlineTmp1 ≠ inlineTmp7 := by decide
@[simp] theorem inlineTmp7_ne_inlineTmp1 : inlineTmp7 ≠ inlineTmp1 := by decide

@[simp] theorem inlineTmp2_ne_inlineTmp3 : inlineTmp2 ≠ inlineTmp3 := by decide
@[simp] theorem inlineTmp3_ne_inlineTmp2 : inlineTmp3 ≠ inlineTmp2 := by decide
@[simp] theorem inlineTmp2_ne_inlineTmp4 : inlineTmp2 ≠ inlineTmp4 := by decide
@[simp] theorem inlineTmp4_ne_inlineTmp2 : inlineTmp4 ≠ inlineTmp2 := by decide
@[simp] theorem inlineTmp2_ne_inlineTmp5 : inlineTmp2 ≠ inlineTmp5 := by decide
@[simp] theorem inlineTmp5_ne_inlineTmp2 : inlineTmp5 ≠ inlineTmp2 := by decide
@[simp] theorem inlineTmp2_ne_inlineTmp6 : inlineTmp2 ≠ inlineTmp6 := by decide
@[simp] theorem inlineTmp6_ne_inlineTmp2 : inlineTmp6 ≠ inlineTmp2 := by decide
@[simp] theorem inlineTmp2_ne_inlineTmp7 : inlineTmp2 ≠ inlineTmp7 := by decide
@[simp] theorem inlineTmp7_ne_inlineTmp2 : inlineTmp7 ≠ inlineTmp2 := by decide

@[simp] theorem inlineTmp3_ne_inlineTmp4 : inlineTmp3 ≠ inlineTmp4 := by decide
@[simp] theorem inlineTmp4_ne_inlineTmp3 : inlineTmp4 ≠ inlineTmp3 := by decide
@[simp] theorem inlineTmp3_ne_inlineTmp5 : inlineTmp3 ≠ inlineTmp5 := by decide
@[simp] theorem inlineTmp5_ne_inlineTmp3 : inlineTmp5 ≠ inlineTmp3 := by decide
@[simp] theorem inlineTmp3_ne_inlineTmp6 : inlineTmp3 ≠ inlineTmp6 := by decide
@[simp] theorem inlineTmp6_ne_inlineTmp3 : inlineTmp6 ≠ inlineTmp3 := by decide
@[simp] theorem inlineTmp3_ne_inlineTmp7 : inlineTmp3 ≠ inlineTmp7 := by decide
@[simp] theorem inlineTmp7_ne_inlineTmp3 : inlineTmp7 ≠ inlineTmp3 := by decide

@[simp] theorem inlineTmp4_ne_inlineTmp5 : inlineTmp4 ≠ inlineTmp5 := by decide
@[simp] theorem inlineTmp5_ne_inlineTmp4 : inlineTmp5 ≠ inlineTmp4 := by decide
@[simp] theorem inlineTmp4_ne_inlineTmp6 : inlineTmp4 ≠ inlineTmp6 := by decide
@[simp] theorem inlineTmp6_ne_inlineTmp4 : inlineTmp6 ≠ inlineTmp4 := by decide
@[simp] theorem inlineTmp4_ne_inlineTmp7 : inlineTmp4 ≠ inlineTmp7 := by decide
@[simp] theorem inlineTmp7_ne_inlineTmp4 : inlineTmp7 ≠ inlineTmp4 := by decide

@[simp] theorem inlineTmp5_ne_inlineTmp6 : inlineTmp5 ≠ inlineTmp6 := by decide
@[simp] theorem inlineTmp6_ne_inlineTmp5 : inlineTmp6 ≠ inlineTmp5 := by decide
@[simp] theorem inlineTmp5_ne_inlineTmp7 : inlineTmp5 ≠ inlineTmp7 := by decide
@[simp] theorem inlineTmp7_ne_inlineTmp5 : inlineTmp7 ≠ inlineTmp5 := by decide

@[simp] theorem inlineTmp6_ne_inlineTmp7 : inlineTmp6 ≠ inlineTmp7 := by decide
@[simp] theorem inlineTmp7_ne_inlineTmp6 : inlineTmp7 ≠ inlineTmp6 := by decide

end JoltISA
