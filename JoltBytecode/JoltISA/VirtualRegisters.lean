import JoltBytecode.JoltISA.RegisterAccess

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
immediately after this base.

Rust name/source: `RISCV_REGISTER_COUNT`,
`common/src/constants.rs:2`.
-/
def riscvRegisterCount : Nat := 32

/-- Number of Jolt virtual registers after the architectural register block.
Rust name/source: `VIRTUAL_REGISTER_COUNT`,
`common/src/constants.rs:3`.
-/
def virtualRegisterCount : Nat := 96

/-- Total Jolt register-address space. Rust keeps this at `128`, a power of two.

Rust name/source: `REGISTER_COUNT`,
`common/src/constants.rs:5`.
-/
def totalRegisterCount : Nat := riscvRegisterCount + virtualRegisterCount

/-- Number of persistent virtual registers skipped by both Rust allocators.

Rust name/source: `NUM_RESERVED_VIRTUAL_REGISTERS`,
`tracer/src/utils/virtual_registers.rs:48-52`,
`crates/jolt-program/src/expand/allocator.rs:8`.
-/
def numReservedVirtualRegisters : Nat := 8

/-- Number of short-lived instruction virtual registers.

Rust name/source: `NUM_VIRTUAL_INSTRUCTION_REGISTERS`,
`tracer/src/utils/virtual_registers.rs:6-10`,
`crates/jolt-program/src/expand/allocator.rs:6`.
-/
def numVirtualInstructionRegisters : Nat := 8

/-- Number of virtual registers available to `allocate_for_inline()`.

Rust name/source: `NUM_INLINE_REGISTERS`,
`crates/jolt-program/src/expand/allocator.rs:9-13`.
-/
def numLargeInlineRegisters : Nat :=
  virtualRegisterCount - numReservedVirtualRegisters -
    numVirtualInstructionRegisters

/-- First Jolt virtual register.

Rust name/source: `RISCV_REGISTER_BASE`,
`tracer/src/utils/virtual_registers.rs:11`,
`crates/jolt-program/src/expand/allocator.rs:7`.
-/
def riscvRegisterBase : Nat := riscvRegisterCount

/-- First virtual register reserved for instruction-local temporaries.

Rust source: `allocate()` skips `NUM_RESERVED_VIRTUAL_REGISTERS`,
`tracer/src/utils/virtual_registers.rs:132-144`,
`crates/jolt-program/src/expand/allocator.rs:133-143`.
-/
def inlineRegisterBase : Nat := riscvRegisterBase + numReservedVirtualRegisters

/-- First virtual register reserved for larger inline allocations.

Rust name/source: `FIRST_INLINE_REGISTER`,
`crates/jolt-program/src/expand/allocator.rs:9-13`;
tracer `allocate_for_inline()` skips reserved and instruction registers at
`tracer/src/utils/virtual_registers.rs:157-164`.
-/
def largeInlineRegisterBase : Nat :=
  inlineRegisterBase + numVirtualInstructionRegisters

/-- Rust allocator's word-reservation virtual register, register 32.

Rust names/source: `RESERVATION_W_REGISTER`, `reservation_w_register()`,
`tracer/src/utils/virtual_registers.rs:37`, `:70-72`,
`crates/jolt-program/src/expand/allocator.rs:16`, `:32-34`.
-/
def reservationWReg : VReg := BitVec.ofNat 7 (riscvRegisterBase + 0)

/-- Rust allocator's dword-reservation virtual register, register 33.

Rust names/source: `RESERVATION_D_REGISTER`, `reservation_d_register()`,
`tracer/src/utils/virtual_registers.rs:38`, `:75-77`,
`crates/jolt-program/src/expand/allocator.rs:17`, `:36-38`.
-/
def reservationDReg : VReg := BitVec.ofNat 7 (riscvRegisterBase + 1)

/-- Rust allocator's trap-handler/`mtvec` virtual register, register 34.

Rust names/source: `TRAP_HANDLER_REGISTER`, `trap_handler_register()`,
`tracer/src/utils/virtual_registers.rs:41`, `:80-82`,
`crates/jolt-program/src/expand/allocator.rs:18`, `:40-42`.
-/
def trapHandlerVReg : VReg := BitVec.ofNat 7 (riscvRegisterBase + 2)

/-- Rust allocator's `mscratch` virtual register, register 35.

Rust names/source: `MSCRATCH_REGISTER`, `mscratch_register()`,
`tracer/src/utils/virtual_registers.rs:42`, `:85-87`,
`crates/jolt-program/src/expand/allocator.rs:19`, `:72-74`.
-/
def mscratchVReg : VReg := BitVec.ofNat 7 (riscvRegisterBase + 3)

/-- Rust allocator's `mepc` virtual register, register 36.

Rust names/source: `MEPC_REGISTER`, `mepc_register()`,
`tracer/src/utils/virtual_registers.rs:43`, `:90-92`,
`crates/jolt-program/src/expand/allocator.rs:20`, `:44-46`.
-/
def mepcVReg : VReg := BitVec.ofNat 7 (riscvRegisterBase + 4)

/-- Rust allocator's `mcause` virtual register, register 37.

Rust names/source: `MCAUSE_REGISTER`, `mcause_register()`,
`tracer/src/utils/virtual_registers.rs:44`, `:95-97`,
`crates/jolt-program/src/expand/allocator.rs:21`, `:48-50`.
-/
def mcauseVReg : VReg := BitVec.ofNat 7 (riscvRegisterBase + 5)

/-- Rust allocator's `mtval` virtual register, register 38.

Rust names/source: `MTVAL_REGISTER`, `mtval_register()`,
`tracer/src/utils/virtual_registers.rs:45`, `:100-102`,
`crates/jolt-program/src/expand/allocator.rs:22`, `:52-54`.
-/
def mtvalVReg : VReg := BitVec.ofNat 7 (riscvRegisterBase + 6)

/-- Rust allocator's `mstatus` virtual register, register 39.

Rust names/source: `MSTATUS_REGISTER`, `mstatus_register()`,
`tracer/src/utils/virtual_registers.rs:46`, `:105-107`,
`crates/jolt-program/src/expand/allocator.rs:23`, `:56-58`.
-/
def mstatusVReg : VReg := BitVec.ofNat 7 (riscvRegisterBase + 7)

/-- The `n`th register returned by Rust `allocate()`, starting at register 40.

Rust name/source: `allocate()`,
`tracer/src/utils/virtual_registers.rs:132-144`,
`crates/jolt-program/src/expand/allocator.rs:133-143`.
-/
def inlineTmp (n : Nat) : VReg := BitVec.ofNat 7 (inlineRegisterBase + n)

/-- The `n`th register returned by Rust `allocate_for_inline()`, starting at
register 48.

Rust name/source: `allocate_for_inline()`,
`tracer/src/utils/virtual_registers.rs:157-164`,
`crates/jolt-program/src/expand/allocator.rs:146-156`.
-/
def largeInlineTmp (n : Nat) : VReg := BitVec.ofNat 7 (largeInlineRegisterBase + n)

/-!
## Total Jolt register-address map

Rust uses one 7-bit register address space:

* `0..31` are architectural RISC-V integer registers;
* `32..39` are persistent virtual registers never returned by an allocator;
* `40..47` are the short-lived `allocate()` pool;
* `48..127` are the `allocate_for_inline()` pool.

The definition below is the single total classifier for that address space.
Projection, preservation, and allocator lemmas should be derived from it.
-/

/-- Meaning of one address in Jolt's 7-bit register space. -/
inductive JoltRegisterSlot where
  | xreg (idx : regidx)
  | reservationW
  | reservationD
  | mtvec
  | mscratch
  | mepc
  | mcause
  | mtval
  | mstatus
  | instructionTmp (idx : Nat)
  | largeInlineTmp (idx : Nat)

/-- Total Rust/Jolt register-address classifier for every `BitVec 7`. -/
def joltRegisterSlot (r : VReg) : JoltRegisterSlot :=
  match r.toNat with
  | 0 => .xreg (regidx.Regidx (BitVec.ofNat 5 0))
  | 1 => .xreg (regidx.Regidx (BitVec.ofNat 5 1))
  | 2 => .xreg (regidx.Regidx (BitVec.ofNat 5 2))
  | 3 => .xreg (regidx.Regidx (BitVec.ofNat 5 3))
  | 4 => .xreg (regidx.Regidx (BitVec.ofNat 5 4))
  | 5 => .xreg (regidx.Regidx (BitVec.ofNat 5 5))
  | 6 => .xreg (regidx.Regidx (BitVec.ofNat 5 6))
  | 7 => .xreg (regidx.Regidx (BitVec.ofNat 5 7))
  | 8 => .xreg (regidx.Regidx (BitVec.ofNat 5 8))
  | 9 => .xreg (regidx.Regidx (BitVec.ofNat 5 9))
  | 10 => .xreg (regidx.Regidx (BitVec.ofNat 5 10))
  | 11 => .xreg (regidx.Regidx (BitVec.ofNat 5 11))
  | 12 => .xreg (regidx.Regidx (BitVec.ofNat 5 12))
  | 13 => .xreg (regidx.Regidx (BitVec.ofNat 5 13))
  | 14 => .xreg (regidx.Regidx (BitVec.ofNat 5 14))
  | 15 => .xreg (regidx.Regidx (BitVec.ofNat 5 15))
  | 16 => .xreg (regidx.Regidx (BitVec.ofNat 5 16))
  | 17 => .xreg (regidx.Regidx (BitVec.ofNat 5 17))
  | 18 => .xreg (regidx.Regidx (BitVec.ofNat 5 18))
  | 19 => .xreg (regidx.Regidx (BitVec.ofNat 5 19))
  | 20 => .xreg (regidx.Regidx (BitVec.ofNat 5 20))
  | 21 => .xreg (regidx.Regidx (BitVec.ofNat 5 21))
  | 22 => .xreg (regidx.Regidx (BitVec.ofNat 5 22))
  | 23 => .xreg (regidx.Regidx (BitVec.ofNat 5 23))
  | 24 => .xreg (regidx.Regidx (BitVec.ofNat 5 24))
  | 25 => .xreg (regidx.Regidx (BitVec.ofNat 5 25))
  | 26 => .xreg (regidx.Regidx (BitVec.ofNat 5 26))
  | 27 => .xreg (regidx.Regidx (BitVec.ofNat 5 27))
  | 28 => .xreg (regidx.Regidx (BitVec.ofNat 5 28))
  | 29 => .xreg (regidx.Regidx (BitVec.ofNat 5 29))
  | 30 => .xreg (regidx.Regidx (BitVec.ofNat 5 30))
  | 31 => .xreg (regidx.Regidx (BitVec.ofNat 5 31))
  | 32 => .reservationW
  | 33 => .reservationD
  | 34 => .mtvec
  | 35 => .mscratch
  | 36 => .mepc
  | 37 => .mcause
  | 38 => .mtval
  | 39 => .mstatus
  | 40 => .instructionTmp 0
  | 41 => .instructionTmp 1
  | 42 => .instructionTmp 2
  | 43 => .instructionTmp 3
  | 44 => .instructionTmp 4
  | 45 => .instructionTmp 5
  | 46 => .instructionTmp 6
  | 47 => .instructionTmp 7
  | n => .largeInlineTmp (n - largeInlineRegisterBase)

/-- The generated Sail register materialized by this Jolt register address, if
any. Most Jolt register addresses do not project into a generated Sail register. -/
def JoltRegisterSlot.sailRegister? : JoltRegisterSlot → Option Register
  | .mtvec => some Register.mtvec
  | .mscratch => some Register.mscratch
  | .mepc => some Register.mepc
  | .mcause => some Register.mcause
  | .mtval => some Register.mtval
  | .mstatus => some Register.mstatus
  | _ => none

/-- The CSR address represented by this Jolt register address, if any. -/
def JoltRegisterSlot.csrAddress? : JoltRegisterSlot → Option (BitVec 12)
  | .mstatus => some 0x300#12
  | .mtvec => some 0x305#12
  | .mscratch => some 0x340#12
  | .mepc => some 0x341#12
  | .mcause => some 0x342#12
  | .mtval => some 0x343#12
  | _ => none

/-- Projection target for one Jolt register address, derived from
`joltRegisterSlot`. -/
def joltRegisterSailTarget? (r : VReg) : Option Register :=
  (joltRegisterSlot r).sailRegister?

/-- CSR address for one Jolt register address, derived from `joltRegisterSlot`. -/
def joltRegisterCsrAddress? (r : VReg) : Option (BitVec 12) :=
  (joltRegisterSlot r).csrAddress?

/-- True exactly for Jolt register addresses that are semantically protected:
architectural integer-register addresses and persistent CSR virtual registers.
Short-lived allocator scratch registers are not protected by this predicate. -/
def JoltRegisterSlot.isProtected : JoltRegisterSlot → Bool
  | .xreg _ => true
  -- LR/SC reservation virtual registers are Jolt bookkeeping, not RISC-visible
  -- architectural state. LR/SC proofs will need their own reservation contract.
  | .reservationW => false
  | .reservationD => false
  | .mtvec => true
  | .mscratch => true
  | .mepc => true
  | .mcause => true
  | .mtval => true
  | .mstatus => true
  | .instructionTmp _ => false
  | .largeInlineTmp _ => false

/-- Jolt register addresses that must not be clobbered by instruction-local
scratch use. This hides the Rust allocator range split behind the total
register-address classifier. -/
def IsProtectedJoltRegister (r : VReg) : Prop :=
  (joltRegisterSlot r).isProtected = true

/-!
The reserved CSR entries below are Jolt ISA layout facts.  They reduce by
`rfl`; later proofs should not re-assume this mapping.
-/

@[simp] theorem joltRegisterSailTarget_trapHandlerVReg :
    joltRegisterSailTarget? trapHandlerVReg = some Register.mtvec := rfl

@[simp] theorem joltRegisterSailTarget_mscratchVReg :
    joltRegisterSailTarget? mscratchVReg = some Register.mscratch := rfl

@[simp] theorem joltRegisterSailTarget_mepcVReg :
    joltRegisterSailTarget? mepcVReg = some Register.mepc := rfl

@[simp] theorem joltRegisterSailTarget_mcauseVReg :
    joltRegisterSailTarget? mcauseVReg = some Register.mcause := rfl

@[simp] theorem joltRegisterSailTarget_mtvalVReg :
    joltRegisterSailTarget? mtvalVReg = some Register.mtval := rfl

@[simp] theorem joltRegisterSailTarget_mstatusVReg :
    joltRegisterSailTarget? mstatusVReg = some Register.mstatus := rfl

@[simp] theorem joltRegisterCsrAddress_trapHandlerVReg :
    joltRegisterCsrAddress? trapHandlerVReg = some 0x305#12 := rfl

@[simp] theorem joltRegisterCsrAddress_mscratchVReg :
    joltRegisterCsrAddress? mscratchVReg = some 0x340#12 := rfl

@[simp] theorem joltRegisterCsrAddress_mepcVReg :
    joltRegisterCsrAddress? mepcVReg = some 0x341#12 := rfl

@[simp] theorem joltRegisterCsrAddress_mcauseVReg :
    joltRegisterCsrAddress? mcauseVReg = some 0x342#12 := rfl

@[simp] theorem joltRegisterCsrAddress_mtvalVReg :
    joltRegisterCsrAddress? mtvalVReg = some 0x343#12 := rfl

@[simp] theorem joltRegisterCsrAddress_mstatusVReg :
    joltRegisterCsrAddress? mstatusVReg = some 0x300#12 := rfl

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

/-- Any Jolt register classified as instruction-local scratch is not
protected. -/
theorem not_protected_of_instructionTmp {r : VReg} {n : Nat}
    (h : joltRegisterSlot r = .instructionTmp n) :
    ¬ IsProtectedJoltRegister r := by
  unfold IsProtectedJoltRegister
  rw [h]
  simp [JoltRegisterSlot.isProtected]

/-- A protected Jolt register cannot be an unprotected scratch register. -/
theorem protected_ne_of_not_protected {r scratch : VReg}
    (hprotected : IsProtectedJoltRegister r)
    (hscratch : ¬ IsProtectedJoltRegister scratch) :
    r ≠ scratch := by
  intro hEq
  rw [hEq] at hprotected
  exact hscratch hprotected

/-- Rust's first instruction-local scratch register is not protected. -/
@[simp] theorem inlineTmp0_not_protected : ¬ IsProtectedJoltRegister inlineTmp0 :=
  not_protected_of_instructionTmp (r := inlineTmp0) (n := 0) rfl

/-- Any protected Jolt register address is distinct from Rust's first
instruction-local scratch register. -/
theorem protected_ne_inlineTmp0 {r : VReg}
    (h : IsProtectedJoltRegister r) :
    r ≠ inlineTmp0 := by
  exact protected_ne_of_not_protected h inlineTmp0_not_protected

/-- Second Rust `allocate()` scratch register, register 41. -/
def inlineTmp1 : VReg := inlineTmp 1

/-- Rust's second instruction-local scratch register is not protected. -/
@[simp] theorem inlineTmp1_not_protected : ¬ IsProtectedJoltRegister inlineTmp1 :=
  not_protected_of_instructionTmp (r := inlineTmp1) (n := 1) rfl

/-- Any protected Jolt register address is distinct from Rust's second
instruction-local scratch register. -/
theorem protected_ne_inlineTmp1 {r : VReg}
    (h : IsProtectedJoltRegister r) :
    r ≠ inlineTmp1 := by
  exact protected_ne_of_not_protected h inlineTmp1_not_protected

/-- Third Rust `allocate()` scratch register, register 42. -/
def inlineTmp2 : VReg := inlineTmp 2

/-- Rust's third instruction-local scratch register is not protected. -/
@[simp] theorem inlineTmp2_not_protected : ¬ IsProtectedJoltRegister inlineTmp2 :=
  not_protected_of_instructionTmp (r := inlineTmp2) (n := 2) rfl

/-- Any protected Jolt register address is distinct from Rust's third
instruction-local scratch register. -/
theorem protected_ne_inlineTmp2 {r : VReg}
    (h : IsProtectedJoltRegister r) :
    r ≠ inlineTmp2 := by
  exact protected_ne_of_not_protected h inlineTmp2_not_protected

/-- Fourth Rust `allocate()` scratch register, register 43. -/
def inlineTmp3 : VReg := inlineTmp 3

/-- Rust's fourth instruction-local scratch register is not protected. -/
@[simp] theorem inlineTmp3_not_protected : ¬ IsProtectedJoltRegister inlineTmp3 :=
  not_protected_of_instructionTmp (r := inlineTmp3) (n := 3) rfl

/-- Any protected Jolt register address is distinct from Rust's fourth
instruction-local scratch register. -/
theorem protected_ne_inlineTmp3 {r : VReg}
    (h : IsProtectedJoltRegister r) :
    r ≠ inlineTmp3 := by
  exact protected_ne_of_not_protected h inlineTmp3_not_protected

/-- Fifth Rust `allocate()` scratch register, register 44. -/
def inlineTmp4 : VReg := inlineTmp 4

/-- Rust's fifth instruction-local scratch register is not protected. -/
@[simp] theorem inlineTmp4_not_protected : ¬ IsProtectedJoltRegister inlineTmp4 :=
  not_protected_of_instructionTmp (r := inlineTmp4) (n := 4) rfl

/-- Any protected Jolt register address is distinct from Rust's fifth
instruction-local scratch register. -/
theorem protected_ne_inlineTmp4 {r : VReg}
    (h : IsProtectedJoltRegister r) :
    r ≠ inlineTmp4 := by
  exact protected_ne_of_not_protected h inlineTmp4_not_protected

/-- Sixth Rust `allocate()` scratch register, register 45. -/
def inlineTmp5 : VReg := inlineTmp 5

/-- Rust's sixth instruction-local scratch register is not protected. -/
@[simp] theorem inlineTmp5_not_protected : ¬ IsProtectedJoltRegister inlineTmp5 :=
  not_protected_of_instructionTmp (r := inlineTmp5) (n := 5) rfl

/-- Any protected Jolt register address is distinct from Rust's sixth
instruction-local scratch register. -/
theorem protected_ne_inlineTmp5 {r : VReg}
    (h : IsProtectedJoltRegister r) :
    r ≠ inlineTmp5 := by
  exact protected_ne_of_not_protected h inlineTmp5_not_protected

/-- Seventh Rust `allocate()` scratch register, register 46. -/
def inlineTmp6 : VReg := inlineTmp 6

/-- Rust's seventh instruction-local scratch register is not protected. -/
@[simp] theorem inlineTmp6_not_protected : ¬ IsProtectedJoltRegister inlineTmp6 :=
  not_protected_of_instructionTmp (r := inlineTmp6) (n := 6) rfl

/-- Eighth Rust `allocate()` scratch register, register 47. -/
def inlineTmp7 : VReg := inlineTmp 7

/-- Rust's eighth instruction-local scratch register is not protected. -/
@[simp] theorem inlineTmp7_not_protected : ¬ IsProtectedJoltRegister inlineTmp7 :=
  not_protected_of_instructionTmp (r := inlineTmp7) (n := 7) rfl

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
