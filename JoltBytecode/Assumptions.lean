import JoltBytecode.JoltISA.VirtualRegisters
-- NOTE: Some of the assumptions (the OS ones are stale and need review)
/-!
# Jolt proof assumptions

This file is the top-level index of primitive assumptions used by the
instruction-equivalence proofs. It is intentionally assumption-only:

* every exported declaration below is a primitive proof assumption predicate;
* no theorem declarations or derived facts live here;
* no dword/window/range helper aliases live here;
* composed proof-facing bundles live in family `Bundles` modules;
* exact low-level memory access facts live in
  `InstructionEquivalence.Memory.Basic`;
* projections and derived consequences live in `Derived` or family utility
  files.
-/

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace Assumptions

-- ============================================================================
-- Register assumptions
-- ============================================================================

/-- Integer register `r` is readable, with some value.

Rust source: `tracer/src/emulator/cpu.rs:166`,
`tracer/src/emulator/cpu.rs:375-394`.

Rust stores integer registers in `Cpu.x`; reads are total for decoded register
indices and writes keep `x0` hardwired to zero. The Lean assumption is the Sail
finite-map/readability side of the same pre-state.
-/
structure XRegReadable (r : regidx) (s : SailState) : Prop where
  exists_value : ∃ value : BitVec 64, rX_bits r s = .ok value s

structure SailRegReadable (r : Register) (s : SailState) : Prop where
  exists_value : ∃ value : RegisterType r, s.regs.get? r = some value

/-- Assumptions for an instruction that reads one architectural source register. -/
structure UnarySourceReadAssumptions (rs1 : regidx) (s : SailState) where
  rs1_val : BitVec 64
  rs1_read : rX_bits rs1 s = .ok rs1_val s

/-- Assumptions for an instruction that reads two architectural source registers. -/
structure BinarySourceReadAssumptions
    (rs2 rs1 : regidx) (s : SailState) where
  rs1_val : BitVec 64
  rs1_read : rX_bits rs1 s = .ok rs1_val s
  rs2_val : BitVec 64
  rs2_read : rX_bits rs2 s = .ok rs2_val s

-- ============================================================================
-- Memory assumptions
-- ============================================================================

/-- The 8-byte dword beginning at `addr` is present in Sail's finite memory map.

Rust source: `tracer/src/emulator/memory.rs:38-63`,
`tracer/src/emulator/memory.rs:136-196`.

Rust memory is doubleword-backed and treats missing doublewords as
zero-initialized. Lean's direct byte helpers use finite-map lookup; this
assumption states that the single enclosing dword Jolt reads is populated.
-/
structure DwordPresent (addr : BitVec 64) (s : SailState) : Prop where
  bytes :
    ∃ bytes : Fin 8 → BitVec 8,
      ∀ k : Fin 8, s.mem.get? (addr.toNat + k.val) = some (bytes k)

/-- Machine-mode PMP accepts a data load from `addr` for `width` bytes.

Rust source: `tracer/src/emulator/mmu.rs:13-18`.

Jolt's Rust MMU explicitly says memory protection is not implemented. This
predicate constrains generated Sail to the corresponding no-PMP-fault path.
-/
abbrev LoadPmpOk (addr : BitVec 64) (width : Nat) (s : SailState) : Prop :=
  phys_access_check (Load Data) Privilege.Machine
    (physaddr.Physaddr addr) width false s = .ok none s

/-- Machine-mode PMP accepts every explicit sub-load inside a memory window. -/
structure LoadPmpOkWindow
    (base : BitVec 64) (width : Nat) (s : SailState) : Prop where
  ok :
    ∀ offset accessWidth : Nat, offset + accessWidth ≤ width →
      LoadPmpOk (base + BitVec.ofNat 64 offset) accessWidth s

/-- Machine-mode PMP accepts a data store to `addr` for `width` bytes.

Rust source: `tracer/src/emulator/mmu.rs:13-18`.

Jolt's Rust MMU explicitly says memory protection is not implemented. This
predicate constrains generated Sail to the corresponding no-PMP-fault path.
-/
abbrev StorePmpOk (addr : BitVec 64) (width : Nat) (s : SailState) : Prop :=
  phys_access_check (Store Data) Privilege.Machine
    (physaddr.Physaddr addr) width false s = .ok none s

/-- Machine-mode PMP accepts every explicit sub-store inside a memory window. -/
structure StorePmpOkWindow
    (base : BitVec 64) (width : Nat) (s : SailState) : Prop where
  ok :
    ∀ offset accessWidth : Nat, offset + accessWidth ≤ width →
      StorePmpOk (base + BitVec.ofNat 64 offset) accessWidth s

/-- Machine-mode PMP accepts an AMO at `addr` for `width` bytes.

Rust source: `tracer/src/emulator/mmu.rs:13-18`.

Jolt's Rust MMU explicitly says memory protection is not implemented. This
predicate constrains generated Sail to the corresponding no-PMP-fault path.
-/
abbrev AtomicPmpOk
    (op : amoop) (addr : BitVec 64) (width : Nat) (s : SailState) : Prop :=
  phys_access_check (Atomic (op, Data, Data)) Privilege.Machine
    (physaddr.Physaddr addr) width true s = .ok none s

/-- Machine-mode PMP accepts every explicit sub-AMO inside a memory window. -/
structure AtomicPmpOkWindow
    (op : amoop) (base : BitVec 64) (width : Nat) (s : SailState) : Prop where
  ok :
    ∀ offset accessWidth : Nat, offset + accessWidth ≤ width →
      AtomicPmpOk op (base + BitVec.ofNat 64 offset) accessWidth s

/-- The physical range is not readable MMIO.

Rust source: `tracer/src/emulator/mmu.rs:139-213`.

Rust has a device/I/O address branch and an ordinary RAM branch. The flat-memory
proofs using this predicate are intentionally about the ordinary RAM path, not
device I/O.
-/
abbrev NotReadableMmio (addr : BitVec 64) (width : Nat) (s : SailState) : Prop :=
  within_mmio_readable (physaddr.Physaddr addr) width s = .ok false s

/-- Every explicit sub-load inside a memory window avoids readable MMIO. -/
structure NotReadableMmioWindow
    (base : BitVec 64) (width : Nat) (s : SailState) : Prop where
  ok :
    ∀ offset accessWidth : Nat, offset + accessWidth ≤ width →
      NotReadableMmio (base + BitVec.ofNat 64 offset) accessWidth s

/-- The physical range is not writable MMIO.

Rust source: `tracer/src/emulator/mmu.rs:139-213`.

Rust has a device/I/O address branch and an ordinary RAM branch. The flat-memory
proofs using this predicate are intentionally about the ordinary RAM path, not
device I/O.
-/
abbrev NotWritableMmio (addr : BitVec 64) (width : Nat) (s : SailState) : Prop :=
  within_mmio_writable (physaddr.Physaddr addr) width s = .ok false s

/-- Every explicit sub-store inside a memory window avoids writable MMIO. -/
structure NotWritableMmioWindow
    (base : BitVec 64) (width : Nat) (s : SailState) : Prop where
  ok :
    ∀ offset accessWidth : Nat, offset + accessWidth ≤ width →
      NotWritableMmio (base + BitVec.ofNat 64 offset) accessWidth s

-- ============================================================================
-- System/CSR register assumptions
-- ============================================================================

/-- The current generated-Sail privilege register is Machine mode.

Rust source: `tracer/src/emulator/cpu.rs:329-353`
```rust
privilege_mode: PrivilegeMode::Machine,
```
-/
structure CurPrivilegeMachine (s : SailState) : Prop where
  value : s.regs.get? Register.cur_privilege =
    some (Privilege.Machine : RegisterType Register.cur_privilege)

/-- The generated `misa` CSR is present and has the U extension bit set.

Rust source:
`/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/emulator/cpu.rs:399`.
Generated Sail source: `LeanRV64D/Types.lean:381-382`.

Rust initializes `misa` to `0x800000008014312f`; generated Sail's
`_get_Misa_U` reads bit 20, which is set in that value.
-/
structure MisaUserEnabled (s : SailState) : Prop where
  exists_value : ∃ misa : BitVec 64,
    s.regs.get? Register.misa = some (misa : RegisterType Register.misa) ∧
    _get_Misa_U misa = 1#1

/-- The Sail `mstatus` register is readable and has MPRV=0.

Rust source: `tracer/src/emulator/mmu.rs:870-898`.

Rust's address translation returns the address unchanged in Machine mode when
`mstatus.MPRV = 0`. The memory-family proofs assume that envelope so Sail does
not take an MPRV remapping path that Jolt's bytecode proof is not modeling.
-/
structure MstatusMprvZero (s : SailState) : Prop where
  value : ∃ mval : RegisterType Register.mstatus,
    s.regs.get? Register.mstatus = some mval ∧
    _get_Mstatus_MPRV mval = 0#1

/-- The generated Sail Zicfilp landing-pad extension is disabled.

Jolt does not model the generated Sail `elp` register or Zicfilp landing-pad
state.
-/
structure ZicfilpDisabled (s : SailState) : Prop where
  value : currentlyEnabled extension.Ext_Zicfilp s = .ok false s

-- vreg == sail.csr begins  here 

/-- Sail `mstatus` agrees with Jolt's persistent `mstatus` virtual register. -/
structure MstatusVRegMatchesSail (js : SailJoltState) : Prop where
  value_eq :
    js.sail.regs.get? Register.mstatus =
      some (js.vregs JoltISA.mstatusVReg)

/-- Sail `mtvec` agrees with Jolt's persistent trap-handler virtual register. -/
structure MtvecVRegMatchesSail (js : SailJoltState) : Prop where
  value_eq :
    js.sail.regs.get? Register.mtvec =
      some (js.vregs JoltISA.trapHandlerVReg)

/-- A value written to `mtvec` uses Direct mode, so Sail's `legalize_tvec`
accepts it unchanged.

Jolt source:
`/Users/ari.biswas/Work-with-A16z/jolt/jolt-sdk/src/runtime/boot.rs:21-28`.
ZeroOS source:
`https://github.com/LayerZero-Labs/ZeroOS/blob/main/platforms/spike-platform/src/boot.rs#L13-L19`;
`https://github.com/LayerZero-Labs/ZeroOS/blob/main/crates/zeroos-arch-riscv/src/trap.rs#L308-L316`.
Generated Sail source:
`LeanRV64D/SysRegs.lean:1180-1181`, `LeanRV64D/SysRegs.lean:1210-1223`;
`LeanRV64D/Types.lean:11089-11093`.

The ZeroOS/Jolt boot path writes `_trap_handler` to `mtvec` with `csrw mtvec,
t0`; ZeroOS defines `_trap_handler` under `.align 2`, which gives 4-byte
alignment, so the lower two bits are `00`. In generated Sail, those two bits are
the `mtvec.MODE` field; `00` is `TV_Direct`, and `legalize_tvec` returns Direct
or Vector values unchanged. For CSRRW, this has to be an assumption on the
source value being written, not on the old stored `mtvec`, because Sail
legalizes the new `rs1` value.
-/
structure MtvecWriteDirectMode (value : BitVec 64) : Prop where
  mode_eq : _get_Mtvec_Mode value = 0b00#2

/-- Sail `mscratch` agrees with Jolt's persistent `mscratch` virtual register. -/
structure MscratchVRegMatchesSail (js : SailJoltState) : Prop where
  value_eq :
    js.sail.regs.get? Register.mscratch =
      some (js.vregs JoltISA.mscratchVReg)

/-- Sail `mepc` agrees with Jolt's persistent `mepc` virtual register. -/
structure MepcVRegMatchesSail (js : SailJoltState) : Prop where
  value_eq :
    js.sail.regs.get? Register.mepc =
      some (js.vregs JoltISA.mepcVReg)

/-- A stored `mepc` value is already aligned for Sail's read-side `align_pc`.

ZeroOS/Jolt source:
`https://github.com/LayerZero-Labs/ZeroOS/blob/main/crates/zeroos-build/src/spec/profiles.rs#L27-L30`;
`https://github.com/LayerZero-Research/jolt/blob/main/book/src/how/appendix/risc-v.md#L5-L8`;
`https://github.com/LayerZero-Labs/ZeroOS/blob/main/crates/zeroos-arch-riscv/src/trap.rs#L229-L259`;
`https://github.com/LayerZero-Research/jolt/blob/main/jolt-sdk/src/runtime/trap.rs#L18-L34`;
`https://github.com/LayerZero-Research/jolt/blob/main/jolt-sdk/src/runtime/trap.rs#L47-L55`.
Generated Sail source:
`LeanRV64D/SysExceptions.lean:224-231`;
`LeanRV64D/SysRegs.lean:1266-1269`.

Current ZeroOS/Jolt targets are compressed-capable (`+c` / RV64IMAC), so the
relevant invariant is `mepc[0] = 0`. This predicate records the generated-Sail
read-side consequence: `align_pc` leaves the stored `mepc` value unchanged.
-/
structure MepcReadAligned (value : BitVec 64) (s : SailState) : Prop where
  value_eq : align_pc value s = .ok value s

/-- A value written to `mepc` is already legal, so Sail's `legalize_xepc`
accepts it unchanged.

This is the write-side counterpart of `MepcReadAligned`: CSRRW writes the new
`rs1` value, so the assumption must be about that source value rather than only
the old stored `mepc`.
-/
structure MepcWriteLegalized (value : BitVec 64) : Prop where
  value_eq : legalize_xepc value = value

/-- Sail `mcause` agrees with Jolt's persistent `mcause` virtual register. -/
structure McauseVRegMatchesSail (js : SailJoltState) : Prop where
  value_eq :
    js.sail.regs.get? Register.mcause =
      some (js.vregs JoltISA.mcauseVReg)

/-- Sail `mtval` agrees with Jolt's persistent `mtval` virtual register. -/
structure MtvalVRegMatchesSail (js : SailJoltState) : Prop where
  value_eq :
    js.sail.regs.get? Register.mtval =
      some (js.vregs JoltISA.mtvalVReg)

-- vreg == sail.csr ends here 

/- /-- Sail's machine-trap update maps Jolt's fixed `mstatus` virtual register to
the fixed ZeroOS machine-trap `mstatus` value.

WARNING: (No rust) I found no Rust line proving the generated-Sail trap-entry
update from the current projected `mstatus` computes this fixed value.
-/
structure MachineTrapMstatusMatches (js : SailJoltState) : Prop where
  value_eq :
    Sail.BitVec.updateSubrange
      (Sail.BitVec.updateSubrange
        (Sail.BitVec.updateSubrange (js.vregs JoltISA.mstatusVReg) 7 7
          (_get_Mstatus_MIE (js.vregs JoltISA.mstatusVReg)))
        3 3 0#1)
      12 11 (privLevel_to_bits Privilege.Machine) = BitVec.ofNat 64 0x1800


/-- Sail's trap-vector helper selects the ECALL target from Jolt's fixed
trap-handler virtual register.

WARNING: (No rust) I found no Rust line proving generated-Sail `tvec_addr`
selects this target for the current `mtvec` mode and ECALL cause.
-/
structure TrapVectorTargetMatches (js : SailJoltState) : Prop where
  value_eq :
    tvec_addr (js.vregs JoltISA.trapHandlerVReg)
        (zero_extend (m := 64)
          (exceptionType_bits_forwards (ExceptionType.E_M_EnvCall ()))) =
      some (BitVec.update (js.vregs JoltISA.trapHandlerVReg) 0 0#1)

/-- The ECALL trap target from Jolt's fixed trap-handler virtual register passes
the compressed-disabled fetch-alignment check.

WARNING: (No rust) I found no Rust line enforcing target bit 1 is zero.
-/
structure EcallTrapTargetAligned (js : SailJoltState) : Prop where
  bit1_zero :
    BitVec.access (BitVec.update (js.vregs JoltISA.trapHandlerVReg) 0 0#1) 1 =
      0#1

/-- The MRET return target from Jolt's fixed `mepc` virtual register passes the
compressed-disabled fetch-alignment check.

WARNING: (No rust) I found no Rust line enforcing target bit 1 is zero.
-/
structure MretReturnTargetAligned (js : SailJoltState) : Prop where
  bit1_zero :
    BitVec.access (BitVec.update (js.vregs JoltISA.mepcVReg) 0 0#1) 1 = 0#1

/-- Jolt's fixed `mstatus` virtual register has `MIE = MPIE`.

WARNING: (No rust) I found no Rust line asserting this pre-MRET `MIE = MPIE`
field condition.
-/
structure MstatusMieMatchesMpie (js : SailJoltState) : Prop where
  value_eq :
    _get_Mstatus_MIE (js.vregs JoltISA.mstatusVReg) =
      _get_Mstatus_MPIE (js.vregs JoltISA.mstatusVReg)

/-- Jolt's fixed `mstatus` virtual register has `MPIE = 1`.

field condition.
-/
structure MstatusMpieOne (js : SailJoltState) : Prop where
  value_eq :
    _get_Mstatus_MPIE (js.vregs JoltISA.mstatusVReg) = 1#1
-/

/-- Jolt's fixed `mstatus` virtual register has `MPP = Machine`.

Rust source:
`/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/instruction/mret.rs:7-18`;
`/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/instruction/ecall.rs:8-16`;
`/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-program/src/expand/control_flow/ecall.rs:43-51`.
-/
structure MstatusMppMachine (js : SailJoltState) : Prop where
  value_eq :
    _get_Mstatus_MPP (js.vregs JoltISA.mstatusVReg) =
      privLevel_to_bits Privilege.Machine

end Assumptions

export Assumptions (
  CurPrivilegeMachine
  MstatusMprvZero
  ZicfilpDisabled
  XRegReadable
  SailRegReadable
  MisaUserEnabled
  MtvecWriteDirectMode
  MstatusMppMachine
  DwordPresent
  LoadPmpOk
  LoadPmpOkWindow
  StorePmpOk
  StorePmpOkWindow
  AtomicPmpOk
  AtomicPmpOkWindow
  NotReadableMmio
  NotReadableMmioWindow
  NotWritableMmio
  NotWritableMmioWindow
)

end
