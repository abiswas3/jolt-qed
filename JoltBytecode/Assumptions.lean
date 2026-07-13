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
-- Execution assumptions
-- ============================================================================

/-- The current generated-Sail privilege register is Machine mode.

Rust source: `tracer/src/emulator/cpu.rs:329-353`
```rust
privilege_mode: PrivilegeMode::Machine,
```

This is justified by Jolt's M-mode-only execution envelope. If a theorem is
about a path where Rust can leave Machine mode, this assumption is a bug.
-/
structure CurPrivilegeMachine (s : SailState) : Prop where
  value : s.regs.get? Register.cur_privilege =
    some (Privilege.Machine : RegisterType Register.cur_privilege)

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
state, so native control-flow proofs use the Jolt execution profile where
`update_elp_state` is a no-op.
-/
structure ZicfilpDisabled (s : SailState) : Prop where
  value : currentlyEnabled extension.Ext_Zicfilp s = .ok false s

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

/-- Generated Sail register `r` is present, with some value.

WARNING: (model state) Rust has concrete CPU fields and CSR storage; this
predicate is about the generated-Sail register map being populated at the proof
boundary.
-/
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

/-- The generated `misa` register is present and disables user mode.

WARNING: (bug) Rust initializes `misa` to `0x800000008014312f` in
`tracer/src/emulator/cpu.rs:352-353`; bit 20 is set there. This assumption is
therefore not justified by the current Rust initialization unless another
trusted setup path rewrites `misa` before the theorem.
-/
structure MisaUserDisabled (s : SailState) : Prop where
  exists_value : ∃ misa : BitVec 64,
    s.regs.get? Register.misa = some (misa : RegisterType Register.misa) ∧
    _get_Misa_U misa = 0#1

-- ============================================================================
-- System/CSR assumptions
-- ============================================================================

/-- Sail `mstatus` agrees with Jolt's persistent `mstatus` virtual register.

Rust source: `tracer/src/instruction/csrrw.rs:12`;
`tracer/src/utils/virtual_registers.rs:105`, `:114`, `:122`.
-/
structure MstatusVRegMatchesSail (js : SailJoltState) : Prop where
  value_eq :
    js.sail.regs.get? Register.mstatus =
      some (js.vregs JoltISA.mstatusVReg)

/-- Sail `mtvec` agrees with Jolt's persistent trap-handler virtual register.

Rust source: `tracer/src/instruction/csrrw.rs:7`;
`tracer/src/utils/virtual_registers.rs:80`, `:115`, `:123`.
-/
structure MtvecVRegMatchesSail (js : SailJoltState) : Prop where
  value_eq :
    js.sail.regs.get? Register.mtvec =
      some (js.vregs JoltISA.trapHandlerVReg)

/-- Sail `mscratch` agrees with Jolt's persistent `mscratch` virtual register.

Rust source: `tracer/src/instruction/csrrw.rs:8`;
`tracer/src/utils/virtual_registers.rs:85`, `:116`, `:124`.
-/
structure MscratchVRegMatchesSail (js : SailJoltState) : Prop where
  value_eq :
    js.sail.regs.get? Register.mscratch =
      some (js.vregs JoltISA.mscratchVReg)

/-- Sail `mepc` agrees with Jolt's persistent `mepc` virtual register.

Rust source: `tracer/src/instruction/csrrw.rs:9`;
`tracer/src/utils/virtual_registers.rs:90`, `:117`, `:125`.
-/
structure MepcVRegMatchesSail (js : SailJoltState) : Prop where
  value_eq :
    js.sail.regs.get? Register.mepc =
      some (js.vregs JoltISA.mepcVReg)

/-- Sail `mcause` agrees with Jolt's persistent `mcause` virtual register.

Rust source: `tracer/src/instruction/csrrw.rs:10`;
`tracer/src/utils/virtual_registers.rs:95`, `:118`, `:126`.
-/
structure McauseVRegMatchesSail (js : SailJoltState) : Prop where
  value_eq :
    js.sail.regs.get? Register.mcause =
      some (js.vregs JoltISA.mcauseVReg)

/-- Sail `mtval` agrees with Jolt's persistent `mtval` virtual register.

Rust source: `tracer/src/instruction/csrrw.rs:11`;
`tracer/src/utils/virtual_registers.rs:100`, `:119`, `:127`.
-/
structure MtvalVRegMatchesSail (js : SailJoltState) : Prop where
  value_eq :
    js.sail.regs.get? Register.mtval =
      some (js.vregs JoltISA.mtvalVReg)

/-- Sail's machine-trap `mstatus` update maps `current` to `expected`.

Rust source: `crates/jolt-program/src/expand/control_flow/ecall.rs:43-51`.

Jolt ECALL writes `mstatus = 3 << 11`, i.e. `MPP=M-mode` with interrupt-enable
bits cleared. This assumption is the proof boundary saying Sail's trap-entry
update computes that same value for the current `mstatus`.
-/
structure MachineTrapMstatusMatches
    (current expected : BitVec 64) : Prop where
  value_eq :
    Sail.BitVec.updateSubrange
      (Sail.BitVec.updateSubrange
        (Sail.BitVec.updateSubrange current 7 7 (_get_Mstatus_MIE current))
        3 3 0#1)
      12 11 (privLevel_to_bits Privilege.Machine) = expected

/-- Sail's trap-vector helper selects the same concrete control-flow target.

Rust source: `crates/jolt-program/src/expand/control_flow/ecall.rs:54-62`.

Jolt ECALL jumps with `JALR` through the reserved `mtvec` virtual register.
This assumption states that Sail's `tvec_addr` calculation selects that same
target for the ECALL cause. If `mtvec` mode semantics make Sail choose a
different target, that is Rust/Lean drift.
-/
structure TrapVectorTargetMatches
    (mtvec cause target : BitVec 64) : Prop where
  value_eq : tvec_addr mtvec cause = some target

/-- The target satisfies Sail/Jolt's compressed-disabled fetch-alignment check.

WARNING: (missing) This is currently a generated-Sail fetch side condition. I
have not found a Rust source line that states the same `target[1] = 0` check for
these system-control transfers.
-/
structure FetchTargetAligned (target : BitVec 64) : Prop where
  bit1_zero : BitVec.access target 1 = 0#1

/-- MRET's `MIE := MPIE` write is idempotent for this `mstatus` value.

Rust source: `crates/jolt-program/src/expand/control_flow/mret.rs:3-23`.

Jolt lowers MRET to a `JALR` through `mepc`; it does not implement Sail's full
architectural `mstatus` rewrite in the inline sequence. The ZeroOS envelope
therefore must make this Sail field update state-neutral.
-/
structure MstatusMieMatchesMpie (mstatus : BitVec 64) : Prop where
  value_eq : _get_Mstatus_MIE mstatus = _get_Mstatus_MPIE mstatus

/-- MRET's `MPIE := 1` write is idempotent for this `mstatus` value.

Rust source: `crates/jolt-program/src/expand/control_flow/mret.rs:3-23`.

Jolt's MRET expansion is only a jump through `mepc`; this assumption states the
corresponding Sail `mstatus.MPIE := 1` step is already a no-op.
-/
structure MstatusMpieOne (mstatus : BitVec 64) : Prop where
  value_eq : _get_Mstatus_MPIE mstatus = 1#1

/-- MRET's `MPP := least_privilege` write is idempotent in the Machine-only
ZeroOS envelope.

Rust source: `crates/jolt-program/src/expand/control_flow/mret.rs:3-23`.

Jolt's MRET expansion does not change privilege. In the current proof envelope,
Sail's MRET privilege restoration must therefore decode and preserve Machine
mode.
-/
structure MstatusMppMachine (mstatus : BitVec 64) : Prop where
  value_eq : _get_Mstatus_MPP mstatus = privLevel_to_bits Privilege.Machine

/-- Sail's generated Zicfilp MRET hook is idempotent for this `mstatus` value.

WARNING: (missing) This is a generated-Sail Zicfilp side condition. I have not
found a Rust/tracer source line that models `mstatus.MPELP` for MRET.
-/
structure MstatusMpelpZero (mstatus : BitVec 64) : Prop where
  value_eq : _get_Mstatus_MPELP mstatus = 0#1

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

end Assumptions

export Assumptions (
  CurPrivilegeMachine
  MstatusMprvZero
  ZicfilpDisabled
  XRegReadable
  SailRegReadable
  MisaUserDisabled
  MachineTrapMstatusMatches
  TrapVectorTargetMatches
  FetchTargetAligned
  MstatusMieMatchesMpie
  MstatusMpieOne
  MstatusMppMachine
  MstatusMpelpZero
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
