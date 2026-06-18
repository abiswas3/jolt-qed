# Jolt Proof Registers vs Sail Register Model Mismatch

Status: identified model mismatch, not currently classified as a Jolt bug.

## Summary

The generated Sail model in Lean represents the full architectural/simulator state
inside its generated `Register` namespace. That includes integer registers, CSRs,
PC/nextPC, privilege state, RVFI fields, vector/floating state, and other simulator
or device state.

Rust Jolt is organized differently. The emulator has hardware-like state such as
`pc`, `privilege_mode`, an integer/virtual register array, a raw CSR array, MMU state,
and reservation state. Separately, the Jolt proof-facing register file is made of the
32 RISC-V integer registers plus Jolt virtual registers. Only a small CSR subset is
materialized as persistent Jolt virtual registers.

So the mismatch is not "Rust has no state for these things." The mismatch is that
Sail models everything as generated Lean registers, while Jolt's proof/register-file
interface only exposes a restricted subset as Jolt virtual registers. Equivalence
proofs must bridge those different representations.

## Rust Evidence

`/Users/ari.biswas/Work-with-A16z/jolt/common/src/constants.rs:1`

```rust
pub const XLEN: usize = 64;
pub const RISCV_REGISTER_COUNT: u8 = 32;
pub const VIRTUAL_REGISTER_COUNT: u8 = 96; //  see Section 6.1 of Jolt paper
pub const VIRTUAL_INSTRUCTION_RESERVED_REGISTER_COUNT: u8 = 8; // Reserved virtual registers for virtual instructions
pub const REGISTER_COUNT: u8 = RISCV_REGISTER_COUNT + VIRTUAL_REGISTER_COUNT; // must be a power of 2
```

`/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/utils/virtual_registers.rs:13`

```rust
/// CSR addresses for M-mode CSRs supported by the virtual register system.
/// These are the standard RISC-V CSR addresses.
pub const CSR_MSTATUS: u16 = 0x300; // Machine Status
pub const CSR_MTVEC: u16 = 0x305; // Machine Trap-Vector Base Address
pub const CSR_MSCRATCH: u16 = 0x340; // Machine Scratch Register
pub const CSR_MEPC: u16 = 0x341; // Machine Exception Program Counter
pub const CSR_MCAUSE: u16 = 0x342; // Machine Trap Cause
pub const CSR_MTVAL: u16 = 0x343; // Machine Trap Value
```

`/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/utils/virtual_registers.rs:22`

```rust
/// Layout of virtual registers:
/// - Registers 32-39: Reserved registers (persistent, never allocated)
///   - 32: Reservation address for LR.W/SC.W
///   - 33: Reservation address for LR.D/SC.D
///   - 34: mtvec (trap handler address)
///   - 35: mscratch (trap scratch register)
///   - 36: mepc (exception PC)
///   - 37: mcause (trap cause)
///   - 38: mtval (trap value)
///   - 39: mstatus (machine status)
```

`/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/utils/virtual_registers.rs:110`

```rust
/// Map a CSR address to its corresponding virtual register number.
/// Returns Some(register) if the CSR is supported, None otherwise.
///
/// Supported CSRs:
/// - mstatus (0x300) → vr39
/// - mtvec (0x305) → vr34
/// - mscratch (0x340) → vr35
/// - mepc (0x341) → vr36
/// - mcause (0x342) → vr37
/// - mtval (0x343) → vr38
pub fn csr_to_virtual_register(&self, csr_addr: u16) -> Option<u8> {
    match csr_addr {
        CSR_MSTATUS => Some(self.mstatus_register()),
        CSR_MTVEC => Some(self.trap_handler_register()),
        CSR_MSCRATCH => Some(self.mscratch_register()),
        CSR_MEPC => Some(self.mepc_register()),
        CSR_MCAUSE => Some(self.mcause_register()),
        CSR_MTVAL => Some(self.mtval_register()),
        _ => None,
    }
}
```

The static expansion path has the same CSR subset.

`/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-program/src/expand/allocator.rs:25`

```rust
pub const CSR_MSTATUS: u16 = 0x300;
pub const CSR_MTVEC: u16 = 0x305;
pub const CSR_MSCRATCH: u16 = 0x340;
pub const CSR_MEPC: u16 = 0x341;
pub const CSR_MCAUSE: u16 = 0x342;
pub const CSR_MTVAL: u16 = 0x343;
```

`/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-program/src/expand/allocator.rs:60`

```rust
pub(super) fn virtual_register_for_csr(csr_addr: u16) -> Option<u8> {
    match csr_addr {
        CSR_MSTATUS => Some(mstatus_register()),
        CSR_MTVEC => Some(trap_handler_register()),
        CSR_MSCRATCH => Some(mscratch_register()),
        CSR_MEPC => Some(mepc_register()),
        CSR_MCAUSE => Some(mcause_register()),
        CSR_MTVAL => Some(mtval_register()),
        _ => None,
    }
}
```

Unsupported CSR instructions are rejected before reaching the inline sequence path.

`/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/instruction/mod.rs:1166`

```rust
// CSRRW: funct3=1. Reject unsupported CSRs at decode time
// so the trace path never reaches an unmodelled CSR — the
// inline_sequence path would otherwise panic the prover.
(1, _, _) => {
    let csr_addr = ((instr >> 20) & 0xFFF) as u16;
    if !is_supported_csr(csr_addr) {
        return Err("Unsupported CSR in CSRRW");
    }
    Ok(CSRRW::new(instr, address, true, compressed).into())
}
```

The emulator does have hardware-like state. This is important: the issue is not that
Rust lacks a PC, CSR state, or privilege state. The issue is that those pieces are
not all represented as persistent Jolt virtual registers.

`/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/emulator/cpu.rs:159`

```rust
/// Emulates a RISC-V CPU core
#[derive(Clone, Debug)]
pub struct Cpu {
    clock: u64,

    pub(crate) privilege_mode: PrivilegeMode,
    wfi: bool,
    pub x: [i64; REGISTER_COUNT as usize],
    #[allow(dead_code)]
    f: [f64; 32],
    pub(crate) pc: u64,
    csr: [u64; CSR_CAPACITY],
```

The emulator advances `pc` as part of instruction execution. Sail has generated
registers named `PC` and `nextPC`; Rust represents this operationally using the
`pc` field rather than as two generated-register keys.

`/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/emulator/cpu.rs:459`

```rust
let original_word = self.fetch()?;
let instruction_address = normalize_u64(self.pc);
let is_compressed = (original_word & 0x3) != 0x3;
let word = match is_compressed {
    false => {
        self.pc = self.pc.wrapping_add(4); // 32-bit length non-compressed instruction
        original_word
    }
    true => {
        self.pc = self.pc.wrapping_add(2); // 16-bit length compressed instruction
        uncompress_instruction(original_word & 0xffff)
    }
};
```

## Sail / Lean Evidence

The generated Sail register namespace is the full Lean-side state model. It contains
many more entries than Jolt's proof-facing CSR virtual-register subset.

`/Users/ari.biswas/Lean/lz-qed/LeanRV64D/Defs.lean:1526`

```lean
inductive Register : Type where
  | hart_state
  | mhpmcounter
  | mhpmevent
  | ssp
  | srmcfg
  | satp
  | tlb
  | pma_regions
```

`/Users/ari.biswas/Lean/lz-qed/LeanRV64D/Defs.lean:1674`

```lean
  | nextPC
  | PC
  | vstart
  | vl
  | vtype
  | menvcfg
  | mseccfg
  | senvcfg
  | sstateen3
  | sstateen2
  | sstateen1
  | sstateen0
  | mstateen3
  | mstateen2
  | mstateen1
  | mstateen0
  | hstateen3
  | hstateen2
  | hstateen1
  | hstateen0
  | mstatus
  | misa
  | cur_privilege
```

The Lean Jolt mirror explicitly maps only the same six CSR-backed virtual registers
to generated Sail registers.

`/Users/ari.biswas/Lean/lz-qed/JoltBytecode/JoltISA/VirtualRegisters.lean:250`

```lean
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
```

`/Users/ari.biswas/Lean/lz-qed/JoltBytecode/InstructionEquivalence/System/Common.lean:64`

```lean
/-- Overlay Jolt's persistent virtual CSR registers onto the generated Sail CSR
register keys.

This is only a proof projection: the Rust-faithful Jolt programs still write
Jolt virtual registers, and the Sail specification still reads/writes generated
Sail registers. -/
def systemProject (js : SailJoltState) : SailState :=
  { js.sail with
    regs :=
      ((((((js.sail.regs
        |>.insert Register.mtvec (js.vregs JoltISA.trapHandlerVReg))
        |>.insert Register.mscratch (js.vregs JoltISA.mscratchVReg))
        |>.insert Register.mepc (js.vregs JoltISA.mepcVReg))
        |>.insert Register.mcause (js.vregs JoltISA.mcauseVReg))
        |>.insert Register.mtval (js.vregs JoltISA.mtvalVReg))
        |>.insert Register.mstatus (js.vregs JoltISA.mstatusVReg)) }
```

## Interpretation

This should be tracked as a model-boundary mismatch, not as an immediate Rust bug.
Rust Jolt has an emulator state for hardware execution, but it deliberately exposes
only a restricted CSR/register subset through the proof-facing virtual register model.
Sail exposes the full architectural/simulator state as generated Lean registers.

For equivalence work, this means:

- proofs should not assume every Sail register has a corresponding Jolt virtual register;
- unsupported CSR instructions should remain outside the supported instruction set unless
  Jolt adds proof-facing virtual-register semantics for them;
- assumptions involving Sail registers such as `cur_privilege`, `misa`, `PC`, or
  `nextPC` need to be classified by representation: some correspond to Rust emulator
  fields or raw CSR state, while others may be outside the current proof-facing model;
- projection lemmas should state exactly which Sail registers are overlaid from Jolt
  virtual registers and which remain unchanged from the ambient Sail state.

## Classification

Identified abstraction mismatch:

Jolt Rust has hardware-like emulator state, but implements only a restricted
proof-facing virtual-register model. Generated Sail models the full RISC-V
architectural/simulator state as Lean registers. The current bridge must make that
representation boundary explicit.
