# Bug Report: CSRRW System CSR Expansion Bypasses Architectural Legalization

## Instruction
`CSRRW csr, rs1, rd` / `CSRW csr, rs1` for Jolt's supported machine CSRs.

The affected CSR cases are:

- `mstatus`, CSR address `0x300`
- `mtvec`, CSR address `0x305`
- `mepc`, CSR address `0x341`

`mepc` has both a read-side and write-side mismatch. `mstatus` and `mtvec` have
write-side mismatches.

## Jolt Expansion

Jolt lowers `CSRRW` to plain `ADDI` copies through a reserved virtual register for
the CSR.

`/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-program/src/expand/control_flow/csrrw.rs:10`

```rust
pub(in crate::expand) fn expand_csrrw(
    instruction: &SourceInstructionRow,
) -> Result<ExpandedInstructionSequence, ExpansionError> {
    let csr = csr_address(instruction);
    let virtual_reg = virtual_register_for_csr(csr).ok_or(ExpansionError::UnsupportedCsr(csr))?;
    let mut asm = ExpansionBuilder::new(*instruction);

    if rd(instruction)? == 0 {
        // `csrw csr, rs1`: write the CSR and discard the old value.
        asm.emit_i(
            JoltInstructionKind::ADDI,
            reg(virtual_reg),
            reg(rs1(instruction)?),
            0,
        );
        return asm.finalize();
    } else if rd(instruction)? == rs1(instruction)? {
        // Preserve rs1 before rd is overwritten with the old CSR value.
        let temp = asm.allocate()?;
        asm.emit_i(
            JoltInstructionKind::ADDI,
            temp.operand(),
            reg(rs1(instruction)?),
            0,
        );
        asm.emit_i(
            JoltInstructionKind::ADDI,
            reg(rd(instruction)?),
            reg(virtual_reg),
            0,
        );
        asm.emit_i(
            JoltInstructionKind::ADDI,
            reg(virtual_reg),
            temp.operand(),
            0,
        );
        asm.release(temp);
        return asm.finalize();
    }

    // General case: copy old CSR to rd, then copy rs1 into the CSR.
    asm.emit_i(
        JoltInstructionKind::ADDI,
        reg(rd(instruction)?),
        reg(virtual_reg),
        0,
    );
    asm.emit_i(
        JoltInstructionKind::ADDI,
        reg(virtual_reg),
        reg(rs1(instruction)?),
        0,
    );

    asm.finalize()
}
```

`/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-program/src/expand/allocator.rs:16`

```rust
const RESERVATION_W_REGISTER: u8 = RISCV_REGISTER_BASE;
const RESERVATION_D_REGISTER: u8 = RISCV_REGISTER_BASE + 1;
const TRAP_HANDLER_REGISTER: u8 = RISCV_REGISTER_BASE + 2;
const MSCRATCH_REGISTER: u8 = RISCV_REGISTER_BASE + 3;
const MEPC_REGISTER: u8 = RISCV_REGISTER_BASE + 4;
const MCAUSE_REGISTER: u8 = RISCV_REGISTER_BASE + 5;
const MTVAL_REGISTER: u8 = RISCV_REGISTER_BASE + 6;
const MSTATUS_REGISTER: u8 = RISCV_REGISTER_BASE + 7;

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

For `mepc`, `virtual_register_for_csr(0x341)` returns Jolt's reserved `mepc`
virtual register. There is no alignment, masking, or legalization step in the
`CSRRW` expansion.

The local Lean model of the Jolt expansion mirrors that Rust expansion.

`JoltBytecode/JoltISA/Expansions/System.lean:44`

```lean
inductive SystemCSR where
  | mstatus
  | mtvec
  | mscratch
  | mepc
  | mcause
  | mtval
  deriving Repr, DecidableEq

namespace SystemCSR

/-- Rust CSR address used by the decoded SYSTEM instruction. -/
def address : SystemCSR → BitVec 12
  | .mstatus => 0x300
  | .mtvec => 0x305
  | .mscratch => 0x340
  | .mepc => 0x341
  | .mcause => 0x342
  | .mtval => 0x343

/-- Reserved virtual register used as the proof/trace source of truth for a CSR. -/
def vreg : SystemCSR → VReg
  | .mstatus => mstatusVReg
  | .mtvec => trapHandlerVReg
  | .mscratch => mscratchVReg
  | .mepc => mepcVReg
  | .mcause => mcauseVReg
  | .mtval => mtvalVReg
```

`JoltBytecode/JoltISA/Expansions/System.lean:160`

```lean
def csrrwProgram (csr : SystemCSR) (rs1 rd : regidx) : Program :=
  let vr := SystemCSR.vreg csr
  if isX0 rd then
    .instr (.ADDI (.vreg vr) (.xreg rs1) (0 : BitVec 12)) <|
    .done RETIRE_SUCCESS
  else if sameXReg rd rs1 then
    .instr (.ADDI (.vreg systemScratchVReg) (.xreg rs1) (0 : BitVec 12)) <|
    .instr (.ADDI (.xreg rd) (.vreg vr) (0 : BitVec 12)) <|
    .instr (.ADDI (.vreg vr) (.vreg systemScratchVReg) (0 : BitVec 12)) <|
    .done RETIRE_SUCCESS
  else
    .instr (.ADDI (.xreg rd) (.vreg vr) (0 : BitVec 12)) <|
    .instr (.ADDI (.vreg vr) (.xreg rs1) (0 : BitVec 12)) <|
    .done RETIRE_SUCCESS
```

`JoltBytecode/JoltISA/Expansions/System.lean:176`

```lean
def csrrwProgram? (csr : BitVec 12) (rs1 rd : regidx) : Option Program :=
  match systemCSR? csr with
  | some supported => some (csrrwProgram supported rs1 rd)
  | none => none
```

## Sail Pipeline

The relevant generated Lean code is the important part.

For `mstatus`, Sail writes through `legalize_mstatus`:

`LeanRV64D/ZicsrInsts.lean:11708`

```lean
| (0x300, value) =>
  (do
    if ((xlen == 64) : Bool)
    then
      (do
        writeReg mstatus (← (legalize_mstatus (← readReg mstatus) value))
        (pure (Ok (← readReg mstatus))))
    else
      (do
        writeReg mstatus (← (legalize_mstatus (← readReg mstatus)
            ((Sail.BitVec.extractLsb (← readReg mstatus) 63 32) +++ value)))
        (pure (Ok (Sail.BitVec.extractLsb (← readReg mstatus) 31 0)))))
```

The `legalize_mstatus` function is:

`LeanRV64D/SysRegs.lean:994`

```lean
def legalize_mstatus (o : (BitVec 64)) (v : (BitVec 64)) : SailM (BitVec 64) := do
  let v := (Mk_Mstatus v)
  let o ← do
    (pure (_update_Mstatus_SIE
        (_update_Mstatus_MIE
          (_update_Mstatus_SPIE
            (_update_Mstatus_MPIE
              (_update_Mstatus_VS
                (_update_Mstatus_SPP
                  (_update_Mstatus_MPP
                    (_update_Mstatus_FS
                      (_update_Mstatus_XS
                        (_update_Mstatus_MPRV
                          (_update_Mstatus_SUM
                            (_update_Mstatus_MXR
                              (_update_Mstatus_TVM
                                (_update_Mstatus_TW
                                  (_update_Mstatus_TSR
                                    (_update_Mstatus_SPELP
                                      (_update_Mstatus_MPELP o
                                        (if ((hartSupports Ext_Zicfilp) : Bool)
                                        then (_get_Mstatus_MPELP v)
                                        else 0#1))
                                      (if ((hartSupports Ext_Zicfilp) : Bool)
                                      then (_get_Mstatus_SPELP v)
                                      else 0#1))
                                    (← do
                                      if ((← (currentlyEnabled Ext_S)) : Bool)
                                      then (pure (_get_Mstatus_TSR v))
                                      else (pure 0#1)))
                                  (← do
                                    if ((← (currentlyEnabled Ext_U)) : Bool)
                                    then (pure (_get_Mstatus_TW v))
                                    else (pure 0#1)))
                                (← do
                                  if ((← (currentlyEnabled Ext_S)) : Bool)
                                  then (pure (_get_Mstatus_TVM v))
                                  else (pure 0#1)))
                              (← do
                                if ((← (currentlyEnabled Ext_S)) : Bool)
                                then (pure (_get_Mstatus_MXR v))
                                else (pure 0#1)))
                            (← do
                              if ((← (virtual_memory_supported ())) : Bool)
                              then (pure (_get_Mstatus_SUM v))
                              else (pure 0#1)))
                          (← do
                            if ((← (currentlyEnabled Ext_U)) : Bool)
                            then (pure (_get_Mstatus_MPRV v))
                            else (pure 0#1))) (extStatus_to_bits Off))
                      (if ((hartSupports Ext_Zfinx) : Bool)
                      then (extStatus_to_bits Off)
                      else (_get_Mstatus_FS v)))
                    (← do
                      if ((← (have_nominal_privLevel (_get_Mstatus_MPP v))) : Bool)
                      then (pure (_get_Mstatus_MPP v))
                      else (pure (privLevel_to_bits (← (lowest_supported_privLevel ()))))))
                  (← do
                    if ((← (currentlyEnabled Ext_S)) : Bool)
                    then (pure (_get_Mstatus_SPP v))
                    else (pure 0#1)))
                (if ((hartSupports Ext_Zve32x) : Bool)
                then (_get_Mstatus_VS v)
                else 0b00#2)) (_get_Mstatus_MPIE v))
            (← do
              if ((← (currentlyEnabled Ext_S)) : Bool)
              then (pure (_get_Mstatus_SPIE v))
              else (pure 0#1))) (_get_Mstatus_MIE v))
        (← do
          if ((← (currentlyEnabled Ext_S)) : Bool)
          then (pure (_get_Mstatus_SIE v))
          else (pure 0#1))))
  let dirty :=
    (((extStatus_of_bits (_get_Mstatus_FS o)) == Dirty) || (((extStatus_of_bits (_get_Mstatus_XS o)) == Dirty) || ((extStatus_of_bits
            (_get_Mstatus_VS o)) == Dirty)))
  (pure (_update_Mstatus_SD o (bool_to_bit dirty)))
```

This is not a raw write. It reconstructs a legal `mstatus`, including forcing
unsupported fields to zero/off, legalizing privilege fields, and recomputing `SD`.

For `mtvec`, Sail writes through `set_mtvec`, which calls `legalize_tvec`:

`LeanRV64D/ZicsrInsts.lean:20202`

```lean
| (0x305, value) => (pure (Ok (← (set_mtvec value))))
```

`LeanRV64D/SysExceptions.lean:255`

```lean
def set_mtvec (value : (BitVec 64)) : SailM (BitVec 64) := do
  writeReg mtvec (← (legalize_tvec (← readReg mtvec) value))
  readReg mtvec
```

`LeanRV64D/SysRegs.lean:1210`

```lean
def legalize_tvec (o : (BitVec 64)) (v : (BitVec 64)) : SailM (BitVec 64) := do
  let v := (Mk_Mtvec v)
  match (trapVectorMode_of_bits (_get_Mtvec_Mode v)) with
  | TV_Direct => (pure v)
  | TV_Vector => (pure v)
  | _ =>
    (do
      match xtvec_mode_reserved_behavior with
      | Xtvec_Fatal =>
        (reserved_behavior
          (HAppend.hAppend "Tried to write a reserved value ("
            (HAppend.hAppend (Int.repr (BitVec.toNatInt (_get_Mtvec_Mode v)))
              ") to the MODE field of xtvec.")))
      | Xtvec_Ignore => (pure (_update_Mtvec_Mode v (_get_Mtvec_Mode o))))
```

This is not a raw write. Reserved `MODE` values are rejected or replaced with the
old mode, depending on the configured reserved-behavior policy.

For `mepc`, Sail reads through `align_pc` and writes through `legalize_xepc`:

`LeanRV64D/ZicsrInsts.lean:9478`

```lean
| 0x341 => (get_xepc Machine)
```

`LeanRV64D/SysExceptions.lean:224`

```lean
def get_xepc (p : Privilege) : SailM (BitVec 64) := do
  match p with
  | Machine => (align_pc (← readReg mepc))
  | Supervisor => (align_pc (← readReg sepc))
  | User => (internal_error "exceptions/sys_exceptions.sail" 45 "Invalid privilege level")
  | VirtualUser =>
    (internal_error "exceptions/sys_exceptions.sail" 46 "Hypervisor extension not supported")
  | VirtualSupervisor =>
    (internal_error "exceptions/sys_exceptions.sail" 47 "Hypervisor extension not supported")
```

`LeanRV64D/SysRegs.lean:1266`

```lean
def align_pc (addr : (BitVec 64)) : SailM (BitVec 64) := do
  if ((← (currentlyEnabled Ext_Zca)) : Bool)
  then (pure (BitVec.update addr 0 0#1))
  else (pure (Sail.BitVec.updateSubrange addr 1 0 (zeros (n := (1 -i (0 -i 1))))))
```

`LeanRV64D/ZicsrInsts.lean:20203`

```lean
| (0x341, value) => (pure (Ok (← (set_xepc Machine value))))
```

`LeanRV64D/SysExceptions.lean:234`

```lean
def set_xepc (p : Privilege) (value : (BitVec 64)) : SailM (BitVec 64) := do
  let target := (legalize_xepc value)
  match p with
  | Machine => writeReg mepc target
  | Supervisor => writeReg sepc target
  | User => (internal_error "exceptions/sys_exceptions.sail" 55 "Invalid privilege level")
  | VirtualUser =>
    (internal_error "exceptions/sys_exceptions.sail" 56 "Hypervisor extension not supported")
  | VirtualSupervisor =>
    (internal_error "exceptions/sys_exceptions.sail" 57 "Hypervisor extension not supported")
  (pure target)
```

`LeanRV64D/SysRegs.lean:1261`

```lean
def legalize_xepc (v : (BitVec 64)) : (BitVec 64) :=
  if ((hartSupports Ext_Zca) : Bool)
  then (BitVec.update v 0 0#1)
  else (Sail.BitVec.updateSubrange v 1 0 (zeros (n := (1 -i (0 -i 1)))))
```

Sail executes CSR register instructions through:

`LeanRV64D/InstsEnd.lean:71392`

```lean
def execute_CSRReg (csr : (BitVec 12)) (rs1 : regidx) (rd : regidx) (op : csrop) : SailM ExecutionResult := do
  let access_type := (csr_access_type op (rd == zreg) (rs1 == zreg))
  (doCSR csr (← (rX_bits rs1)) rd op access_type)
```

For `CSRRW`, `doCSR`:

`LeanRV64D/ZicsrInsts.lean:22115`

```lean
def doCSR (csr : (BitVec 12)) (rs1_val : (BitVec 64)) (rd : regidx) (op : csrop) (access_type : CSRAccessType) : SailM ExecutionResult := do
  if ((not (← (check_CSR csr (← readReg cur_privilege) access_type))) : Bool)
  then (pure (Illegal_Instruction ()))
  else
    (do
      if ((not (ext_check_CSR csr (← readReg cur_privilege) access_type)) : Bool)
      then (pure (Ext_CSR_Check_Failure ()))
      else
        (do
          let csr_val ← (( do
            if ((bne access_type CSRWrite) : Bool)
            then (read_CSR csr)
            else (pure (zeros (n := 64))) ) : SailM xlenbits )
          if ((bne access_type CSRRead) : Bool)
          then
            (do
              let new_val : xlenbits :=
                match op with
                | CSRRW => rs1_val
                | CSRRS => (csr_val ||| rs1_val)
                | CSRRC => (csr_val &&& (Complement.complement rs1_val))
              match (← (write_CSR csr new_val)) with
              | .Ok final_val =>
                (do
                  (csr_id_write_callback csr final_val)
                  (wX_bits rd csr_val)
                  (pure RETIRE_SUCCESS))
              | .Err () => (pure (Illegal_Instruction ())))
          else
            (do
              (csr_id_read_callback csr csr_val)
              (wX_bits rd csr_val)
              (pure RETIRE_SUCCESS))))
```

`align_pc` returns an aligned PC:

```text
if currentlyEnabled Ext_Zca:
  clear bit 0
else:
  clear bits 1:0
```

`legalize_xepc` returns a legal exception PC:

```text
if hartSupports Ext_Zca:
  clear bit 0
else:
  clear bits 1:0
```

## Problem

Jolt treats supported CSRs as raw virtual-register storage:

```text
rd       := old_csr_vreg
csr_vreg := rs1_val_raw
```

Sail treats these as architectural CSRs:

```text
mstatus write := legalize_mstatus old_mstatus rs1_val
mtvec write   := legalize_tvec old_mtvec rs1_val
mepc read     := align_pc old_mepc
mepc write    := legalize_xepc rs1_val
```

These are not equivalent in general.

For `mepc`, the mismatch is visible when the low alignment bit or bits are set:

```text
old_mepc = 0x1003
rs1_val  = 0x2003
rd != x0
```

Jolt writes raw values:

```text
rd        = 0x1003
mepc_vreg = 0x2003
```

Sail writes aligned/legalized values:

```text
rd   = align_pc 0x1003
mepc = legalize_xepc 0x2003
```

So the Jolt expansion is only equivalent if additional invariants guarantee:

```text
old_mepc = align_pc old_mepc
rs1_val  = legalize_xepc rs1_val
```

For `mstatus`, the expansion is only equivalent if:

```text
rs1_val = legalize_mstatus old_mstatus rs1_val
```

For `mtvec`, the expansion is only equivalent if:

```text
rs1_val = legalize_tvec old_mtvec rs1_val
```

Without those invariants, the expansion does not match RISC-V architectural CSR
behavior for `CSRRW`/`CSRW` targeting these CSRs.

## RISC-V Spec Reference

Official RISC-V privileged specification:

- `mstatus`: https://docs.riscv.org/reference/isa/v20260120/priv/machine.html#_machine_status_mstatus_and_mstatush_registers
- `mtvec`: https://docs.riscv.org/reference/isa/v20260120/priv/machine.html#_machine_trap_vector_base_address_mtvec_register
- `mepc`: https://docs.riscv.org/reference/isa/v20260120/priv/machine.html#_machine_exception_program_counter_mepc_register

For `mstatus`, the ISA describes it as the machine status register that controls
the hart's current operating state. Multiple fields are WARL or read-only-zero
depending on supported privilege levels and extensions. A raw write of arbitrary
bits is not the architectural model.

For `mtvec`, the ISA describes it as an MXLEN-bit WARL read/write register
containing BASE and MODE. The BASE and MODE fields are constrained: BASE is
aligned, MODE has defined encodings, and implementations may impose additional
constraints.

For `mepc`, the ISA states that `mepc` stores the virtual address of the interrupted or
excepting instruction when a trap enters M-mode, and that software may explicitly
write it. It also states that `mepc[0]` is always zero; on implementations with
32-bit instruction alignment, `mepc[1:0]` are zero, and `mepc[1]` may be masked on
reads when the current alignment is 32-bit.

Official RISC-V unprivileged CSR instruction specification:

- https://docs.riscv.org/reference/isa/v20260120/unpriv/zicsr.html

The spec states that `CSRRW` reads the old CSR value into `rd` and writes the
initial `rs1` value to the CSR, with the `rd = x0` case suppressing the CSR read.
For architectural `mepc`, that CSR read/write must respect the `mepc`
alignment/legalization rules above.

## Conclusion

For `mstatus`, `mtvec`, and `mepc`, Sail is applying RISC-V architectural CSR
behavior and Jolt is performing raw virtual-register moves. Jolt is wrong for
architectural RISC-V `CSRRW`/`CSRW` to these CSRs unless it either applies the
same legalization/alignment or proves the raw values are already fixed points of
the corresponding Sail legalizers.
