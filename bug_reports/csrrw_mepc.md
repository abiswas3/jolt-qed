# Bug Report: CSRRW `mepc` Expansion Does Not Apply RISC-V `mepc` Alignment Rules

## Instruction
`CSRRW mepc, rs1, rd` / `CSRW mepc, rs1`.

The relevant CSR is machine exception program counter `mepc`, CSR address `0x341`.

## Jolt Expansion

Jolt lowers `CSRRW` to plain `ADDI` copies through a reserved virtual register for
the CSR.

Evidence:

- Rust expansion: `/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-program/src/expand/control_flow/csrrw.rs:10`
- CSR-to-virtual-register mapping: `/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-program/src/expand/allocator.rs:60`

Pseudo-code for the expansion:

```text
virtual_reg := virtual_register_for_csr(csr)

if rd == x0:
  virtual_reg := rs1
else if rd == rs1:
  temp := rs1
  rd := virtual_reg
  virtual_reg := temp
else:
  rd := virtual_reg
  virtual_reg := rs1
```

For `mepc`, `virtual_register_for_csr(0x341)` returns Jolt's reserved `mepc`
virtual register. There is no alignment, masking, or legalization step in the
`CSRRW` expansion.

## Sail Pipeline

Sail executes CSR register instructions through:

```text
execute_CSRReg csr rs1 rd CSRRW
  -> rX_bits rs1
  -> doCSR csr rs1_val rd CSRRW access_type
```

Evidence:

- `execute_CSRReg`: `/Users/ari.biswas/Lean/lz-qed/LeanRV64D/InstsEnd.lean:71392`
- `doCSR`: `/Users/ari.biswas/Lean/lz-qed/LeanRV64D/ZicsrInsts.lean:22115`

For `CSRRW`, `doCSR`:

```text
if rd != x0:
  csr_val := read_CSR csr
else:
  csr_val := 0

new_val := rs1_val
write_CSR csr new_val
wX_bits rd csr_val
```

For `mepc`, the read path is:

```text
read_CSR 0x341
  -> get_xepc Machine
  -> align_pc (readReg mepc)
```

Evidence:

- `read_CSR 0x341`: `/Users/ari.biswas/Lean/lz-qed/LeanRV64D/ZicsrInsts.lean:9478`
- `get_xepc Machine`: `/Users/ari.biswas/Lean/lz-qed/LeanRV64D/SysExceptions.lean:224`
- `align_pc`: `/Users/ari.biswas/Lean/lz-qed/LeanRV64D/SysRegs.lean:1266`

`align_pc` returns an aligned PC:

```text
if currentlyEnabled Ext_Zca:
  clear bit 0
else:
  clear bits 1:0
```

For `mepc`, the write path is:

```text
write_CSR 0x341 rs1_val
  -> set_xepc Machine rs1_val
  -> target := legalize_xepc rs1_val
  -> writeReg mepc target
```

Evidence:

- `write_CSR 0x341`: `/Users/ari.biswas/Lean/lz-qed/LeanRV64D/ZicsrInsts.lean:20203`
- `set_xepc Machine`: `/Users/ari.biswas/Lean/lz-qed/LeanRV64D/SysExceptions.lean:234`
- `legalize_xepc`: `/Users/ari.biswas/Lean/lz-qed/LeanRV64D/SysRegs.lean:1261`

`legalize_xepc` returns a legal exception PC:

```text
if hartSupports Ext_Zca:
  clear bit 0
else:
  clear bits 1:0
```

## Problem

Jolt treats `mepc` as raw virtual-register storage:

```text
rd        := old_mepc_raw
mepc_vreg := rs1_val_raw
```

Sail treats `mepc` as an architectural PC CSR:

```text
rd   := align_pc old_mepc
mepc := legalize_xepc rs1_val
```

These are not equivalent when the low alignment bit or bits are set.

Example:

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

Without those invariants, the expansion does not match RISC-V architectural
behavior for `CSRRW`/`CSRW` targeting `mepc`.

## RISC-V Spec Reference

Official RISC-V privileged specification, `mepc`:

- https://docs.riscv.org/reference/isa/v20260120/priv/machine.html

The spec states that `mepc` stores the virtual address of the interrupted or
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

For `mepc`, Sail is applying RISC-V architectural behavior and Jolt is performing
raw virtual-register moves. Jolt is wrong for architectural RISC-V `CSRRW`/`CSRW`
to `mepc` unless it either applies the same alignment/legalization or proves the
low bit or low two bits are already zero on every relevant read and write.
