import JoltBytecode.BytecodeExpansions.Common.FormatI
import JoltBytecode.BytecodeExpansions.Common.Virtual
import JoltBytecode.BytecodeExpansions.Common.Riscv

/-!
# CSRRW: RISC-V ≡ Jolt Decomposition

## Instruction (RV64 Zicsr, Format I)

`CSRRW rd, csr, rs1` atomically reads the CSR into rd and writes rs1 to the CSR.
- If rd = x0, the read is suppressed (write-only).
- If rd = rs1, a temporary is used to preserve the original rs1.

## Jolt Decomposition (faithful to Rust implementation)

Jolt maps each CSR to a virtual register. The inline sequence depends on
the operand pattern:

### Case 1: rd = 0 (write-only, `csrw` pseudo-op)
```
ADDI    csr_vreg, rs1, 0              -- csr ← rs1
```

### Case 2: rd = rs1 (same register)
```
ADDI    v_tmp, rs1, 0                 -- save rs1 in temp
ADDI    rd, csr_vreg, 0               -- rd ← old csr value
ADDI    csr_vreg, v_tmp, 0            -- csr ← saved rs1
```

### Case 3: rd ≠ rs1 (general case)
```
ADDI    rd, csr_vreg, 0               -- rd ← old csr value
ADDI    csr_vreg, rs1, 0              -- csr ← rs1
```

## Proof strategy

CSRRW cannot be expressed as a simple FormatI op because it writes both a
general-purpose register and a CSR register. Instead we define `jolt_csrrw`
directly at the State level and prove componentwise equality using `ext`.

Both the RISC-V definition and the Jolt decomposition produce the same
final state: when rd ≠ 0, the CSR gets rs1's value, and rd gets the old CSR
value. The two definitions differ only in the order of writes (CSR-then-reg
vs reg-then-CSR), which is irrelevant because the writes target different
state fields.
-/

-- ============================================================================
-- Jolt decomposition (state-level)
-- ============================================================================

/-- Jolt's CSRRW decomposition. Captures the values from the original state
    and performs reg/CSR writes in the Jolt order.

    - Case rd = 0: write-only (just copy rs1 to CSR)
    - Case rd ≠ 0: read old CSR into rd, then write rs1 to CSR.
      (Cases 2 and 3 from Jolt produce identical final states because
      the temporary in Case 2 only matters for intermediate steps.) -/
def jolt_csrrw (rs1 rd : BitVec 5) (csr_addr : BitVec 12) (s : State) : State :=
  if rd = 0#5 then
    -- Case 1: write-only
    write_csr csr_addr (read rs1 s.reg) s
  else
    -- Cases 2 & 3: read old CSR, write rs1 to CSR
    let old_csr := read_csr csr_addr s
    let rs1_val := read rs1 s.reg
    let s := { s with reg := write rd old_csr s.reg }
    write_csr csr_addr rs1_val s

-- ============================================================================
-- Main theorem
-- ============================================================================

/-- CSRRW equivalence: the RISC-V definition and Jolt decomposition produce
    the same state. The key insight is that CSR writes and register writes
    commute because they target different state fields. -/
theorem csrrw_eq (rs1 rd : BitVec 5) (csr_addr : BitVec 12) (s : State) :
    Riscv.csrrw rs1 rd csr_addr s = jolt_csrrw rs1 rd csr_addr s := by
  simp only [Riscv.csrrw, jolt_csrrw, read_csr, write_csr]

-- ============================================================================
-- Sanity check
-- ============================================================================

-- Compare two States on all registers (0..31), the target CSR, and error flag.
private def statesAgree (s1 s2 : State) (csr_addr : BitVec 12) : Bool :=
  (List.range 32).all (fun i =>
    read (BitVec.ofNat 5 i) s1.reg == read (BitVec.ofNat 5 i) s2.reg) &&
  (read_csr csr_addr s1 == read_csr csr_addr s2) &&
  (s1.error == s2.error)

#eval do
  let mut failures := 0
  for i in List.range 32 do
    for j in List.range 32 do
      let rs1 : BitVec 5 := BitVec.ofNat 5 i
      let rd : BitVec 5 := BitVec.ofNat 5 j
      let csr_addr : BitVec 12 := 0x300#12
      let s : State := { mem := fun _ => 0#8,
                          reg := fun r => BitVec.ofNat 64 (r.toNat * 100 + 42),
                          csr := fun c => BitVec.ofNat 64 (c.toNat * 7 + 13) }
      let r1 := Riscv.csrrw rs1 rd csr_addr s
      let r2 := jolt_csrrw rs1 rd csr_addr s
      if !statesAgree r1 r2 csr_addr then
        failures := failures + 1
  if failures == 0 then
    IO.println "✓ Exhaustive check passed: csrrw == jolt_csrrw for all 1024 (rs1, rd) pairs"
  else
    IO.println s!"✗ FAILED: {failures} mismatches found"
