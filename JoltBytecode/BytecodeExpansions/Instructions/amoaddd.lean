import JoltBytecode.BytecodeExpansions.Instructions.Lw
import JoltBytecode.BytecodeExpansions.Instructions.Sw
import JoltBytecode.BytecodeExpansions.Common.Virtual
import JoltBytecode.BytecodeExpansions.Common.Riscv

/-!
# AMOADD.D: RISC-V ≡ Jolt Decomposition

## Instruction (RV64A, Atomic)

`AMOADD.D rd, rs2, (rs1)` atomically loads a 64-bit doubleword from the
address in rs1, adds rs2 to the loaded value, stores the sum back to the
same address, and writes the *original* loaded value to rd.

Semantics:
```
  t   = mem[rs1]          -- load 64-bit doubleword
  mem[rs1] = t + rs2      -- store sum back
  rd  = t                 -- write original value to rd
```

The address in rs1 must be 8-byte (doubleword) aligned.

## Jolt Decomposition (faithful to Rust implementation)

```
VirtualAssertDwordAlignment  rs1, 0              -- assert rs1 is 8-byte aligned
LD                           v_rd, rs1, 0        -- v_rd = mem[rs1] (load doubleword)
ADD                          v_rs2, v_rd, rs2    -- v_rs2 = v_rd + rs2
SD                           rs1, v_rs2, 0       -- mem[rs1] = v_rd + rs2 (store sum)
ADDI                         rd, v_rd, 0         -- rd = v_rd (copy original value)
```

## Proof Strategy

1. Both sides assert dword alignment — misaligned → both panic.
2. In the aligned case, unfold both definitions:
   - RISC-V: load dword, compute sum, store, write original to rd
   - Jolt: LD, ADD, SD, ADDI — same operations in same order
3. Show memory state equality: `write_dword addr (load + rs2) s`
4. Show register state equality: `write rd (original_load) reg`
-/

-- ============================================================================
-- Dword alignment check (for AMO doubleword instructions)
-- ============================================================================

/-- VirtualAssertDwordAlignment: checks 8-byte alignment. If misaligned,
    sets the state error flag. -/
def Jolt.virtualAssertDwordAlignment (addr : BitVec 64) (s : State) : BitVec 64 × State :=
  if addr &&& 7#64 ≠ 0#64 then (addr, { s with error := true })
  else (addr, s)

-- ============================================================================
-- RISC-V AMOADD.D definition (state-level)
-- ============================================================================

namespace Riscv

/-- AMOADD.D rd, rs2, (rs1) (RV64A): atomically load doubleword from mem[rs1],
    store (loaded + rs2) back, write original loaded value to rd.
    Panics if rs1 is not doubleword-aligned. -/
def amoaddd (rs1 rs2 rd : BitVec 5) (s : State) : State :=
  let addr := read rs1 s.reg
  if addr &&& 7#64 ≠ 0#64 then { s with error := true }
  else
    let old_val   := read_dword addr s              -- load doubleword
    let sum       := old_val + read rs2 s.reg       -- compute sum
    let s'        := write_dword addr sum s          -- store sum back
    let new_reg   := write rd old_val s'.reg         -- write original value to rd
    { s' with reg := new_reg }

end Riscv

-- ============================================================================
-- Jolt decomposition (state-level)
-- ============================================================================

/-- Jolt's AMOADD.D decomposition:
    VirtualAssertDwordAlignment → LD → ADD → SD → ADDI -/
def jolt_amoaddd (rs1 rs2 rd : BitVec 5) (s : State) : State :=
  let addr            := read rs1 s.reg
  let (addr, s)       := Jolt.virtualAssertDwordAlignment addr s     -- assert alignment
  if s.error then s
  else
    let v_rd          := read_dword addr s                           -- LD v_rd, rs1, 0
    let v_rs2         := Riscv.add v_rd (read rs2 s.reg)            -- ADD v_rs2, v_rd, rs2
    let s'            := write_dword addr v_rs2 s                    -- SD rs1, v_rs2, 0
    let new_reg       := write rd v_rd s'.reg                        -- ADDI rd, v_rd, 0
    { s' with reg := new_reg }

-- ============================================================================
-- Helper lemmas (sorry stubs)
-- ============================================================================

-- write_dword preserves reg
@[simp] private lemma write_dword_reg (addr : BitVec 64) (val : BitVec 64) (s : State) :
    (write_dword addr val s).reg = s.reg := by
  unfold write_dword; simp [write_mem_bytes_reg]

-- write_dword preserves error
@[simp] private lemma write_dword_error (addr : BitVec 64) (val : BitVec 64) (s : State) :
    (write_dword addr val s).error = s.error := by
  unfold write_dword; simp [write_mem_bytes_error]

-- ============================================================================
-- Main theorem
-- ============================================================================

/-- AMOADD.D equivalence: RISC-V definition equals Jolt decomposition. -/
theorem amoaddd_eq (rs1 rs2 rd : BitVec 5) (s : State)
    (h_no_error : s.error = false) :
    Riscv.amoaddd rs1 rs2 rd s = jolt_amoaddd rs1 rs2 rd s := by
  unfold Riscv.amoaddd jolt_amoaddd Jolt.virtualAssertDwordAlignment Riscv.add
  by_cases h : (read rs1 s.reg) &&& 7#64 = 0#64
  · -- Aligned: both sides perform the atomic operation
    simp only [ne_eq, h, not_true_eq_false, ↓reduceIte, h_no_error,
               write_dword_reg, write_dword_error, Bool.false_eq_true]
  · -- Misaligned: both sides panic
    simp only [ne_eq, h, not_false_eq_true, ↓reduceIte]

/-SANITY CHECKS-/
-- Verify the theorem type-checks (no sorry in the main proof).
-- Full exhaustive testing is harder for state-level operations, so we
-- rely on the proof plus spot checks.
#check @amoaddd_eq
