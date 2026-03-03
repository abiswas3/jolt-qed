import JoltBytecode.BytecodeExpansions.Common.FormatR
import JoltBytecode.BytecodeExpansions.Common.Virtual
import JoltBytecode.BytecodeExpansions.Common.Riscv


/-!
# ADDW: RISC-V ≡ Jolt Decomposition

## Instruction (RV64I, Format R)

`ADDW rd, rs1, rs2` adds 64 bit signed integers in rs1 and rs2, truncates the
result to 32 bits, sign-extends to 64 bits, and writes to rd.

## Jolt Decomposition (faithful to Rust implementation)

```
ADD                      rd rs1 rs2                   -- add 
VirtualSignExtendWord    rd, rd, 0                    -- sign-extend lower 32 bits
```

## Proof
This proof is almost definitionally equivalent. 
-/

-- Step 0: Write them down as two pure functions
def addwJolt (rs1_val rs2_val: BitVec 64) : BitVec 64 := 
  Jolt.virtualSignExtendWord (rs1_val + rs2_val)

-- Step 1 write the pure function equivalence 
theorem addw_eq_addwJolt (rs1_val rs2_val : BitVec 64) :
    Riscv.addw rs1_val rs2_val = addwJolt rs1_val rs2_val := by
  unfold Riscv.addw addwJolt Jolt.virtualSignExtendWord
  rfl

-- Step 2: Write down the state equivalence 
-- I like this breakdown a little more
theorem addw_state_eq (rs1 rs2 rd : BitVec 5) (s: State) : 
    format_r_exec rs1 rs2 rd Riscv.addw s = format_r_exec rs1 rs2 rd addwJolt s := by { 
      -- h is a proof that the these are equal
      -- we get this proof by invoking the theorem we wrote 
      have fn_equal: Riscv.addw = addwJolt := by funext rs1_val rs2_val; exact addw_eq_addwJolt rs1_val rs2_val; 
      exact format_r_ops_eq_of_fns_eq Riscv.addw addwJolt rs1 rs2 rd s fn_equal
}

