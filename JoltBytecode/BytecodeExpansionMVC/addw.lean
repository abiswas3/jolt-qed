/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari
-/

import Std.Tactic.Do
import JoltBytecode.BytecodeExpansions.Common.Cpu
import JoltBytecode.BytecodeExpansions.Common.Riscv
import JoltBytecode.BytecodeExpansions.Common.Virtual


/-!
# ADDW: mvcgen approach

Same theorem as `BytecodeExpansions/Instructions/addw.lean`, different proof
strategy. Instead of factoring into pure-function equality + a hand-rolled
lifting lemma (`format_r_ops_eq_of_fns_eq`), we:

  1. Write the Jolt decomposition as an imperative `Id.run do` block
  2. Let `mvcgen` handle the state plumbing
  3. Close everything with `grind`

## Comparison

  Original (manual lifting):
    - You build `format_r_exec` to abstract the read-apply-write pattern
    - You build `format_r_ops_eq_of_fns_eq` to lift pure equality to state equality
    - Each instruction invokes the lifting lemma with `funext`
    - For non-R-type instructions (loads, stores, CSR) you need new lifting lemmas

  mvcgen:
    - You write the execution as `Id.run do` with `let mut`
    - `mvcgen` generates verification conditions from the do-block automatically
    - `grind` discharges them
    - The same pattern works for ANY instruction shape — no per-format lemmas needed

For ADDW specifically (straight-line, no loops, no early return), both are
equally concise. mvcgen's real advantage shows for multi-step sequences,
loops, or early exits — see `verified-imperative-blog.lean`.
-/

set_option mvcgen.warning false
open Std.Do

-----------------------------------------------------------------------
-- Auxiliary: overwriting the same register twice collapses.
-- Cpu.lean has read_write_eq/ne but not this one.
-----------------------------------------------------------------------

@[simp] lemma write_write_eq {α β : Type} [DecidableEq α]
    (a : α) (b₁ b₂ : β) (ds : DataStore α β) :
    write a b₂ (write a b₁ ds) = write a b₂ ds := by
  funext x; unfold write; split <;> rfl

-----------------------------------------------------------------------
-- Step 0: Write the Jolt decomposition as an imperative program
-----------------------------------------------------------------------

/-- Jolt's ADDW decomposition: two sub-instructions executed sequentially.

    ```
    ADD                      rd, rs1, rs2   -- add 64-bit values
    VirtualSignExtendWord    rd, rd,  0     -- sign-extend lower 32 bits
    ```

    Each sub-instruction mutates the register file. We model this with
    `let mut reg` — the compiler desugars it into pure state-passing,
    and mvcgen reasons about that desugaring for us. -/
def addw_jolt_exec (rs1 rs2 rd : BitVec 5) (s : State) : State := Id.run do
  let mut reg := s.reg
  -- Sub-instruction 1: ADD rd, rs1, rs2
  reg := write rd (read rs1 reg + read rs2 reg) reg
  -- Sub-instruction 2: VirtualSignExtendWord rd, rd, 0
  reg := write rd (Jolt.virtualSignExtendWord (read rd reg)) reg
  return { s with reg := reg }

/-- RISC-V ADDW as a single state transformation (no do-notation). -/
def addw_riscv_exec (rs1 rs2 rd : BitVec 5) (s : State) : State :=
  { s with reg := write rd (Riscv.addw (read rs1 s.reg) (read rs2 s.reg)) s.reg }

-----------------------------------------------------------------------
-- Step 1: mvcgen computes what the Jolt execution actually does
-----------------------------------------------------------------------

/-- mvcgen handles the monadic plumbing — the `Id.run`, the `bind` chain
    from `let mut`, the sequential assignments — all automatically.

    Without mvcgen, you'd need to:
      1. Unfold `Id.run` and the do-block desugaring (`bind`, `pure`)
      2. Manually substitute through each `reg := ...` assignment
      3. Apply `read_write_eq` to simplify `read rd (write rd v ...)`
      4. Apply `write_write_eq` to collapse the double write to `rd`

    With mvcgen, those four steps become: `mvcgen; all_goals grind`.

    Compare with `VerifiedImperative.lean`'s CPU example — same pattern:
      generalize → Id.of_wp_run_eq → mvcgen → grind -/
theorem addw_jolt_spec (rs1 rs2 rd : BitVec 5) (s : State) :
    addw_jolt_exec rs1 rs2 rd s =
    ({ s with reg := write rd (Jolt.virtualSignExtendWord (read rs1 s.reg + read rs2 s.reg)) s.reg }) := by
  generalize h : addw_jolt_exec rs1 rs2 rd s = x   -- name the result
  apply Id.of_wp_run_eq h                           -- enter WP framework
  mvcgen                                             -- generate VCs from the do-block
  -- The VC compares two State structs with let-bound register intermediates.
  -- grind with explicit read/write lemmas resolves the DataStore reasoning:
  --   read_write_eq:  read a (write a b ds) = b
  --   write_write_eq: write a b₂ (write a b₁ ds) = write a b₂ ds
  all_goals grind [read_write_eq, write_write_eq]

-----------------------------------------------------------------------
-- Step 2: Pure function equality (same as original — the math doesn't change)
-----------------------------------------------------------------------

/-- The core mathematical fact: Riscv.addw = add then sign-extend.
    This is definitional — both sides unfold to the same expression. -/
theorem addw_pure_eq (x y : BitVec 64) :
    Riscv.addw x y = Jolt.virtualSignExtendWord (x + y) := by
  unfold Riscv.addw Jolt.virtualSignExtendWord; rfl

-----------------------------------------------------------------------
-- Step 3: State equivalence
-----------------------------------------------------------------------

/-- Final theorem: RISC-V ADDW and Jolt's two-step decomposition produce
    identical CPU states.

    Proof:
      1. `addw_jolt_spec` (via mvcgen) tells us what the Jolt side computes
      2. `addw_pure_eq` tells us Riscv.addw ≡ virtualSignExtendWord ∘ (+)
      3. After rewriting, both sides are definitionally equal

    No lifting lemma needed. No `format_r_exec`. No `funext`.
    mvcgen absorbed all the state plumbing in Step 1. -/
theorem addw_state_eq (rs1 rs2 rd : BitVec 5) (s : State) :
    addw_riscv_exec rs1 rs2 rd s = addw_jolt_exec rs1 rs2 rd s := by
  rw [addw_jolt_spec]                                         -- apply the mvcgen-derived spec
  unfold addw_riscv_exec Riscv.addw Jolt.virtualSignExtendWord -- unfold both sides fully
  rfl                                                          -- definitionally equal
