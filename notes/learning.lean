import Mathlib.Tactic
import Mathlib.Data.BitVec

/-!
# Learning Lean Tactics by Example

Open this file in VS Code with the Lean extension. Place your cursor on any
line inside a `by` block and the **Lean Infoview** panel will show you the
current proof state (hypotheses above the bar, goal below).

Try deleting a tactic line and watch how the goal changes. This is the best
way to build intuition.
-/

-- ============================================================================
-- 1. conv_lhs / conv_rhs — Surgical Rewrites
-- ============================================================================

/-!
## `conv_lhs` and `conv_rhs`

**Problem**: `rw [h]` replaces ALL occurrences of a pattern. Sometimes you
only want to rewrite on one side of an equation.

`conv_lhs => ...` enters a "cursor" mode where you're focused on just the
left-hand side. Same idea with `conv_rhs` for the right.

Think of it like find-and-replace with "Replace in selection" turned on,
instead of "Replace all".
-/

-- Example 1a: rw replaces EVERYWHERE
-- Here that's fine — we want both `a`s replaced.
example (a b : Nat) (h : a = b + 1) : a + a = (b + 1) + (b + 1) := by
  rw [h]
  -- Both `a`s became `b + 1`. Goal closes.

-- Example 1b: But what if we only want to rewrite ONE side?
-- Goal: a + 3 = (b + 1) + 3.  We want to rewrite `a` only on the LEFT.
-- (Plain `rw [h]` would also change the RHS if `a` appeared there.)
example (a b : Nat) (h : a = b + 1) : a + 3 = (b + 1) + 3 := by
  conv_lhs => rw [h]
  -- Only the LHS was rewritten. Now both sides are `(b + 1) + 3`.

-- Example 1c: conv_rhs — rewrite only on the right
example (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  conv_rhs => rw [← h]
  -- Rewrote `b` to `a` on the RHS only. Now both sides are `a + 1`.

-- Example 1d: The real gotcha — rewriting a variable that appears in subterms.
-- This is EXACTLY the bug we hit in the MULH proof.
-- Here `y` appears both as a BitVec and inside `y.toNat` on the RHS.
-- A plain `rw [hy]` would replace `y` in `y.toNat` too — creating a mess.
example (y : BitVec 8) (hy : y = BitVec.ofInt 8 (↑y.toNat : Int)) :
    (3 : BitVec 8) * y = (3 : BitVec 8) * BitVec.ofInt 8 (↑y.toNat : Int) := by
  conv_lhs => rw [hy]
  -- Only replaced `y` on the left. `y.toNat` on the right is untouched.

-- Example 1e: You can also navigate INSIDE a term with conv
example (a b c : Nat) (h : b = 0) : a + (b + c) = a + (0 + c) := by
  conv_lhs => rw [h]

-- ============================================================================
-- 2. simp only — Predictable Simplification
-- ============================================================================

/-!
## `simp` vs `simp only`

`simp` is Lean's automated simplifier. It applies hundreds of rewrite rules
tagged with `@[simp]` until nothing changes. It's powerful but can be
unpredictable — it might simplify things you didn't want changed, or fail
because two simp lemmas conflict.

`simp only [h1, h2, h3]` is the controlled version: it ONLY uses the
lemmas you list. This makes proofs:
- **Reproducible**: won't break when someone adds a new @[simp] lemma
- **Readable**: you can see exactly what facts are being used
- **Debuggable**: if it fails, you know which lemma is missing
-/

-- Example 2a: simp knows a lot of basic facts
example (n : Nat) : n + 0 = n := by simp
example (n : Nat) : 0 + n = n := by simp
example (n : Nat) : n * 1 = n := by simp
example (b : Bool) : (if true then b else false) = b := by simp

-- Example 2b: simp only — you choose what it uses
example (n : Nat) : n + 0 = n := by
  simp only [Nat.add_zero]   -- explicitly: "use the fact that x + 0 = x"

-- Example 2c: simp only with a hypothesis
example (a b : Nat) (h : a = 0) : a + b = b := by
  simp only [h, Nat.zero_add]  -- substitute a = 0, then simplify 0 + b

-- Example 2d: simp only [] — the empty list
-- With no lemmas, it just does basic reductions (beta, let-bindings).
-- This is useful for "cleaning up" after `unfold`.
example (n : Nat) :
    (let x := n + 1; x * 2) = (n + 1) * 2 := by
  simp only []   -- reduces the let-binding, nothing else

-- Example 2e: In our MULH proof, we use `simp only [BitVec.toInt_ofInt]`
-- to apply JUST this one rule, leaving everything else untouched.
example (i : Int) (w : Nat) :
    (BitVec.ofInt w i).toInt = i.bmod (2 ^ w) := by
  simp only [BitVec.toInt_ofInt]

-- ============================================================================
-- 3. push_cast — Push Coercions Toward Leaves
-- ============================================================================

/-!
## `push_cast`

When you mix number types (Nat and Int), Lean inserts coercion arrows `↑`.
For example, if `a : Nat`, then `(↑a : Int)` means "treat `a` as an integer".

`push_cast` pushes these coercions inward through operations:

```
↑(a * b)  →  ↑a * ↑b
↑(a + b)  →  ↑a + ↑b
↑(2 ^ n)  →  (2 : Int) ^ n
```

The name "push" means: push the `↑` from the outside toward the leaves
(individual variables).

After `push_cast`, all operations are in the target type (Int), and
each individual variable carries its own `↑`. This often makes the goal
amenable to `ring` or `omega`.
-/

-- Example 3a: push_cast distributes ↑ over *
example (a b : Nat) : (↑(a * b) : Int) = ↑a * ↑b := by push_cast; ring

-- Example 3b: push_cast distributes ↑ over +
example (a b : Nat) : (↑(a + b) : Int) = ↑a + ↑b := by push_cast; ring

-- Example 3c: push_cast handles nested operations
example (a b c : Nat) :
    (↑(a * b + c) : Int) = ↑a * ↑b + ↑c := by push_cast; ring

-- Example 3d: push_cast with 2^w (common in bitvector proofs)
-- This is used in our MULH proof to normalize ↑(2^w : Nat) to (2 : Int) ^ w
example (w : Nat) : (↑(2 ^ w : Nat) : Int) = (2 : Int) ^ w := by push_cast; ring

-- Example 3e: push_cast + ring — a common combo
-- push_cast normalizes the casts, then ring handles the algebra
example (a b : Nat) :
    (↑a : Int) * ↑b * (2 : Int) ^ 8 =
    ↑(2 ^ 8 : Nat) * (↑a * ↑b) := by
  push_cast
  ring

-- ============================================================================
-- 4. norm_cast — Normalize Coercions
-- ============================================================================

/-!
## `norm_cast`

`norm_cast` is the heavy-duty version of `push_cast`. It can:
- Push coercions inward (like `push_cast`)
- Pull coercions outward
- Cancel redundant coercions
- Prove goals that are true "up to casting"

Use `push_cast` when you want a specific direction (push inward, then use
`ring` or another tactic to finish).
Use `norm_cast` when you want the tactic to decide the direction AND close
the goal in one shot.

A key use: for natural numbers, multiplication and division commute with
the cast to integers: `↑(a * b / c) = ↑a * ↑b / ↑c`. This is NOT true
for all integers (integer division is quirky), but it IS true when
everything is non-negative. `norm_cast` knows this.
-/

-- Example 4a: norm_cast proves cast equalities in one shot
example (a b : Nat) : (↑(a + b) : Int) = ↑a + ↑b := by norm_cast

-- Example 4b: norm_cast handles division of Nats cast to Int
-- This is critical in our MULHU bridging lemma
example (a b c : Nat) :
    (↑a : Int) * ↑b / ↑c = ↑(a * b / c) := by norm_cast

-- Example 4c: norm_cast can close goals about inequalities too
example (a : Nat) : (0 : Int) ≤ ↑a := by norm_cast; omega

-- Example 4d: The difference between push_cast and norm_cast:
-- push_cast pushes ↑ inward and stops. norm_cast tries to close the goal.
-- If the goal isn't closeable after pushing, you need another tactic.
example (a b : Nat) : (↑(a + b) : Int) = ↑a + ↑b := by
  norm_cast  -- closes it in one step

-- With push_cast you'd need:
example (a b : Nat) : (↑(a + b) : Int) = ↑a + ↑b := by
  push_cast; ring  -- push_cast normalizes, ring finishes

-- ============================================================================
-- 5. positivity — Prove Things Are Positive / Non-Negative
-- ============================================================================

/-!
## `positivity`

`positivity` proves goals of the form:
- `0 < expr`  (strictly positive)
- `0 ≤ expr`  (non-negative)
- `expr ≠ 0`  (nonzero)

It works by structural analysis: 2 is positive, powers of positives are
positive, products of positives are positive, etc.

We use it constantly in bitvector proofs because many lemmas require
`2^w ≠ 0` as a side condition (you can't divide by zero).
-/

-- Example 5a: basic positivity
example : (0 : Int) < 42 := by positivity
example : (0 : Int) < 2 ^ 10 := by positivity

-- Example 5b: the key use case — 2^w ≠ 0
-- Almost every division lemma needs this.
example (w : Nat) : (2 ^ w : Int) ≠ 0 := by positivity

-- Example 5c: products of positive things are positive
example (a : Nat) : (0 : Int) < 2 ^ a * 3 := by positivity

-- Example 5d: In our MULH proof (Lemma 3), we need 2^w ≠ 0 to apply
-- the division lemma Int.add_mul_ediv_right:
--   (A + B * C) / C = A / C + B    (requires C ≠ 0)
-- We get this with:
--   have h2w : (2 ^ w : Int) ≠ 0 := by positivity

-- ============================================================================
-- 6. omega — Linear Arithmetic Decision Procedure
-- ============================================================================

/-!
## `omega`

`omega` is a decision procedure for **linear arithmetic** over `Nat` and `Int`.
It can automatically prove any true statement that involves:
- Variables
- Constants (0, 1, 2, ...)
- Addition (+) and subtraction (-)
- Multiplication by constants (2 * n, 3 * n, ...)
- Comparisons (<, ≤, =, ≠, ≥, >)
- Logical connectives (∧, ∨, →)

It CANNOT handle:
- Multiplication of two variables (n * m)
- Division
- Exponentiation (2 ^ n)

Think of `omega` as a calculator for inequalities and equations.
-/

-- Example 6a: basic arithmetic
example : 2 + 3 = 5 := by omega
example (n : Nat) : n < n + 1 := by omega

-- Example 6b: omega handles implications and case splits
example (n : Nat) (h : n ≥ 5) : n ≥ 3 := by omega

-- Example 6c: omega can prove modular arithmetic facts
example (n : Nat) (h : n < 256) : n % 256 = n := by omega

-- Example 6d: omega with multiple hypotheses
example (a b : Nat) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by omega

-- Example 6e: omega with Int
example (a b : Int) (h : a + b = 10) (h2 : a = 3) : b = 7 := by omega

-- Example 6f: What omega CANNOT do (uncomment to see it fail):
-- example (a b : Nat) : a * b = b * a := by omega   -- FAILS: variable * variable
-- Use `ring` for that instead:
example (a b : Nat) : a * b = b * a := by ring

-- Example 6g: In bitvector proofs, omega is useful for Nat bounds:
example (x : BitVec 8) : x.toNat < 256 := x.isLt

-- omega can reason from BitVec bounds:
example (x : BitVec 8) : x.toNat + 1 ≤ 256 := by omega

-- ============================================================================
-- 7. Combining Tactics — Real Patterns from the MULH Proof
-- ============================================================================

/-!
## Putting It Together

Here are some common patterns that combine the tactics above.
These are taken directly from the MULH proof.
-/

-- Pattern A: "push_cast; ring" — normalize casts, then do algebra
-- Used in the main theorem to rearrange sign terms.
example (sx sy : Int) (w : Nat) :
    sx * sy * (2 : Int) ^ w = ↑(2 ^ w : Nat) * (sx * sy) := by
  push_cast   -- ↑(2^w : Nat) becomes (2 : Int) ^ w
  ring        -- rearrange: sx * sy * 2^w = 2^w * (sx * sy)

-- Pattern B: "unfold ... ; split ; simp" — case-split on a definition
-- Used in Lemma 1 to handle the two's complement cases.
-- (Simplified version with a toy definition)
def mySign (b : Bool) : Int := if b then -1 else 0

example (b : Bool) : mySign b * 0 = 0 := by
  unfold mySign   -- expose the if-then-else
  split           -- case on b
  · simp          -- true case: (-1) * 0 = 0
  · simp          -- false case: 0 * 0 = 0

-- Pattern C: "have h := ... ; rw [h]" — prove a fact, then use it
-- Used in Lemma 3 to rearrange terms before applying a division lemma.
example (a b c : Int) (hc : c ≠ 0) :
    (a + b * c) / c = a / c + b := by
  exact Int.add_mul_ediv_right a b hc

-- Pattern D: "apply eq_of_toInt_eq ; simp [toInt_ofInt]" — BitVec to Int
-- The standard opening for BitVec equality proofs.
example (a b : Int) (w : Nat) (h : a.bmod (2^w) = b.bmod (2^w)) :
    BitVec.ofInt w a = BitVec.ofInt w b := by
  apply BitVec.eq_of_toInt_eq
  simp only [BitVec.toInt_ofInt]
  exact h
