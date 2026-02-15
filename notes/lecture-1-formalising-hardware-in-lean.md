**NOTE**: This is mostly AI generated SPAM, asked to run my Lean proofs. I wanted to understand what it can generate.

# Lecture 1: Formalising Hardware Correctness in Lean 4

> *"Testing shows the presence of bugs, not their absence."* — Dijkstra

In this lecture, we'll learn how to write machine-checked mathematical proofs in Lean 4 by working through a real example: proving that a CPU instruction computes the same result as its replacement circuit. By the end, you'll understand the core mechanics of theorem proving in Lean and have a mental model for tackling similar proofs.

## 1. Why Formal Verification?

Suppose you're building a virtual machine (a software CPU). One of its instructions, `MULH`, computes the "high bits" of a signed multiplication. For performance reasons, you want to replace this single complex instruction with a sequence of simpler ones.

**The question**: does the replacement sequence always produce the same answer?

You could test it. For 8-bit numbers, there are only 256 x 256 = 65,536 input pairs — easy to check exhaustively. But real CPUs use 32-bit or 64-bit numbers. At 64 bits, there are 2^128 pairs — more than the number of atoms in the universe. Testing is hopeless.

This is where formal verification comes in. Instead of checking every input, we write a **proof** — a logical argument that the two computations are equivalent **for all possible inputs, at any bit-width**. And we have a computer (Lean) check that our argument is valid.

## 2. Setting Up: What You Need to Know

### 2.1 Types: Everything Has a Type

In Lean, every expression has a type. Think of types as "what kind of thing is this?"

```lean
7           : Nat          -- a natural number
-3          : Int          -- an integer
true        : Bool         -- a boolean
```

The type we'll work with most is `BitVec w` — a **bitvector of width `w`**. This represents a `w`-bit binary number, exactly like a CPU register.

```lean
(5 : BitVec 8)     -- the 8-bit number 00000101
(255 : BitVec 8)    -- the 8-bit number 11111111
```

### 2.2 Two Views of the Same Bits

A key concept: the same bitvector can be **interpreted** in two ways.

Take the 8-bit pattern `11111101`:

| Interpretation | Function | Value |
|---|---|---|
| **Unsigned** (just read the bits) | `x.toNat` | 253 |
| **Signed** (two's complement) | `x.toInt` | -3 |

This duality is at the heart of our proof. The original instruction uses signed arithmetic (`toInt`), while the replacement uses unsigned arithmetic (`toNat`) plus correction terms.

### 2.3 Functions in Lean

Functions are defined with `def`:

```lean
def signExtract (x : BitVec w) : Int :=
  if x.msb then -1 else 0
```

This says: "`signExtract` takes a bitvector `x` of any width `w`, and returns an integer. If the most significant bit is set (the number is negative), return -1; otherwise return 0."

The `{w : Nat}` is an **implicit argument** — Lean figures out the bit-width from context, so you don't have to write it every time.

### 2.4 Theorems and Proofs

A **theorem** states that something is true. A **proof** is the evidence.

```lean
theorem mulh_eq_mulhJolt (x y : BitVec w) : mulh x y = mulhJolt x y := by
  ...  -- proof goes here
```

This says: "For any bit-width `w` and any two bitvectors `x` and `y`, the function `mulh` returns the same result as `mulhJolt`."

The `by` keyword enters **tactic mode** — an interactive way to build proofs step by step.

## 3. The Problem: MULH vs. Its Replacement

### 3.1 The Original Instruction

The RISC-V `MULH` instruction computes the upper half of a signed multiplication:

```lean
def mulh (x y : BitVec w) : BitVec w :=
  BitVec.ofInt w (x.toInt * y.toInt / (2 ^ w : Int))
```

Reading this: take the signed values of `x` and `y`, multiply them (getting a potentially very large integer), divide by 2^w (keeping only the "high half"), and pack the result back into a `w`-bit bitvector.

### 3.2 The Replacement: A Sequence of Simpler Instructions

In the Jolt zkVM, `MULH` is replaced by seven simpler instructions:

```
VirtualMovsign  v_sx, rs1, 0      -- s_x = sign(rs1)
VirtualMovsign  v_sy, rs2, 0      -- s_y = sign(rs2)
MULHU           v_0,  rs1, rs2    -- v_0 = unsigned_high_mul(rs1, rs2)
MUL             v_sx, v_sx, rs2   -- v_sx = s_x * rs2
MUL             v_sy, v_sy, rs1   -- v_sy = s_y * rs1
ADD             v_0,  v_0,  v_sx  -- v_0 = v_0 + v_sx
ADD             rd,   v_0,  v_sy  -- rd  = v_0 + v_sy
```

In Lean, we define each instruction as a function and compose them:

```lean
namespace Jolt

def virtualMovSign (x : BitVec w) : BitVec w :=
  BitVec.ofInt w (signExtract x)

def mulhu (x y : BitVec w) : BitVec w :=
  BitVec.ofNat w (x.toNat * y.toNat / 2 ^ w)

end Jolt

def mulhJolt (x y : BitVec w) : BitVec w :=
  let v_sx := Jolt.virtualMovSign x       -- VirtualMovsign
  let v_sy := Jolt.virtualMovSign y       -- VirtualMovsign
  let v_0  := Jolt.mulhu x y              -- MULHU
  let v_sx := v_sx * y                    -- MUL
  let v_sy := v_sy * x                    -- MUL
  let v_0  := v_0 + v_sx                  -- ADD
  v_0 + v_sy                              -- ADD
```

Notice `MUL` and `ADD` are just `*` and `+` — Lean's built-in BitVec arithmetic is already modular (mod 2^w), exactly like a CPU.

### 3.3 The Intuition: Why Does This Work?

The key identity is **two's complement decomposition**:

```
signed_value(x) = unsigned_value(x) + sign(x) * 2^w
```

If `x` is non-negative, `sign(x) = 0` and the signed and unsigned values are the same.
If `x` is negative, `sign(x) = -1` and `signed_value = unsigned_value - 2^w`.

When you multiply two signed numbers, you can expand using this identity:

```
x_signed * y_signed = x_unsigned * y_unsigned
                    + sign(x) * y_unsigned * 2^w
                    + sign(y) * x_unsigned * 2^w
                    + sign(x) * sign(y) * 2^(2w)
```

Dividing by 2^w and taking mod 2^w, the last term vanishes. What remains is exactly what the replacement sequence computes.

## 4. Tactics: The Tools for Building Proofs

Before we walk through the proof, let's meet the tactics we'll use. Think of tactics as **moves in a puzzle game** — each one transforms the current goal into something simpler.

### 4.1 `rw` (rewrite)

The most fundamental tactic. If you have a proof that `A = B`, you can replace `A` with `B` (or vice versa) in the goal.

```lean
-- If we know: h : x + 0 = x
-- We can rewrite: rw [h]   (replaces x + 0 with x in the goal)
-- Or backwards:   rw [← h] (replaces x with x + 0)
```

**Gotcha**: `rw` replaces **all** occurrences. If `y` appears in multiple places and you only want to rewrite one of them, use `conv`:

```lean
conv_lhs => rw [h]   -- only rewrite on the left-hand side
```

We hit this exact issue in our proof. The rewrite `rw [hy]` (where `hy : y = ...`) would replace `y` everywhere — including inside `y.toNat` on the other side of the equation. Using `conv_lhs => rw [hy]` fixed it.

### 4.2 `unfold`

Replaces a function name with its definition:

```lean
unfold mulh
-- Replaces `mulh x y` with `BitVec.ofInt w (x.toInt * y.toInt / (2 ^ w : Int))`
```

### 4.3 `simp` (simplify)

An automated rewriting engine. It applies a large database of known simplification rules until nothing changes. You can also pass specific lemmas:

```lean
simp                           -- use all @[simp] lemmas
simp [BitVec.toNat_ofNat]     -- also use this specific lemma
simp only [h1, h2]            -- ONLY use these lemmas (more predictable)
```

### 4.4 `ring`

Automatically proves equalities that follow from ring axioms (commutativity, associativity, distributivity). Extremely powerful for polynomial-like rearrangements:

```lean
-- Goal: (a + b) * (c + d) = a*c + a*d + b*c + b*d
ring   -- done!
```

### 4.5 `split`

When the goal involves an `if-then-else`, `split` creates one subgoal for each branch:

```lean
-- Goal: (if x.msb then -1 else 0) * 2^w = ...
split
· -- Case: x.msb = true, so the expression is (-1) * 2^w = ...
· -- Case: x.msb = false, so the expression is 0 * 2^w = ...
```

### 4.6 `apply`

Uses a lemma or theorem to transform the goal. If the lemma says "to prove A, it suffices to prove B", then `apply` changes the goal from A to B:

```lean
-- Goal: (a : BitVec w) = (b : BitVec w)
apply BitVec.eq_of_toInt_eq
-- New goal: a.toInt = b.toInt
```

This is a common pattern: to prove two bitvectors are equal, prove their integer interpretations are equal.

### 4.7 `push_cast` and `norm_cast`

Handle coercions between number types (Nat to Int, etc.):

```lean
-- Goal: ↑(a * b) = ↑a * ↑b   (where ↑ is Nat → Int)
push_cast   -- done!
```

### 4.8 `positivity`

Proves that an expression is positive or non-negative:

```lean
-- Goal: (2 ^ w : Int) ≠ 0
positivity   -- done! (2^w is always positive)
```

### 4.9 `have`

Introduces a helper fact that you prove inline, then use later:

```lean
have h2w : (2 ^ w : Int) ≠ 0 := by positivity
-- Now h2w is available as a fact for the rest of the proof
```

## 5. The Proof, Step by Step

### 5.1 Phase 1: Bridging (BitVec World to Int World)

Our `mulhJolt` is defined using BitVec operations (addition, multiplication on bitvectors). But the mathematical proof works with integers. We need **bridging lemmas** to connect them.

**Key insight**: `BitVec.ofInt` is a ring homomorphism — it distributes over `+` and `*`:

```lean
BitVec.ofInt w (a + b) = BitVec.ofInt w a + BitVec.ofInt w b   -- ofInt_add
BitVec.ofInt w (a * b) = BitVec.ofInt w a * BitVec.ofInt w b   -- ofInt_mul
```

This means: it doesn't matter whether you add integers then convert to bitvectors, or convert first then add bitvectors. The result is the same. This is what makes the replacement sequence correct despite doing intermediate mod 2^w reductions.

**Bridging Lemma 1**: `virtualMovSign_eq_ofInt`

```lean
lemma virtualMovSign_eq_ofInt (x : BitVec w) :
    Jolt.virtualMovSign x = BitVec.ofInt w (signExtract x) := rfl
```

This is true **by definition** — we literally defined `virtualMovSign` as `BitVec.ofInt w (signExtract x)`. The proof is `rfl` (reflexivity — both sides are the same thing).

**Bridging Lemma 2**: `virtualMovSign_mul_eq`

```lean
lemma virtualMovSign_mul_eq (x y : BitVec w) :
    Jolt.virtualMovSign x * y =
      BitVec.ofInt w (signExtract x * (y.toNat : Int)) := by
  rw [virtualMovSign_eq_ofInt]
  have hy : y = BitVec.ofInt w (↑y.toNat : Int) := by
    rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  conv_lhs => rw [hy]
  rw [← BitVec.ofInt_mul]
```

Let's trace through this:

1. **`rw [virtualMovSign_eq_ofInt]`** — Replace `Jolt.virtualMovSign x` with `BitVec.ofInt w (signExtract x)`. Goal becomes:
   ```
   BitVec.ofInt w (signExtract x) * y = BitVec.ofInt w (signExtract x * ↑y.toNat)
   ```

2. **`have hy`** — We need `y` in `ofInt` form to use `ofInt_mul`. The chain:
   - `ofInt_natCast`: `BitVec.ofInt w ↑n = BitVec.ofNat w n`
   - `ofNat_toNat`: `BitVec.ofNat m x.toNat = setWidth m x`
   - `setWidth_eq`: `setWidth w x = x` (same width, no change)

   Together: `y = BitVec.ofInt w ↑y.toNat`.

3. **`conv_lhs => rw [hy]`** — Replace `y` with `BitVec.ofInt w ↑y.toNat` **only on the left side**. This is critical — a plain `rw [hy]` would also replace `y` inside `y.toNat` on the right side, creating a circular mess.

4. **`rw [← BitVec.ofInt_mul]`** — Fuse `ofInt(a) * ofInt(b)` into `ofInt(a * b)`. Both sides are now identical.

**Bridging Lemma 3**: `mulhu_eq_ofInt`

```lean
lemma mulhu_eq_ofInt (x y : BitVec w) :
    (Jolt.mulhu x y : BitVec w) =
      BitVec.ofInt w ((x.toNat : Int) * (y.toNat : Int) / (2 ^ w : Int)) := by
  unfold Jolt.mulhu
  have h : (x.toNat : Int) * (y.toNat : Int) / (2 ^ w : Int) =
      ↑(x.toNat * y.toNat / 2 ^ w) := by norm_cast
  rw [h, BitVec.ofInt_natCast]
```

The key step is `norm_cast`: it knows that for natural numbers, multiplying then dividing in Nat gives the same result as casting to Int then multiplying and dividing. This lets us rewrite the Int expression back to a Nat cast, where `ofInt_natCast` finishes the job.

**The Main Bridge**: `mulhJolt_eq_ofInt`

```lean
lemma mulhJolt_eq_ofInt (x y : BitVec w) :
    mulhJolt x y =
      BitVec.ofInt w (
        (x.toNat : Int) * (y.toNat : Int) / (2 ^ w : Int)
        + signExtract x * (y.toNat : Int)
        + signExtract y * (x.toNat : Int)) := by
  unfold mulhJolt
  simp only []
  rw [mulhu_eq_ofInt, virtualMovSign_mul_eq x y, virtualMovSign_mul_eq y x]
  rw [← BitVec.ofInt_add, ← BitVec.ofInt_add]
```

After unfolding and rewriting each instruction to its `ofInt` form, we use `← ofInt_add` twice to fuse the three separate `ofInt` applications into one:

```
ofInt(A) + ofInt(B) + ofInt(C)  →  ofInt(A + B) + ofInt(C)  →  ofInt(A + B + C)
```

### 5.2 Phase 2: The Mathematical Proof (Int World)

Now that we've bridged from BitVec to Int, we need three mathematical lemmas.

**Lemma 1: Two's Complement Identity**

```lean
lemma toInt_eq_toNat_add_signExtract_mul (x : BitVec w) :
    (x.toInt : Int) = (x.toNat : Int) + signExtract x * (2 ^ w : Int) := by
  unfold signExtract
  rw [BitVec.toInt_eq_msb_cond]
  split
  · simp; ring    -- msb = true:  toNat - 2^w = toNat + (-1) * 2^w
  · simp          -- msb = false: toNat = toNat + 0 * 2^w
```

We use `BitVec.toInt_eq_msb_cond`, a Lean library lemma that says:

```
x.toInt = if x.msb then x.toNat - 2^w else x.toNat
```

Then `split` gives us two cases, each closed by `simp` and `ring`.

**Lemma 2: Product Expansion**

```lean
lemma signed_product_expansion (x y : BitVec w) :
    (x.toInt * y.toInt : Int) =
      (x.toNat : Int) * (y.toNat : Int)
      + signExtract x * (y.toNat : Int) * (2 ^ w : Int)
      + signExtract y * (x.toNat : Int) * (2 ^ w : Int)
      + signExtract x * signExtract y * (2 ^ w : Int) * (2 ^ w : Int) := by
  rw [toInt_eq_toNat_add_signExtract_mul x, toInt_eq_toNat_add_signExtract_mul y]
  ring
```

Substitute Lemma 1 for both `x` and `y`, then `ring` handles the polynomial expansion. This is where `ring` really shines — expanding `(a + b*c) * (d + e*f)` by hand is tedious and error-prone, but `ring` does it instantly and correctly.

**Lemma 3: Division Extracts Coefficients**

```lean
lemma div_signed_product (x y : BitVec w) :
    x.toInt * y.toInt / (2 ^ w : Int) =
      (x.toNat : Int) * (y.toNat : Int) / (2 ^ w : Int)
      + signExtract x * (y.toNat : Int)
      + signExtract y * (x.toNat : Int)
      + signExtract x * signExtract y * (2 ^ w : Int) := by
  rw [signed_product_expansion]
  have h2w : (2 ^ w : Int) ≠ 0 := by positivity
  have hrearrange :
    ... = ... + (sx*y' + sy*x' + sx*sy*2^w) * (2 ^ w) := by ring
  rw [hrearrange]
  rw [Int.add_mul_ediv_right _ _ h2w]
  ring
```

The strategy:

1. Substitute the product expansion (Lemma 2).
2. **Rearrange** into the form `A + B * 2^w` using `ring`. This is a creative step — you need to see that the cross terms factor out.
3. Apply `Int.add_mul_ediv_right`: `(A + B * C) / C = A / C + B` (for `C ≠ 0`). This is the key number theory lemma — exact multiples of the divisor split off cleanly.
4. `ring` cleans up.

### 5.3 Phase 3: Putting It All Together

```lean
theorem mulh_eq_mulhJolt (x y : BitVec w) : mulh x y = mulhJolt x y := by
  rw [mulhJolt_eq_ofInt]                    -- Bridge: unfold to ofInt form
  unfold mulh
  apply BitVec.eq_of_toInt_eq               -- Reduce to Int equality
  simp only [BitVec.toInt_ofInt]            -- toInt(ofInt(i)) = i.bmod(2^w)
  rw [div_signed_product]                   -- Apply Lemma 3
  have key : sx * sy * 2^w = ↑(2^w) * (sx * sy) := by push_cast; ring
  rw [key, Int.bmod_add_mul_cancel]         -- Drop the multiple of 2^w
```

The last two lines are the punchline. After applying Lemma 3, the left side has an extra `sign(x) * sign(y) * 2^w` compared to the right. But both sides are wrapped in `.bmod(2^w)` (modular reduction). The lemma `Int.bmod_add_mul_cancel` says:

```
bmod(A + n * k, n) = bmod(A, n)
```

Any multiple of `n` vanishes under mod `n`. That extra term is a multiple of `2^w`, so it disappears. QED.

## 6. Sanity Checking: Trust but Verify

Before attempting a proof, it's wise to test your definitions computationally. Lean's `#eval` command runs code:

```lean
#eval do
  let mut failures := 0
  for i in List.range 256 do
    for j in List.range 256 do
      let x : BitVec 8 := BitVec.ofNat 8 i
      let y : BitVec 8 := BitVec.ofNat 8 j
      if mulh x y != mulhJolt x y then
        failures := failures + 1
  IO.println s!"Failures: {failures}"
-- Output: Failures: 0
```

This exhaustively checks all 65,536 8-bit pairs. It's not a proof (it only covers w=8), but it catches definition bugs before you spend hours on a proof that was never going to work.

## 7. Common Pitfalls and Patterns

### 7.1 `rw` Rewrites Too Much

When you have `hy : y = f(y.toNat)` and you `rw [hy]`, Lean replaces **every** `y` — including the one inside `y.toNat` on the other side. Use `conv_lhs` or `conv_rhs` to target specific sides:

```lean
conv_lhs => rw [hy]    -- only rewrite on the left
```

### 7.2 Casting Between Nat and Int

Moving between `Nat` and `Int` is a constant source of friction. Key lemmas:

| Pattern | Tactic |
|---|---|
| `↑(a * b) = ↑a * ↑b` | `push_cast` or `norm_cast` |
| `↑(a / b) = ↑a / ↑b` (for Nat) | `norm_cast` |
| `BitVec.ofInt w ↑n = BitVec.ofNat w n` | `rw [BitVec.ofInt_natCast]` |

### 7.3 `ofNat_toNat` Gives `setWidth`, Not the Original

A surprising subtlety:

```lean
BitVec.ofNat_toNat : BitVec.ofNat m x.toNat = setWidth m x
```

This gives `setWidth m x`, **not** `x`! You need `setWidth_eq` to go the last mile when `m = w`:

```lean
rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]   -- ofNat w x.toNat = x
```

### 7.4 Docstrings Can't Go Before `namespace`

In Lean 4, `/-- ... -/` docstrings can only precede declarations (`def`, `theorem`, `lemma`, etc.). Using one before `namespace` causes a parse error. Use a regular comment (`--`) instead.

### 7.5 The Proof Architecture

For proofs involving BitVec and integers, a common architecture is:

```
BitVec equality
    ↓  (apply eq_of_toInt_eq)
Int equality modulo 2^w
    ↓  (simp [toInt_ofInt])
bmod equality
    ↓  (rewrite, then bmod_add_mul_cancel to drop multiples of 2^w)
done
```

## 8. Key Takeaways

1. **Define, then prove.** Get your definitions right first. Use `#eval` to sanity-check before attempting a proof.

2. **Bridge between worlds.** Hardware lives in BitVec; math lives in Int. Bridging lemmas (especially `ofInt_add` and `ofInt_mul`) connect them.

3. **Lemma decomposition.** Break the proof into small, independently-provable lemmas. Each should have one clear mathematical insight.

4. **Let automation do the tedious parts.** `ring` handles polynomial algebra. `simp` applies known simplifications. `norm_cast` manages type coercions. `positivity` handles `2^w ≠ 0`. Reserve manual reasoning for the creative steps.

5. **Modular arithmetic is your friend.** The key insight in many hardware proofs: extra terms that are multiples of 2^w vanish under mod 2^w.

## 9. Exercises

1. **Warm-up**: Prove that `signExtract x` is always either `0` or `-1`. (Hint: `unfold`, `split`, `simp`.)

2. **Explore**: Change `mulhJolt` to remove one of the sign correction terms (e.g., delete the `v_sy` lines). Run the exhaustive 8-bit check. Which inputs fail?

3. **Challenge**: The `MULHU` instruction (unsigned high multiply) has a trivial Jolt decomposition — it's just itself. State and prove `mulhu x y = mulhu x y` as a warm-up for understanding the proof framework.

4. **Research**: Look up the RISC-V `SLT` (Set Less Than) instruction. What virtual instruction sequence might Jolt use to replace it? What would the definitions look like in Lean?

## Appendix: Tactic Quick Reference

| Tactic | What it does |
|---|---|
| `rfl` | Closes goal when both sides are definitionally equal |
| `rw [h]` | Rewrite using `h : A = B` (left to right) |
| `rw [← h]` | Rewrite using `h : A = B` (right to left) |
| `conv_lhs => rw [h]` | Rewrite only on the left-hand side |
| `unfold f` | Replace `f` with its definition |
| `simp` | Automated simplification |
| `simp only [h1, h2]` | Simplification with specific lemmas only |
| `ring` | Prove equalities using ring axioms |
| `split` | Case-split on an `if-then-else` or `match` |
| `apply h` | Use `h` to transform the goal |
| `exact h` | Close the goal directly with `h` |
| `have h : P := by ...` | Prove a helper fact inline |
| `push_cast` | Push coercions (↑) towards leaves |
| `norm_cast` | Normalize coercions |
| `positivity` | Prove an expression is positive/nonneg |
| `omega` | Decide linear arithmetic over Nat/Int |
