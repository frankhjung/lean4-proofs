import Mathlib.Algebra.Group.Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
-- import Plausible

/-!
Generic implementation for getting a slice of a list.

This extends `List` with a slice function.
 -/
def List.slice {α : Type u}
    (l : List α)  -- the list to slice
    (s : ℕ := 0) -- start index for slice
    (e : ℕ := l.length) -- end index for slice
    : List α :=
  (l.drop s).take (e - s)

namespace Structure

#eval IO.println "Structure.Structure"

/-!
# Maths: Proofs with Structure

Examples from [MoP](https://hrmacbeth.github.io/math2001/index.html), chapters
[2.1 Intermediate Steps](https://hrmacbeth.github.io/math2001/02_Proofs_with_Structure.html#intermediate-steps)
and
[2.2 Invoking lemmas](https://hrmacbeth.github.io/math2001/02_Proofs_with_Structure.html#invoking-lemmas)

## Plausible Tactic

The [plausible tactic](https://api.cslib.io/docs/Plausible/Tactic.html) is a
property testing tool (similar to QuickCheck). It works by randomly generating
instances to search for counterexamples.

Currently, the Plausible library in Lean 4 does not include a built-in random
generator (SampleableExt) for the rational numbers (ℚ). Because it does not
know how to generate random rationals, it fails with an error.

To test hypotheses using plausible, you can temporarily change the types from ℚ
to integers (ℤ), which it can generate:

```lean4
example {r s : ℤ}
  (h1 : s + 3 ≥ r)
  (h2 : s + r ≤ 3)
  : r ≤ 3 := by plausible
```

-/

-- example {r s : ℤ}
--   (h1 : s + 3 ≥ r)
--   (h2 : s + r ≤ 3)
--   : r ≤ 3 := by plausible

/-!
## [2.1 Intermediate Steps](https://hrmacbeth.github.io/math2001/02_Proofs_with_Structure.html#intermediate-steps)

### [2.1.1](https://hrmacbeth.github.io/math2001/02_Proofs_with_Structure.html#example)

Let $a$ and $b$ be real numbers and suppose that
$a - 5b = 4$ and $b + 2 = 3$. Show that $a = 9$.

-/
example {a b : ℝ}
  (h1 : a - 5 * b = 4)
  (h2 : b + 2 = 3)
  : a = 9 := by
  have hb : b = 1 := by linarith [h2]
  calc
    a = a - 5 * b + 5 * b := by ring
    _ = 4 + 5 := by rw [h1, hb]; simp
    _ = 9 := by norm_num

/-!
### [2.1.1](https://hrmacbeth.github.io/math2001/02_Proofs_with_Structure.html#example)

Simplified proof using
[linarith](https://lean-lang.org/doc/reference/latest/The--grind--tactic/Linear-Arithmetic-Solver/).

-/
example {a b : ℝ}
  (h1 : a - 5 * b = 4)
  (h2 : b + 2 = 3)
  : a = 9 := by linarith

/-!
### [2.1.3](https://hrmacbeth.github.io/math2001/02_Proofs_with_Structure.html#id3)

Let $s$ and $r$ be rational numbers, and suppose that $s + 3 \ge r$ and $s + r
\le 3$. Show that $r \le 3$.

Introducing intermediate hypothesis using `have` avoids the [principle of
logical explosion](https://en.wikipedia.org/wiki/Principle_of_explosion).

-/
example {r s : ℚ}
  (h1 : s + 3 ≥ r)
  (h2 : s + r ≤ 3)
  : r ≤ 3 := by
  have hr : r = (r + r) / 2 := by ring
  have hs : r ≤ 3 - s := by linarith
  calc
    r = (r + r) / 2 := hr -- by hypothesis hr
    _ ≤ ((s + 3) + (3 - s)) / 2 := by gcongr
    _ = 3 := by ring

/-!
## [2.2 Invoking Lemmas](https://hrmacbeth.github.io/math2001/02_Proofs_with_Structure.html#invoking-lemmas)

### [2.2.1](https://hrmacbeth.github.io/math2001/02_Proofs_with_Structure.html#id9)

Let $x$ be a rational number, and suppose that $3x = 2$. Show that $x ≠ 1$.

Here we will use an existing lemma,
[ne_of_lt](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Defs/PartialOrder.html#ne_of_lt)

-/
example {x : ℚ}
  (hx : 3 * x = 2)
  : x ≠ 1 := by
  apply ne_of_lt  -- apply lemma convert ≠ to an inequality
  calc
    x = 3 * x / 3 := by ring -- introduce relationship so we can use hx
    _ = 2 / 3 := by rw [hx] -- substitute hx
    _ < 1 := by norm_num -- prove inequality using `norm_num`

/-!
### [2.2.2](https://hrmacbeth.github.io/math2001/02_Proofs_with_Structure.html#ne-of-gt)

Let $y$ be a real number. Show that $y^2 + 1 ≠ 0$.

It suffices to prove that $0 < y^2 + 1$, which is clear since squares are
non-negative.

Here we will use an existing lemma,
[ne_of_gt](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Defs/PartialOrder.html#ne_of_gt)

-/
example {y : ℝ} : y ^ 2 + 1 ≠ 0 := by
  apply ne_of_gt
  have hy : y ^ 2 ≥ 0 := sq_nonneg y -- squares are non-negative
  calc
    y ^ 2 + 1 ≥ 0 + 1 := by gcongr -- substitute hy
    _ > 0 := by norm_num -- prove inequality using `norm_num`

/-!
Can also be proven with the
[positivity](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Positivity/Core.html#positivity)
tactic.

-/
example {y : ℝ} : y ^ 2 + 1 ≠ 0 := by
  positivity

/-!
Checking $√2 ≤ 2 by applying
[sqrt_le_iff](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Sqrt.html#Real.sqrt_le_iff)
lemma.

This applies the theorem to the `norm_num` tactic.

-/
example : Real.sqrt 2 ≤ 2 := by
  norm_num[Real.sqrt_le_iff]

/-!
We can also `apply` the lemma using `mpr`, where:

Real.sqrt_le_iff.mpr : (0 ≤ y ∧ x ≤ y ^ 2) → Real.sqrt x ≤ y

`mpr`: is a projection (lemma) that stands for "modus ponens reverse"

-/
example : Real.sqrt 2 ≤ 2 := by
  apply Real.sqrt_le_iff.mpr  -- apply lemma using mpr
  norm_num -- prove inequality using `norm_num`

/-!
### [2.1.2](https://hrmacbeth.github.io/math2001/02_Proofs_with_Structure.html#id2)
Let $m$ and $n$ be integers, and suppose that $m + 3 ≤ 2n -1$ and $n ≤ 5$.
Show that $m ≤ 6$.
-/
example {m n : ℤ} (h1 : m + 3 ≤ 2 * n - 1) (h2 : n ≤ 5) : m ≤ 6 := by
  have h3 : m ≤ 2 * n - 4 := by linarith [h1]
  calc
    m ≤ 2 * n - 4 := h3 -- use h3
    _ ≤ 2 * 5 - 4 := by gcongr -- substitute h2
    _ = 6 := by norm_num -- prove inequality using `norm_num`

/-!
Solution **2.1.2** given in book.
-/
example {m n : ℤ} (h1 : m + 3 ≤ 2 * n - 1) (h2 : n ≤ 5) : m ≤ 6 := by
  have h3 :=
  calc
    m + 3 ≤ 2 * n - 1 := by gcongr
    _ ≤ 2 * 5 - 1 := by gcongr
    _ = 9 := by norm_num
  linarith [h3]

/-!
### [2.1.3](https://hrmacbeth.github.io/math2001/02_Proofs_with_Structure.html#id3)

Let $r$ and $s$ be rational numbers, and suppose that $s + 3 \ge r$ and $s + r \le 3$. Show that $r \le 3$.

Here we introduce the following intermediate hypotheses:

$$h3: r ≤ 3 - s$$

-/
example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 := by
  have
    h3 : r ≤ 3 - s := by linarith [h2] -- substitute h2
  calc
    r = (r + r) / 2 := by ring
    _ <= (3 + s + 3 - s) / 2 := by linarith [h2, h3]
    _ = 3 := by ring

/-!
### [2.1.4](https://hrmacbeth.github.io/math2001/02_Proofs_with_Structure.html#id4)

Let $t$ be a real number, and suppose that $t^2 = 3t$ and $t ≥ 1$. Show that in fact $t ≥ 2$.
-/
example {t : ℝ} (h1 : t ^ 2 = 3 * t) (h2 : t ≥ 1) : t ≥ 2 := by
  have h3 : t * t = t * 3 := by
    calc
      t * t = t ^ 2 := by ring
      _ = 3 * t := h1
      _ = t * 3 := by ring
  have ht : t ≠ 0 := by linarith [h2]
  have h4 : t = 3 := mul_left_cancel₀ ht h3
  linarith [h4]

/-!
Simplified solution to **2.1.4**.
-/
example {t : ℝ} (h1 : t ^ 2 = 3 * t) (h2 : t ≥ 1) : t ≥ 2 := by
  nlinarith

/-!
Alternative that shows exact value of $t : t = 3$.
-/
example {t : ℝ} (h1 : t ^ 2 = 3 * t) (h2 : t ≥ 1) : t = 3 := by
  have h3 : t * t = t * 3 := by
    calc
      t * t = t ^ 2 := by ring
      _ = 3 * t := h1
      _ = t * 3 := by ring
  have ht : t ≠ 0 := by linarith [h2]
  exact mul_left_cancel₀ ht h3

/-!
Polymorphic Point.
-/
structure Point (α : Type) where
  x : α
  y : α
deriving Repr

/-!
Derive `ToString` instance for `Point`.
-/
instance [ToString α] : ToString (Point α) where
  toString p := s!"({p.x}, {p.y})"

#check Point

/--
Create a point using Natural numbers.
-/
def origin : Point ℕ := { x := 0, y := 0 }

#check origin
#eval IO.println s!"origin: {origin}"

/--
Lists functions.

**Note**

If you know a list is non-empty but haven't formally proven it to Lean, use the
`!` suffix (e.g., `tail!`, `head!`). This extracts the value directly but will
**panic (crash)** your program if the list actually turns out to be empty.

If you are not sure whether a list is empty, use the `?` suffix (e.g., `tail?`,
`head?`), which safely returns an `Option`.
-/
def primes : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]

#eval IO.println s!"primes: {primes}"
#eval IO.println s!"primes.tail: {primes.tail}"
#eval IO.println s!"primes.head!: {primes.head!}"
#eval IO.println s!"primes.getLast!: {primes.getLast!}"
#eval IO.println s!"primes.filter (λ x => x < 11): {primes.filter (λ x => x < 11)}"

/--
Sum a list of numbers.

In Lean, (· + ·) is shorthand for an anonymous function with two placeholders:

```lean
(· + ·) = fun x y => x + y
```

This is equivalent to the Haskell's `(+)` operator.
-/
def sumList (l : List ℕ) : ℕ :=
  l.foldl (· + ·) 0

#eval IO.println s!"sumList primes: {sumList primes}" -- 129
#eval IO.println s!"sumList primes == primes.sum: {sumList primes == primes.sum}"

/-!
Length of a (polymorphic) list.
-/
def lengthList {α : Type} (l : List α) : ℕ :=
  l.foldl (fun acc _ => acc + 1) 0

#eval IO.println s!"lengthList primes: {lengthList primes}" -- 10
#eval IO.println s!"lengthList primes == List.length primes: {lengthList primes == List.length primes}"
#eval IO.println s!"lengthList primes == primes.length: {lengthList primes == primes.length}"

#eval IO.println s!"primes.slice: {primes.slice 3 7}" -- [7, 11, 13, 17]
#eval IO.println s!"primes.slice: {primes.slice 10 11}"

end Structure
