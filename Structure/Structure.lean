import Mathlib.Data.Real.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
-- import Plausible

namespace Structure

/-!
# Maths: Proofs with Structure

Examples from [MoP](https://hrmacbeth.github.io/math2001/index.html), [Chapter
2 Proofs with
Structure](https://hrmacbeth.github.io/math2001/02_Proofs_with_Structure.html)

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
## [2. 1 Intermediate Steps](https://hrmacbeth.github.io/math2001/02_Proofs_with_Structure.html#intermediate-steps)

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
    _ ≤ ((s + 3) + (3 - s)) / 2 := by rel [h1, hs]
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
    y ^ 2 + 1 ≥ 0 + 1 := by rel [hy] -- substitute hy
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

end Structure
