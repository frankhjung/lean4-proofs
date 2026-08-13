import Mathlib.Data.Real.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Existence

#eval IO.println "Existence.Existence"

/-!
Examples from [MoP](https://hrmacbeth.github.io/math2001/index.html), chapter [
2.5 Existence Proofs](https://hrmacbeth.github.io/math2001/02_Proofs_with_Structure.html#existence-proofs)

Examples of using existentials (∃) in Lean.
-/

/-!
[2.5.1](https://hrmacbeth.github.io/math2001/02_Proofs_with_Structure.html#id29)

Let $a$ be a rational number, and suppose that there exists a rational number
$b$, such that $a = b^2 + 1$. Show that $a > 1$.
-/
#count_heartbeats in
example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a ≥ 1 := by
  obtain ⟨b, hb⟩ := h                     -- extract the existential
  have hb2 : b ^ 2 ≥ 0 := by nlinarith    -- prove hb2
  calc
    a = b^2 + 1 := hb                     -- use hb
    _ ≥ 0 + 1 := by gcongr                -- use hb2
    _ = 1 := by norm_num                  -- prove inequality using `norm_num`

/-!
Simplified version of **2.5.1**.
-/
#count_heartbeats in
example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a ≥ 1 := by
  obtain ⟨b, hb⟩ := h                     -- extract the existential
  nlinarith                               -- prove inequality using `nlinarith`

/-!
Define odd numbers.
-/
def MyOdd (a : ℤ) : Prop := ∃ k, a = 2 * k + 1

/-!
Show 5 is odd.

The `use` tactic is smart enough to unfold definitions.

You can't use the `decide` tactic here as `MyOdd` is not in Mathlib.
-/
example : MyOdd (5 : ℤ) := by
  -- unfold MyOdd                            -- get k from definition
  use 2                                   -- set k = 2
  norm_num                                -- prove equality

/-!
Define even numbers.
-/
def MyEven (a : ℤ) : Prop := ∃ k, a = 2 * k

/-!
Show 4 is even.

The `use` tactic is smart enough to unfold definitions.
-/
example : MyEven (4 : ℤ) := by
  -- unfold MyEven                           -- get k from definition
  use 2                                   -- set k = 2
  norm_num                                -- prove equality

end Existence
