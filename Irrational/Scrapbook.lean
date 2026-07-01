import Mathlib

namespace Scrapbook

/-!
# Scrapbook

A work scrapbook while learning [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean)

-/

/-! Function $f (x) = 3x$ -/
def f (x : ℕ) := 3 * x

-- #eval f 1 = 3

/-!
  Simple test of function $f (1) = 3$
-/
theorem f1_eq_3 : f 1 = 3 := rfl

-- #check f1_eq_3

/-!
  **Examples:** An *example* is an anonymous definition that is elaborated and then discarded.
-/

/-!
  Even numbers: $m × even$ is still even.
-/
example : ∀ m n : ℕ, Even n → Even (m * n) :=
  fun m n ⟨k, (hk : n = k + k)⟩ ↦
  have hmn : m * n = m * k + m * k := by rw [hk, mul_add]
  show ∃ l, m * n = l + l from ⟨_, hmn⟩

/-!
  Same proof compressed to one line.
  Here, `mul_add` is a standard theorem for distributing multiplication over
  addition. It states that for elements `a`, `b`, and `c`,
  `\(a × (b + c) = (a × b) + (a × c)`.
  It acts as a shortcut for expanding brackets.
-/
example : ∀ m n : ℕ, Even n → Even (m * n) :=
  fun m n ⟨k, hk⟩ ↦ ⟨m * k, by rw [hk, mul_add]⟩

/-!
  We can also use tactics to prove this.
-/
example : ∀ m n : ℕ, Even n → Even (m * n) := by
  -- Say `m` and `n` are natural numbers,
  -- and `Even n` implies `n = k + k` for some `k` in `ℕ`
  rintro m n ⟨k, hk⟩
  -- We need to show `m × n` is twice a natural number
  -- Let's show it's twice `m × k`
  use m * k
  -- Substitute `n`: `m × n` becomes
  -- `m × (2 × k)` using `hk`
  rw [hk]
  -- and now it is obvious:
  -- `m × (2 × k) = 2 × (m × k)`
  ring

/-!
  Same proof compressed to one line using `ring` tactic.
  Which is just the above one line proof compressed with  semicolons.

  `rintro` is a shorthand for the tactics `intros` and `rcases`.
  Where:
  - `intros` repeatedly applies `intro` to introduce hypotheses
  - `rcases` performs `cases` recursively
  - `cases` splits goal into each case

  Note: semicolons can be used to separate tactics in a proof
-/
example : ∀ m n : ℕ, Even n → Even (m * n) := by
  rintro m n ⟨k, hk⟩; use m * k; rw [hk]; ring

/-!
  Lean has a simplifier tactic that can prove this automatically:
  Where:
  - `simp` tactic uses lemmas and hypotheses to simplify the main
     goal target or non-dependent hypotheses
  - `parity_simps` (Mathlib) is a specialized collection of
     mathematical theorems used with the `simp` tactic
-/
example : ∀ m n : ℕ, Even n → Even (m * n) := by
  intros; simp [*, parity_simps]

example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm a]
  rw [mul_comm b]
  rw [mul_comm c]
  rw [mul_assoc b]

example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm a (b * c)]
  rw [mul_assoc b c a]

example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm]
  rw [mul_assoc]

end Scrapbook
