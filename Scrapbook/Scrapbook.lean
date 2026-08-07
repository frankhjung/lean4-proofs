import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Util.CountHeartbeats

namespace Scrapbook

/-!
# Scrapbook

A work scrapbook while learning [Mathematics in
Lean](https://leanprover-community.github.io/mathematics_in_lean)

-/

/-! Function $f (x) = 3x$ -/
def f (x : ℕ) := 3 * x

/-! Evaluate function $f$ at $x = 1$. -/
#eval f 1 = 3
-- true

/-! Equivalent to $f$ above. -/
#check fun (x : ℕ) => 3 * x
-- fun x => 3 * x : ℕ → ℕ

#check λ (x : ℕ) => 3 * x
-- fun x => 3 * x : ℕ → ℕ

#eval (λ x : ℕ => 3 * x) 12
-- 36

/-! Simple test of function $f (1) = 3$ -/
theorem f1_eq_3 : f 1 = 3 := rfl

#check f1_eq_3
-- f1_eq_3 : f 1 = 3

/-!
## Example

An *example* is an anonymous definition that is elaborated and then discarded.
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
addition. It states that for elements `a`, `b`, and `c`, `\(a × (b + c) = (a ×
b) + (a × c)`. It acts as a shortcut for expanding brackets.

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
Same proof compressed to one line using `ring` tactic. Which is just the above
one line proof compressed with  semicolons.

`rintro` is a shorthand for the tactics `intros` and `rcases`.

Where:
- `intros` repeatedly applies `intro` to introduce hypotheses
- `rcases` performs `cases` recursively
- `cases` splits goal into each case

**Notes**

- Semicolons can be used to separate tactics in a proof

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

/-! Ring example -/
example (R : Type*) [CommRing R] (x y : R) : (x + y)^3 = x^3 + 3*x^2*y + 3*x*y^2 + y^3 := by
  ring

/-!
## And Commutative

This example is from the introduction of [Theorem Proving in
Lean](https://lean-lang.org/theorem_proving_in_lean4/Introduction/#Intro)

It declares a theorem named `and_commutative` stating that for any propositions
`p` and `q`, `p ∧ q` implies `q ∧ p`. The `:=` begins the proof.

-/
theorem and_commutative (p q : Prop) : p ∧ q → q ∧ p :=
  -- Assumes the premise `p ∧ q` is true and binds its proof to the name `hpq`.
  -- Proving an implication `A → B` in Lean is done by providing a function
  -- that takes a proof of `A` and returns a proof of `B`.
  fun hpq : p ∧ q =>
  -- Extracts the proof of the left side (`p`) from the conjunction `hpq`
  -- using `And.left`, and binds it to the name `hp`.
  have hp : p := And.left hpq
  -- Extracts the proof of the right side (`q`) from the conjunction `hpq`
  -- using `And.right`, and binds it to the name `hq`.
  have hq : q := And.right hpq
  -- Constructs the final goal `q ∧ p` using `And.intro`, which takes a proof
  -- of the left side (`hq`) and a proof of the right side (`hp`) to form a
  -- proof of the conjunction. The `show ... from` syntax explicitly states
  -- the proposition being proved for clarity.
  show q ∧ p from And.intro hq hp

/-! ## Solving Word Problems -/

/-!
### Problem 1

The following is an example of how to solve a word problem.

A plane flies 450km with the wind in 3 hours.

Flying back against the wind, the plance takes 5 hours to make the trip.

Prove that the plane's speed in still air is 120km/h.

We know that $d = v × t$.

Let $x$ = plane's speed and $y$ = wind's speed.

For the first trip we have:  $h1: 450 = 3 × (x + y)$

For the second trip we have: $h2: 450 = 5 × (x - y)$

Simplify to:
- $h1: 150 = x + y$
- $h2: 90 = x - y$

What we want is to calculate the planes wind speed in still air ($x$).

Answer:
- $x = 120$
- $y = 150-120 = 30$

-/
example {x y : ℝ}
  (h1: x + y = 150)
  (h2: x - y = 90)
  : (x = 120 ∧ y = 30) := by
  have h_x : x = 120 :=
    calc
      x = ((x + y) + (x - y)) / 2 := by ring -- algebraic identity
      _ = (150 + 90) / 2 := by rw [h1, h2] -- rewrites `h1` and `h2` to LHS
      _ = 120 := by norm_num -- better than by ring

  have h_y : y = 30 :=
    calc
      y = (x + y) - x := by ring
      _ = 150 - x := by rw [h1]
      _ = 150 - 120 := by rw [h_x]
      _ = 30 := by norm_num

  exact ⟨h_x, h_y⟩

/-!
### Problem 2

A resistor has a resistance of 4 ohms and a current of 3 Amps flows through it.
Prove the voltage across the resistor is 12 Volts.

$$v = I × R$$

Where:
- $v$ = Voltage (in Volts)
- $I$ = Current (in Amps)
- $R$ = Resistance (in Ohms)

-/
example {v I R : ℝ}
  (h1 : I = 3)
  (h2 : R = 4)
  (h3 : v = I * R) : v = 12 :=
  calc
    -- step-by-step
    -- v = I * R := by rw [h3]
    -- _ = 3 * R := by rw [h1]
    -- _ = 3 * 4 := by rw [h2]
    -- _ = 12 := by norm_num
    v = 12 := by
      -- compressed form
      rw [h3, h1, h2]
      norm_num

/-!
### Problem 3

Given:
- $a - b = 4$
- $a × b = 1$

Prove that $(a + b)^2 = 20$

We know that $(a + b)^2 = (a - b)^2 + 4 × (a × b)$

From [The Mechanics of Proof
(MoP)](https://hrmacbeth.github.io/math2001/index.html), problem
[1.2.1](https://hrmacbeth.github.io/math2001/01_Proofs_by_Calculation.html#id11)

-/
example {a b : ℚ}
  (h1 : a - b = 4)
  (h2 : a * b = 1)
  : (a + b) ^ 2 = 20 :=
  calc
    (a + b) ^ 2 =  (a - b)^2 + 4 * (a * b) := by ring -- algebraic rearrangement
    _ = 4^2 + 4 * 1 := by rw [h1, h2] -- substitute hypothesis h1, h2
    _ = 20 := by norm_num -- numerical calculation

/-!
### Problem 4

From [MoP](https://hrmacbeth.github.io/math2001/index.html), problem
[1.2.4](https://hrmacbeth.github.io/math2001/01_Proofs_by_Calculation.html#id15)

-/
example {a b c d e f : ℤ}
  (h1 : a * d = b * c)
  (h2 : c * f = d * e)
  : d * (a * f - b * e) = 0 :=
  calc
    d * (a * f - b * e) = (a * d) * f - b * (d * e) := by ring
    _ = (b * c) * f - b * (c * f) := by rw [h1, h2]
    _ = 0 := by ring

/-!
### Problem 5

A toy mouse changes speed from 2 m/s to 0 m/s in the span of 2 seconds. It's
mass is estimated to be around 0.1 kg. The toy can only handle 2 Netwons of
force (otherwise it breaks). Prove that the force it experiences in stopping is
below that limit.

-/
example {f v₀ v₁ m t a : ℝ}
  (h1 : v₀ = 2)
  (h2 : v₁ = 0)
  (h3 : m = 0.1)
  (h4 : t = 2)
  (h5 : a = (v₁ - v₀) / t)
  (h6 : f = m * a)
  : f < 2 :=
  calc
    f = m * a := by rw [h6]
    _ = m * ((v₁ - v₀) / t) := by rw [h5]
    _ = 0.1 * ((0 - 2) / 2) := by rw [h3, h2, h1, h4]
    _ < 2 := by linarith -- as the calculation is deterministic

/-!
### Problem 6

From [MoP](https://hrmacbeth.github.io/math2001/index.html), problem
[1.4.1](https://hrmacbeth.github.io/math2001/01_Proofs_by_Calculation.html#id33)

-/
example {x y : ℤ}
  (hx : x + 3 ≤ 2)
  (hy : y + 2 * x ≥ 3)
  : y > 3 :=
  calc
    y = y + 2 * x - 2 * x := by ring
    _ ≥ 3 - 2 * x := by rel [hy] -- rewrite using hy
    _ = 9 - 2 * (x + 3) := by ring
    _ ≥ 9 - 2 * 2 := by rel [hx] -- rewrite using hx
    _ > 3 := by norm_num  -- deterministic calculation
    -- can be more simply done using:
    -- y > 3 := by linarith

/-!
### Problem 7

From [MoP](https://hrmacbeth.github.io/math2001/index.html), problem
[1.4.2](https://hrmacbeth.github.io/math2001/01_Proofs_by_Calculation.html#id35)

-/
example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 :=
  calc
    r = (s + r + r - s) / 2 := by ring -- add term to use both inequalities
    _ ≤ (3 + (s + 3) - s) / 2 := by rel [h2, h1] -- substitute hypothesis
    _ = 3 := by linarith -- deterministic calculation

/-!
### Problem 8.1

From [MoP](https://hrmacbeth.github.io/math2001/index.html), problem
[1.4.3](https://hrmacbeth.github.io/math2001/01_Proofs_by_Calculation.html#id37)

-/
#count_heartbeats in
example {x y : ℝ}
  (h1 : y ≤ x + 5)
  (h2 : x ≤ -2)
  : x + y < 2 :=
  calc
    x + y
    _ ≤ x + (x + 5) := by rel [h1] -- replace y with x + 5
    _ ≤ -2 + (-2 + 5) := by rel [h2] -- replace x with -2, using ≤ 1
    _ < 2 := by norm_num -- deterministic calculation

/-!
### Problem 8.2

From [MoP](https://hrmacbeth.github.io/math2001/index.html), problem
[1.4.3](https://hrmacbeth.github.io/math2001/01_Proofs_by_Calculation.html#id37)

-/
#count_heartbeats in
example {x y : ℝ}
  (h1 : y ≤ x + 5)
  (h2 : x ≤ -2)
  : x + y < 2 :=
  calc
    x + y < 2 := by linarith

/-!
## Floating Point Values

Floating point values are not exact.

See <https://0.30000000000000004.com/>

-/
#eval (0.1 : Float) + (0.2 : Float) == (0.3 : Float)
-- false

#eval (0.1 : Float) + (0.2 : Float)
-- 0.30000000000000004

end Scrapbook
