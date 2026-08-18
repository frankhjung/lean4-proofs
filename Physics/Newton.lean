import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.ZPow

namespace Physics

-- Print a small marker when the file is elaborated.
#eval IO.println "Physics.Newton"

/-! # Newton's Law of Motion -/

/-!
State Newton's second law in the special case where zero force implies zero acceleration.
-/

/-!
If force equals mass times acceleration, and mass is positive, then zero force forces zero acceleration.
-/
theorem zero_force_implies_zero_acceleration {F m a : ℝ}
  -- Hypothesis: force is mass times acceleration.
  (h₁ : F = m * a)
  -- Hypothesis: mass is strictly positive.
  (h₂ : m > 0) :
  -- Conclusion: if force is zero, then acceleration is zero.
  F = 0 → a = 0 := by
  -- Introduce the assumption that force is zero.
  intro hf
  -- Rewrite the force equation to turn the goal into `m * a = 0`.
  have hz : m * a = 0 := by rw [← h₁, hf]
  -- Use positivity of `m` to cancel the nonzero factor and deduce `a = 0`.
  simp [h₂.ne'] at hz
  -- Finish with the simplified conclusion.
  exact hz

/-!
Simplified version of the previous theorem using
`ne_of_gt`, `mul_eq_zero` and `resolve_left`.
-/
theorem zero_force_zero_acceleration {F m a : ℝ}
  -- The force is given by mass times acceleration.
  (h₁ : F = m * a)
  -- The mass is strictly positive.
  (h₂ : m > 0) :
  -- If force is zero, then acceleration is zero.
  F = 0 → a = 0 := by
  -- Assume the force is zero.
  intro hf
  -- A positive real number cannot be zero.
  have hm : m ≠ 0 := ne_of_gt h₂
  -- Rewrite the force equation using the fact that `F = 0`.
  have hma : m * a = 0 := by rw [← h₁, hf]
  -- Split the product equation and discard the impossible `m = 0` branch.
  exact (mul_eq_zero.mp hma).resolve_left hm

/-!
Writing proofs about functions defined outside.
-/
variable (k x x_eq : ℝ)
noncomputable def force (x : ℝ) : ℝ := -k * (x - x_eq)
noncomputable def energy (x : ℝ) : ℝ := (k/2) * (x - x_eq)^2

#check force
#check energy

/-!
Theorem: Force is the negative derivative of energy.  This is a simple consequence of the chain rule and the power rule.  The proof is a bit long, but it is straightforward.
-/
#count_heartbeats in
theorem force_derivative_energy (x : ℝ) :
  deriv (energy k x_eq) x = - force k x_eq x := by
  unfold energy force
  simp only [deriv_const_mul_field', deriv_fun_pow, deriv_fun_sub,
    deriv_id'', deriv_const', differentiableAt_fun_id, differentiableAt_const,
    DifferentiableAt.fun_sub]
  ring

/-!
**Simplified**:  The above can be simplified to just. But this is much less
efficient:

- theorem: Used 33 heartbeats
- example: Used 1616
-/
#count_heartbeats in
example (x : ℝ) :
  deriv (energy k x_eq) x = - force k x_eq x := by
  unfold energy force
  simp
  ring

end Physics
