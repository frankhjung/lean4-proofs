import Mathlib

/-!

# Proof that log₃(2) is irrational.

The following Lean proof is based on the following:

We proceed by contradiction.

Assume $\log_{2}(3)$ is rational. Then there exist positive integers $a$ and $b$
such that:

$$\log_{2}(3) = \frac{a}{b}$$

By the definition of [logarithms](https://mathinsight.org/logarithm_basics), we
can rewrite this as an exponent:

$$2^{a/b} = 3$$

Raise both sides to the power of $b$:

$$2^{a} = 3^{b}$$

Because $a$ is a positive integer, $2^{a}$ is $2$ multiplied by itself $a$
times, meaning the left side is an even number.

Because $b$ is a positive integer, $3^{b}$ is $3$ multiplied by itself $b$
times, meaning the right side is an odd number.

An even number cannot equal an odd number. We have reached a contradiction.

Therefore, $\log_{2}(3)$ is irrational. $\square$

## Explaining the Lean 4 Proof

-/

theorem log2_3_irrational (a b : ℕ) (ha : a > 0) (_ : b > 0) : 2^a ≠ 3^b := by
  -- Assume the opposite: 2^a = 3^b
  intro h

  -- Step 1: Because a is positive, a ≠ 0,
  -- meaning it can be written as k + 1
  have ha_ne : a ≠ 0 := by omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha_ne

  -- Because 2^a = 2^(k+1) = 2 * 2^k,
  -- the left side must be even (divisible by 2)
  have h_left_even : 2 ∣ 2^(k + 1) := ⟨2^k, by ring⟩

  -- Step 2: Since 3 is odd, any power of 3 is also odd (not divisible by 2)
  have h_right_odd : ¬ 2 ∣ 3^b := by
    intro h_div
    have h_2_dvd_3 : 2 ∣ 3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h_div
    revert h_2_dvd_3
    decide

  -- Step 3: By substitution, since 2^a = 3^b, implies 3^b must be even
  have h_right_even : 2 ∣ 3^b := by
    rw [← h]
    exact h_left_even

  -- Step 4: Contradiction!
  -- It is impossible for left to be even and right to be odd.
  exact h_right_odd h_right_even
