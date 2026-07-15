import Mathlib

namespace Irrational

/-!

# Proof that log₂(3) is irrational.

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

-/

theorem log2_3_irrational (a b : ℕ) (ha : a > 0) (_ : b > 0) : 2^a ≠ 3^b := by
  -- Assume the opposite: 2^a = 3^b
  intro h

  -- Step 1: Because a is positive, a ≠ 0,
  -- meaning it can be written as k + 1
  have ha_ne : a ≠ 0 := by omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero ha_ne

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

-- #check log2_3_irrational

/-!

# Proof that log₂(n) is irrational, where n % 2 = 1 and n > 0.

This is a generalised result showing that $log_{2}{(2c+1)}$ is irrational, where
$c$ is a positive integer.
-/
theorem log2_odd_irrational (a b c: ℕ) (ha : a > 0) (_ : b > 0) (hc: Odd c) : 2^a ≠ c^b := by
  -- Assume the opposite: 2^a = c^b for some c that is odd and c > 1
  intro h

  -- Step 1: Because a is positive, a ≠ 0, meaning it can be written as k + 1
  have ha_ne : a ≠ 0 := by omega
  -- Extract the predecessor k such that a = k + 1, replacing a in the context
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero ha_ne

  -- Because 2^a = 2^(k+1) = 2 * 2^k,
  -- the left side must be even (divisible by 2). The witness is 2^k.
  have h_left_even : 2 ∣ 2^(k + 1) := ⟨2^k, by ring⟩

  -- Step 2: Since c is odd, any power of c is also odd (not divisible by 2)
  have h_right_odd : ¬ 2 ∣ c^b := by
    -- Assume the opposite: 2 divides c^b
    intro h_div
    -- Since 2 is prime, if it divides a power c^b, it must divide the base c
    have h_2_dvd_c : 2 ∣ c := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h_div
    -- By definition of divisibility, c = 2 * m for some integer m
    obtain ⟨m, rfl⟩ := h_2_dvd_c
    -- By definition of oddness, c = 2 * n + 1 for some integer n
    obtain ⟨n, hn⟩ := hc
    -- Omega finds the contradiction: 2*m = 2*n + 1 has no integer solutions
    omega

  -- Step 3: By substitution, since 2^a = c^b, c^b must be even
  have h_right_even : 2 ∣ c^b := by
    -- Rewrite the goal using the assumption 2^a = c^b (where a is k + 1)
    rw [← h]
    -- We already proved that 2^(k + 1) is even (Step 1)
    exact h_left_even

  -- Step 4: Contradiction!
  -- It is impossible for c^b to be both even and odd simultaneously.
  exact h_right_odd h_right_even

-- #check log2_odd_irrational

/-!
Next: a generalised result showing that $log_{n}{m}$ is irrational
where $n > 1$ and $m$ is not divisible by $n$.
-/
-- theorem log_n_m_irrational (a b n m : ℕ) (ha : a > 0) (_ : b > 0) (hn : n > 1) (hm : m % n ≠ 0) : n^a ≠ m^b := by
--   -- Assume the opposite: n^a = m^b for some n > 1 and m not divisible by n
--   intro h

end Irrational
