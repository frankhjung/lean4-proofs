import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic.Linarith

open Nat

namespace Euclid

#eval IO.println "Existence.Euclid"

/--
**Euclid's Theorem**: There are infinitely many prime numbers:

For every natural number `n`, there exists a prime number `p` such that `n ≤ p`.

-/
theorem exists_infinite_primes (n : ℕ) :
  ∃ p, n ≤ p ∧ Nat.Prime p := by
    -- Choose p to be the smallest prime factor of n! + 1.
    let p := minFac (n ! + 1)
    -- Prove n! + 1 ≠ 1 since n! ≥ 1 and so n! + 1 ≥ 2.
    have h₁ : n ! + 1 ≠ 1 := by linarith [factorial_pos n]
    -- Since n! + 1 ≠ 1, its smallest factor p is prime.
    have h₂ : Nat.Prime p := minFac_prime h₁
    -- Show p ≥ n by contradiction.
    have h₃ : n ≤ p := by
      -- Assume for contradiction that p < n.
      by_contra! h
      -- If p < n, then p divides n! because p ≤ n and p is prime.
      have h₄ : p ∣ n ! := dvd_factorial h₂.pos (le_of_lt h)
      -- By definition of minFac, p divides n! + 1.
      have h₅ : p ∣ n ! + 1 := minFac_dvd (n ! + 1)
      -- Since p divides both n! and n! + 1, p divides their difference, 1.
      have h₆ : p ∣ 1 := (Nat.dvd_add_right h₄).mp h₅
      -- But no prime number can divide 1, giving a contradiction.
      exact h₂.not_dvd_one h₆
    -- Provide p as the witness along with proofs of n ≤ p and Nat.Prime p.
    exact ⟨p, h₃, h₂⟩

#eval Nat.minFac (10 ! + 1)

end Euclid
