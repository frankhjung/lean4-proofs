import Mathlib

namespace Irrational

/-!
# Proof that √2 is irrational.

## Explaining the Lean 4 Proof
-/

theorem sqrt_two_irrational (a b : ℕ) (h_coprime : a.Coprime b) : a ^ 2 ≠ 2 * b ^ 2 := by
  intro heq
  have ha : 2 ∣ a := Nat.prime_two.dvd_of_dvd_pow ⟨b ^ 2, heq⟩
  obtain ⟨k, rfl⟩ := ha
  have hb_sq : 2 ∣ b ^ 2 := ⟨k ^ 2, by nlinarith⟩
  have hb : 2 ∣ b := Nat.prime_two.dvd_of_dvd_pow hb_sq
  exact absurd (h_coprime.gcd_eq_one ▸ Nat.dvd_gcd ⟨k, rfl⟩ hb) (by decide)

/-! Checks. -/
-- #check sqrt_two_irrational

end Irrational
