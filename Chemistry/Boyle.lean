import Mathlib.Data.Real.Basic

namespace Chemistry

#eval IO.println "Chemistry.Boyle"

/-! Define variables to be used in Boyle's Law. -/
variable (pressure : ℕ → ℝ)
variable (volume : ℕ → ℝ)

/--
Defines Boyle's Law as the existence of a constant product `k` across all
states.
-/
def Boyles_Law : Prop := ∃ (k : ℝ), ∀ n, pressure n * volume n = k

/--
Defines Boyle's Law as the pairwise equality of pressure-volume products across
any two states.
-/
def Boyles_Law_2 : Prop :=
  ∀ n m, pressure n * volume n = pressure m * volume m

/--
Proves that the constant-product formulation of Boyle's Law (`Boyles_Law`)
implies the pairwise-equality formulation (`Boyles_Law_2`).

**Method**: Extracts the existence witness `k` from `Boyles_Law` and shows
that for any two states `n` and `m`, both `pressure n * volume n` and
`pressure m * volume m` equal `k`.
-/
theorem boyles_law_relation:
  Boyles_Law pressure volume → Boyles_Law_2 pressure volume := by
  -- Assume the hypothesis: there is a constant `k` such that every
  -- `pressure n * volume n` equals `k`.
  intro h
  -- Unfold the definition of `Boyles_Law` and expose the witness `k`.
  dsimp [Boyles_Law] at h
  -- Extract the constant `k` and the fact that each product equals it.
  rcases h with ⟨k, hk⟩
  -- To prove the second formulation, we show any two values are equal.
  intro n m
  -- Both `pressure n * volume n` and `pressure m * volume m` equal the
  -- same constant `k`.
  calc
    pressure n * volume n = k := hk n
    _ = pressure m * volume m := by
      -- `hk m` says `pressure m * volume m = k`; reversing it gives the goal.
      symm
      exact hk m

/--
Proves that the pairwise-equality formulation of Boyle's Law (`Boyles_Law_2`)
implies the constant-product formulation (`Boyles_Law`).

**Method**: Constructs the witness constant `k` as `pressure n₀ * volume n₀`
and applies pairwise equality between state `n` and state `n₀`.
-/
theorem boyles_law_relation_rev (n₀ : ℕ := 0) :
  Boyles_Law_2 pressure volume → Boyles_Law pressure volume := by
  -- Assume `Boyles_Law_2`: any two state products are equal.
  intro h
  apply Exists.intro (pressure n₀ * volume n₀)
  -- For any state `n`, `pressure n * volume n = pressure n₀ * volume n₀`.
  intro n
  exact h n n₀

/--
Proves the logical equivalence between the constant-product formulation
(`Boyles_Law`) and the pairwise-equality formulation (`Boyles_Law_2`).

**Method**: Combines `boyles_law_relation` (forward direction) and
`boyles_law_relation_rev` (reverse direction) into a logical bi-implication.
-/
theorem boyles_law_iff (n₀ : ℕ := 0) :
  Boyles_Law pressure volume ↔ Boyles_Law_2 pressure volume :=
  ⟨boyles_law_relation pressure volume,
   boyles_law_relation_rev pressure volume n₀⟩

/-! Prove Boyle's Law

Prove that an ideal gas follows Boyle's Law:

$$ PV = nRT $$

When $T_1 = T_2$ and $n_1 = n_2$, then $P_1V_1 = P_2V_2$.

-/

/--
Proves Boyle's Law for an ideal gas governed by \(PV = nRT\).

Shows that if temperature and molar amount remain constant (\(T_1 = T_2\) and
\(n_1 = n_2\)), then \(P_1 V_1 = P_2 V_2\).

**Method**: Substitutes the temperature and molar amount equalities into the
first ideal gas state equation and rewrites with the second state equation.
-/
theorem Boyle {P1 P2 V1 V2 T1 T2 n1 n2 R : ℝ }
  -- Assumptions
  (h1: P1*V1 = n1*R*T1)
  (h2: P2*V2 = n2*R*T2)
  (h3: T1 = T2)
  (h4: n1 = n2) :
  -- Conjecture
  (P1*V1 = P2*V2) :=
  -- Proof
  by
    rw [h3] at h1
    rw [h4] at h1
    rw [← h2] at h1
    exact h1

end Chemistry
