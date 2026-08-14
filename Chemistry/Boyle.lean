import Mathlib.Data.Real.Basic

namespace Chemistry

#eval IO.println "Chemistry.Boyle"

/-! Prove Boyle's law

Prove that an ideal gas follows Boyle's Law:

$$ PV = nRT $$

When $T_1 = T_2$ and $n_1 = n_2$, then $P_1V_1 = P_2V_2$.

-/

-- Variables
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

-- This proof can also be simplified to:
-- by [h1 h2 h3 h4]
-- by (simp_all using h1 h2 h3 h4)

end Chemistry
