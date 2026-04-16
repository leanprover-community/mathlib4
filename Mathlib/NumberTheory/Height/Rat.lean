/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
import Mathlib.NumberTheory.Height.NumberField

/-!
# Heights of rational numbers

We compute the multiplicative and logarithmic Weil height of a natural number
cast to `ℚ`. Since `ℚ` has a unique infinite place (the usual absolute value)
and every finite place satisfies `v n ≤ 1` for `n : ℕ`, the height simplifies to
`mulHeight₁ (n : ℚ) = n` and `logHeight₁ (n : ℚ) = Real.log n` for `1 ≤ n`.
-/

open NumberField Height

namespace Rat

/-- The multiplicative height of a positive natural number cast to `ℚ` equals `n`. -/
theorem mulHeight₁_natCast (n : ℕ) (hn : 1 ≤ n) :
    mulHeight₁ (n : ℚ) = n := by
  rw [NumberField.mulHeight₁_eq]
  have hfin : ∀ v : FinitePlace ℚ, max (v (n : ℚ)) 1 = 1 := fun v ↦
    max_eq_right (IsNonarchimedean.apply_natCast_le_one_of_isNonarchimedean
      (NonarchimedeanHomClass.map_add_le_max v))
  rw [finprod_eq_one_of_forall_eq_one hfin, mul_one, Fintype.prod_unique]
  conv_lhs => rw [show (default : InfinitePlace ℚ) = infinitePlace from Subsingleton.elim _ _]
  simp [InfinitePlace.mult, if_pos isReal_infinitePlace,
    max_eq_left (by exact_mod_cast hn : (1 : ℝ) ≤ n)]

/-- The logarithmic height of a positive natural number cast to `ℚ` equals `log n`. -/
theorem logHeight₁_natCast (n : ℕ) (hn : 1 ≤ n) :
    logHeight₁ (n : ℚ) = Real.log n := by
  simp [logHeight₁_eq_log_mulHeight₁, mulHeight₁_natCast n hn]

end Rat
