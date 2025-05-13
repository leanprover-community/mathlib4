import Mathlib

open Real

/- $Example 9. If $a, b \in R^{+}$, prove:
$$
\frac{a^{1994}+b^{1994}}{2} \geqslant\left(\frac{a+b}{2}\right)^{1994} .
$$ -/
theorem my_favorite_theorem (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a ^ (1994 : ℝ) + b ^ (1994 : ℝ)) / 2 ≥ ((a + b) / 2) ^ (1994 : ℝ) := by
  set f : Fin 2 → ℝ := fun x ↦ if x = (0 : Fin 2) then a else b
  have f0 : f 0 = a := by simp [f]
  have f1 : f 1 = b := by simp [f]
  have le : 1 ≤ (1994 : ℝ) := by norm_num
  have nonneg : ∀ i ∈ (⊤ : Finset (Fin 2)), 0 ≤ f i :=
    fun i ↦ by fin_cases i <;> simp [f0, f1, le_of_lt ha, le_of_lt hb]
  have := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (⊤ : Finset (Fin 2)) le nonneg
  simp [f0, f1] at this
  have le3 : (a + b) ^ (1994 : ℝ) * 2 ≤ (a ^ (1994 : ℝ) + b ^ (1994 : ℝ)) * 2 ^ (1994 : ℝ) := by
    calc
    _ ≤ 2 ^ ((1994 : ℝ) - 1) * (a ^ (1994 : ℝ) + b ^ (1994 : ℝ)) * 2 := by
      refine mul_le_mul_of_nonneg this (by norm_num) ?_ (by norm_num)
      exact rpow_nonneg (le_of_lt (Right.add_pos' ha hb)) 1994
    _ = _ := by ring
  have : ((a + b) / 2) ^ (1994 : ℝ) = (a + b) ^ (1994 : ℝ) / 2 ^ (1994 : ℝ) :=
    div_rpow (le_of_lt (Right.add_pos' ha hb)) (by norm_num) 1994
  rw [this]
  have le1 : 0 < (2 : ℝ) ^ (1994 : ℝ) := rpow_pos_of_pos (by norm_num) 1994
  exact (div_le_div_iff₀ le1 (by norm_num)).mpr le3
