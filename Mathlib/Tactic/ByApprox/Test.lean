import Mathlib.Data.Real.Basic

private lemma mul_lower_bound (a b : ℝ) (a_l a_u b_l b_u : ℚ)
    (pa_l : a_l ≤ a) (pa_u : a_u ≥ a) (pb_l : b_l ≤ b) (pb_u : b_u ≥ b)
    (lb : ℚ) (hll : lb ≤ a_l * b_l) (hlu : lb ≤ a_l * b_u)
    (hul : lb ≤ a_u * b_l) (huu : lb ≤ a_u * b_u): a * b ≥ lb := by
  by_cases a_sign : a ≥ 0
  . trans a * b_l
    exact mul_le_mul_of_nonneg_left pb_l a_sign
    by_cases b_l_sign : b_l ≥ 0
    . trans a_l * b_l
      exact mul_le_mul_of_nonneg_right pa_l (Rat.cast_nonneg.mpr b_l_sign)
      rw [← Rat.cast_mul]
      apply Rat.cast_le.mpr hll
    . trans a_u * b_l
      simp at b_l_sign
      exact mul_le_mul_of_nonpos_right pa_u (Rat.cast_nonpos.mpr b_l_sign.le)
      rw [← Rat.cast_mul]
      apply Rat.cast_le.mpr hul
  . simp at a_sign
    trans a * b_u
    exact mul_le_mul_of_nonpos_left pb_u a_sign.le
    by_cases b_u_sign : b_u ≥ 0
    . trans a_l * b_u
      exact mul_le_mul_of_nonneg_right pa_l (Rat.cast_nonneg.mpr b_u_sign)
      rw [← Rat.cast_mul]
      apply Rat.cast_le.mpr hlu
    . trans a_u * b_u
      simp at b_u_sign
      exact mul_le_mul_of_nonpos_right pa_u (Rat.cast_nonpos.mpr b_u_sign.le)
      rw [← Rat.cast_mul]
      apply Rat.cast_le.mpr huu

private lemma mul_upper_bound (a b : ℝ) (a_l a_u b_l b_u : ℚ)
    (pa_l : a_l ≤ a) (pa_u : a_u ≥ a) (pb_l : b_l ≤ b) (pb_u : b_u ≥ b)
    (ub : ℚ) (hll : ub ≥ a_l * b_l) (hlu : ub ≥ a_l * b_u)
    (hul : ub ≥ a_u * b_l) (huu : ub ≥ a_u * b_u): a * b ≤ ub := by
  suffices : a * (- b) ≥ ((- ub) : ℚ)
  . simp at this
    exact this
  apply mul_lower_bound a (-b) a_l a_u (-b_u) (-b_l) pa_l pa_u
  repeat { simp ; assumption }
