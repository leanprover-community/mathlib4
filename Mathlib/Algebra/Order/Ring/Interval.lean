
/-! # Intervals of integers in strict ordered rings

These statements could perhaps be generalized, or there could be other variations provided (e.g.,
for `ℕ` instead of `ℤ`, or a version for locally finite `SuccOrder`s with strictly monotone
functions), but for now these are the ones that have found utility in practice (e.g., for lemmas
about `Real.Angle`).
-/

public section

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Let `k : ℤ`. If its multiple of `r > 0` in a strict ordered ring lies strictly between
multiples `r * (m - 1)` and `r * (n + 1)`, then `m ≤ k ≤ n`. -/
lemma IsStrictOrderedRing.int_mem_Icc_of_mul_mem_Ioo
    {r : R} (hr : 0 < r) {k m n : ℤ} (h : r * k ∈ Set.Ioo (r * (m - 1 : ℤ)) (r * (n + 1 : ℤ))) :
    k ∈ Finset.Icc m n := by
  simp only [Set.mem_Ioo, mul_lt_mul_iff_right₀ hr, Int.cast_lt] at h
  grind [Int.lt_iff_add_one_le]

/-- Let `k : ℤ`. If its multiple of `r > 0` in a strict ordered ring lies strictly between
the preceding and succeeding multiples `r * (m - 1)` and `r * (m + 1)`, then `k = m`. -/
lemma IsStrictOrderedRing.int_eq_of_mul_mem_Ioo
    {r : R} (hr : 0 < r) {k m : ℤ} (h : r * k ∈ Set.Ioo (r * (m - 1 : ℤ)) (r * (m + 1 : ℤ))) :
    k = m := by
  simpa using int_mem_Icc_of_mul_mem_Ioo hr h
