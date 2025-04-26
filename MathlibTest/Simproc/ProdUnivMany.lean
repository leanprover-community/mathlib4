import Mathlib.Data.Fin.Tuple.Reflection

example (f : Fin 10 → ℤ) :
    ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 * f 7 * f 8 * f 9 := by
  simp only [Fin.prod_univ_many]

example (f : Fin 10 → ℤ) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  simp only [Fin.sum_univ_many]
