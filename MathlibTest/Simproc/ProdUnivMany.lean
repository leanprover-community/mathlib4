import Mathlib.Data.Fin.Tuple.Reflection

@[to_additive]
lemma prod_test (R : Type) [CommMonoid R] (f : Fin 10 → R) :
    ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 * f 7 * f 8 * f 9 := by
  simp only [Fin.prod_univ_ofNat]

/--
info: sum_test (R : Type) [AddCommMonoid R] (f : Fin 10 → R) :
  ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9
-/
#guard_msgs in
#check sum_test

example (R : Type) [AddCommMonoid R] (f : Fin 10 → R) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  simp only [Fin.sum_univ_ofNat]
