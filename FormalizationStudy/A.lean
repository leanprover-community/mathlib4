import Mathlib

open MeasureTheory intervalIntegral
#check Set.Ioo_subset_Icc_self

#check MeasureTheory.integral
#check integral_lt_integral_of_continuousOn_of_le_of_exists_lt
#check DifferentiableOn
#check ContinuousOn.mono
/-
I guess I'll defined `f` and `g` to go from `ℝ` instead of `[a,b]`,
because otherwise I'm not sure if `DifferentiableOn` is well-defined
-/
theorem A {a b : ℝ} (hab : a < b) (f f' g g' : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hf' : ∀ x ∈ (Set.Ioo a b), HasDerivAt f (f' x) x)
    (hg' : ∀ x ∈ (Set.Ioo a b), HasDerivAt g (g' x) x) :
    ∃ x ∈ Set.Ioo a b, (f b - f a) * g' x = (g b - g a) * f' x :=
  exists_ratio_hasDerivAt_eq_ratio_slope _ _ hab hg hg' _ _ hf hf'


/-
Let's read my Analysis I notes (on paper):
Rolle's theorem. Is it in mathlib? Yes

Oh, I've found this exact theorem in my paper notes.
BINGO:
-/
#check exists_ratio_hasDerivAt_eq_ratio_slope
#check HasDerivAt
/-
It seems that `HasDerivAt` is a more correct way to state this than `DifferentiableOn`.
-/
