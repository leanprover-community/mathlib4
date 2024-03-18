import Mathlib.CategoryTheory.Shift.Localization
import Mathlib.CategoryTheory.Localization.Linear

namespace CategoryTheory

namespace Shift

variable (R : Type _) [Ring R] {C : Type _} [Category C] [Preadditive C] [Linear R C]
  {D : Type _} [Category D] [Preadditive D] [Linear R D]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [L.Additive] [L.Linear R]
  {M : Type _} [AddMonoid M] [HasShift C M] [HasShift D M] [L.CommShift M]
  [∀ (n : M), (shiftFunctor C n).Additive] [∀ (n : M), (shiftFunctor D n).Additive]
  [∀ (n : M), (shiftFunctor C n).Linear R]

lemma linear_of_localization (n : M) : (shiftFunctor D n).Linear R := by
  have : Localization.Lifting L W (shiftFunctor C n ⋙ L) (shiftFunctor D n) := ⟨(L.commShiftIso n).symm⟩
  rw [← Localization.functor_linear_iff L W R (shiftFunctor C n ⋙ L) (shiftFunctor D n)]
  infer_instance

section

variable [HasShift W.Localization M] [W.Q.CommShift M] [Preadditive W.Localization]
  [W.Q.Additive] [Linear R W.Localization] [W.Q.Linear R]
  [∀ (n : M), (shiftFunctor W.Localization n).Additive]

instance (n : M) : (shiftFunctor W.Localization n).Linear R := linear_of_localization _ W.Q W _

end

section

variable [W.HasLocalization]
variable [HasShift W.Localization' M] [W.Q'.CommShift M] [Preadditive W.Localization']
  [W.Q'.Additive] [Linear R W.Localization'] [W.Q'.Linear R]
  [∀ (n : M), (shiftFunctor W.Localization' n).Additive]

instance (n : M) : (shiftFunctor W.Localization' n).Linear R :=
  linear_of_localization _ W.Q' W _

end

end Shift

end CategoryTheory
