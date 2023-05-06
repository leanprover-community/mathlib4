import Mathlib.CategoryTheory.Localization.FiniteProducts
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

namespace CategoryTheory

open Category Limits ZeroObject

lemma Limits.hasZeroObject_of_additive_functor {C D : Type _} [Category C] [Category D]
    (F : C ⥤ D) [Preadditive C] [Preadditive D] [F.Additive] [HasZeroObject C] :
    HasZeroObject D :=
  ⟨⟨F.obj 0, by rw [IsZero.iff_id_eq_zero, ← F.map_id, id_zero, F.map_zero]⟩⟩

namespace Localization

variable {C D : Type _} [Category C] [Category D] [Preadditive C] [HasFiniteProducts C]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
  [W.IsStableUnderFiniteProducts] [W.ContainsIdentities]

example : HasFiniteProducts W.Localization := inferInstance

end Localization

end CategoryTheory
