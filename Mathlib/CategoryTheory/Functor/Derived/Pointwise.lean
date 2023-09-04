import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C D H : Type _} [Category C] [Category D] [Category H]
  (F : C ⥤ H) (L : C ⥤ D) (W : MorphismProperty C)

class HasPointwiseRightDerivedFunctorAt (X : C) : Prop where
  hasColimit' : F.HasPointwiseLeftKanExtensionAt W.Q (W.Q.obj X)

/-lemma hasPointwiseRightDerivedFunctorAt_iff
    [L.IsLocalization W] (X : C) :
    F.HasPointwiseRightDerivedFunctorAt W X ↔
      F.HasPointwiseLeftKanExtensionAt L (L.obj X) := sorry

section

variable [∀ X, F.HasPointwiseRightDerivedFunctorAt W X]

lemma hasRightDerivedFunctor_of_pointwise :
    F.HasRightDerivedFunctor W := sorry

end-/

end Functor

end CategoryTheory
