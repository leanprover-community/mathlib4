import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C D D' H : Type _} [Category C] [Category D] [Category D'] [Category H]
  (F : C ⥤ H) (L : C ⥤ D) (W : MorphismProperty C)

class HasPointwiseRightDerivedFunctorAt (X : C) : Prop where
  hasColimit' : F.HasPointwiseLeftKanExtensionAt W.Q (W.Q.obj X)

/-lemma hasPointwiseRightDerivedFunctorAt_iff [L.IsLocalization W] (X : C) :
    F.HasPointwiseRightDerivedFunctorAt W X ↔
      F.HasPointwiseLeftKanExtensionAt L (L.obj X) := sorry-/

section

variable [∀ X, F.HasPointwiseRightDerivedFunctorAt W X]

lemma hasRightDerivedFunctor_of_pointwise :
    F.HasRightDerivedFunctor W where
  hasLeftKanExtension' := by
    have : ∀ X, F.HasPointwiseLeftKanExtensionAt W.Q (W.Q.obj X) :=
      fun X => HasPointwiseRightDerivedFunctorAt.hasColimit'
    -- this should be an instance
    have : EssSurj W.Q := Localization.essSurj _ W
    have : ∀ Y, F.HasPointwiseLeftKanExtensionAt W.Q Y := fun Y => by
      rw [← F.hasPointwiseLeftKanExtensionAt_iff_of_iso _ (W.Q.objObjPreimageIso Y)]
      infer_instance
    infer_instance

end

end Functor

end CategoryTheory
