import Mathlib.CategoryTheory.Shift.Induced
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Localization.HasLocalization

namespace CategoryTheory

variable {C D : Type _} [Category C] [Category D]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
  (A : Type _) [AddMonoid A] [HasShift C A]

namespace MorphismProperty

class IsCompatibleWithShift : Prop :=
  translate : ∀ (a : A), W.inverseImage (shiftFunctor C a) = W

namespace IsCompatibleWithShift

variable {A}

lemma iff [W.IsCompatibleWithShift A]
    {X Y : C} (f : X ⟶ Y) (a : A) : W (f⟦a⟧') ↔ W f := by
  conv_rhs => rw [← @IsCompatibleWithShift.translate _ _ W A _ _ _ a]

lemma shiftFunctor_comp_inverts [W.IsCompatibleWithShift A] (a : A) :
    W.IsInvertedBy (shiftFunctor C a ⋙ L) := fun _ _ f hf =>
  Localization.inverts L W _ (by simpa only [iff] using hf)

end IsCompatibleWithShift

end MorphismProperty

variable (s : A → D ⥤ D) (i : ∀ a, L ⋙ s a ≅ shiftFunctor C a ⋙ L)

lemma HasShift.localized'_aux :
  Nonempty (Full ((whiskeringLeft C D D).obj L)) ∧ Faithful ((whiskeringLeft C D D).obj L) :=
  ⟨⟨(inferInstance : Full ((Localization.whiskeringLeftFunctor' L W D)))⟩,
    (inferInstance : Faithful ((Localization.whiskeringLeftFunctor' L W D)))⟩

noncomputable def HasShift.localized' :
    HasShift D A :=
  HasShift.induced L A s i (HasShift.localized'_aux L W)

noncomputable def Functor.CommShift.localized' :
    letI : HasShift D A := HasShift.localized' L W A s i
    L.CommShift A :=
  Functor.CommShift.of_induced _ _ _ _ _

noncomputable def HasShift.localized [W.IsCompatibleWithShift A] :
    HasShift D A :=
  HasShift.localized' L W A (fun a =>
    Localization.lift (shiftFunctor C a ⋙ L) (MorphismProperty.IsCompatibleWithShift.shiftFunctor_comp_inverts L W a) L)
    (fun _ => Localization.fac _ _ _)

noncomputable def Functor.CommShift.localized [W.IsCompatibleWithShift A] :
    @Functor.CommShift _ _ _ _ L A _ _ (HasShift.localized L W A) :=
  Functor.CommShift.localized' _ _ _ _ _

attribute [irreducible] HasShift.localized Functor.CommShift.localized

noncomputable instance HasShift.localization [W.IsCompatibleWithShift A] :
    HasShift W.Localization A :=
  HasShift.localized W.Q W A

noncomputable instance MorphismProperty.commShift_Q
    [W.IsCompatibleWithShift A] :
    W.Q.CommShift A :=
  Functor.CommShift.localized W.Q W A

attribute [irreducible] HasShift.localization MorphismProperty.commShift_Q

variable [W.HasLocalization]

noncomputable instance HasShift.localization' [W.IsCompatibleWithShift A] :
    HasShift W.Localization' A :=
  HasShift.localized W.Q' W A

noncomputable instance MorphismProperty.commShift_Q'
    [W.IsCompatibleWithShift A] :
    W.Q'.CommShift A :=
  Functor.CommShift.localized W.Q' W A

attribute [irreducible] HasShift.localization MorphismProperty.commShift_Q'

end CategoryTheory
