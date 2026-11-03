/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.DenseIff
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.CategoryTheory.Presentable.Continuous
public import Mathlib.CategoryTheory.Presentable.Dense

/-!
# The representation theorem

TODO: Add statements about `κ`-accessible categories

In this file, we show that if `C` is a locally `κ`-presentable category,
then `C` identifies to the category of `κ`-continuous presheaves on
the full subcategory of `κ`-presentable objects of `C`.

This completes the equivalence between the conditions (i)-(iv) in
the Representation Theorem 1.46 in the book by Adámek and and Rosický:
if `C` is a locally `w`-small categories and `κ : Cardinal.{w}`, the following
conditions are equivalent:
(i) `C` is locally `κ`-presentable;
(ii) `C` is equivalent to a category `CardinalContinuousFunctor A (Type w) κ` where
`A` is an (essentially) `w`-small category;
(iii) `C` is equivalent to a full subcategory of the form `W.isLocal`
where `W : MorphismProperty (A ⥤ Type w)` is a `w`-small family of morphisms
between `κ`-presentable objects, and `A` is an (essentially) `w`-small category.
(iv) `C` is equivalent to a full, reflective subcategory of `A ⥤ Type w` that
is closed under `κ`-filtered colimits, for some (essentially) `w`-small category A.

In (ii)-(iii)-(iv), `A` can be chosen to be the opposite category of the
full subcategory of `C` consisting of `κ`-presentable objects.

In this file, we show (i) => (ii) (see
`IsCardinalLocallyPresentable.isEquivalence_toCardinalContinuousFunctor`).
We showed (ii) => (iii) as `Presheaf.isCardinalContinuous_eq_isLocal` in the
file `Mathlib/CategoryTheory/Presentable/Continuous.lean`.
The implication (iii) => (iv) follows from the Orthogonal-reflection construction
from the file `Mathlib/CategoryTheory/Presentable/OrthogonalReflection.lean`
(see lemma `MorphismProperty.isRightAdjoint_ι_isLocal`), and the implication
(iv) => (i) follows from lemma `Adjunction.isCardinalLocallyPresentable` from the
file `Mathlib/CategoryTheory/Presentable/Adjunction.lean` (and the fact that
presheaf categories are locally presentable,
see `Mathlib/CategoryTheory/Presentable/Presheaf.lean`).

The Representation THeorem 1.46 in the book by Adámek and and Rosický contains
another condition (v) saying that `C` is a `κ`-free completion of a small
category, but it is not part of this formalization.

The relation between locally `κ`-presentable categories and categories of (`κ`-continuous)
presheaves that is provided by the representation theorem allows to prove
the existence of all limits in locally `κ`-presentable categories.
In the file `Mathlib/CategoryTheory/Presentable/Presheaf.lean`,
we had to assume that a locally `κ`-presentable category `C` had pullbacks in order
to show that a functor category `J ⥤ C` (with `J` (essentially) small) was also
locally `κ`-presentable: this assumption is now automatically satisfied.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

@[expose] public section

universe w

namespace CategoryTheory

open Limits Opposite

-- to be moved
namespace Presheaf

variable {C D : Type*} [Category* C] [Category* D] [LocallySmall.{w} C] [LocallySmall.{w} D]
  (F : C ⥤ D) [F.Full] [F.Faithful]

noncomputable def restrictedShrinkYonedaObjObjRepresentableBy (X : C) :
    ((Presheaf.restrictedShrinkYoneda.{w} F).obj (F.obj X)).RepresentableBy X :=
  (shrinkYonedaRepresentableBy.{w} X).ofIso (asIso (shrinkYonedaMap.{w} F X))

instance (X : C) :
    ((Presheaf.restrictedShrinkYoneda.{w} F).obj (F.obj X)).IsRepresentable :=
  (restrictedShrinkYonedaObjObjRepresentableBy F X).isRepresentable

end Presheaf

section

variable (C : Type*) [Category* C] (κ : Cardinal.{w}) [Fact κ.IsRegular]

instance [LocallySmall.{w} C] [HasColimitsOfSize.{w, w} C] (X : C) :
    Functor.IsCardinalContinuous
      ((Presheaf.restrictedShrinkYoneda.{w} (isCardinalPresentable C κ).ι).obj X) κ where
  preservesLimitsOfShape J _ _ := by
    have : (isCardinalPresentable C κ).IsClosedUnderColimitsOfShape Jᵒᵖ :=
      isClosedUnderColimitsOfShape_isCardinalPresentable _ (by simpa)
    have : PreservesLimitsOfShape J (isCardinalPresentable C κ).ι.op :=
      preservesLimitsOfShape_op _ _
    dsimp [Presheaf.restrictedShrinkYoneda]
    infer_instance

namespace IsCardinalAccessible

variable [IsCardinalAccessibleCategory C κ]

open ObjectProperty.IsClosedUnderCardinalFilteredColimits in
instance (X : C) :
    ((Presheaf.restrictedShrinkYoneda.{w}
      (isCardinalPresentable C κ).ι).obj X).IsCardinalIndObject κ := by
  rw [← Functor.isCardinalIndObject]
  have := isCardinalClosedUnderColimitsOfShape
    (Functor.isCardinalIndObject (isCardinalPresentable C κ).FullSubcategory κ) κ
    (CostructuredArrow (isCardinalPresentable C κ).ι X)
  exact (Functor.isCardinalIndObject _ κ).prop_of_isColimit
    (isColimitOfPreserves (Presheaf.restrictedShrinkYoneda.{w}
      (isCardinalPresentable C κ).ι) ((isCardinalPresentable C κ).ι.denseAt X))
    (fun Y ↦ inferInstanceAs (((Presheaf.restrictedShrinkYoneda _).obj
    ((isCardinalPresentable C κ).ι.obj Y.left)).IsCardinalIndObject κ))

lemma essImage_restrictedShrinkYoneda_isCardinalPresentable_ι :
    (Presheaf.restrictedShrinkYoneda.{w} (isCardinalPresentable C κ).ι).essImage =
      Functor.isCardinalIndObject _ κ := by
  refine le_antisymm ?_ ?_
  · rw [← ObjectProperty.map_top, ObjectProperty.map_le_iff]
    intro P _
    simp only [ObjectProperty.prop_inverseImage_iff]
    infer_instance
  · intro P hP
    simp only [Functor.isCardinalIndObject_iff] at hP
    obtain ⟨J, _, _, F, ι, ⟨h⟩⟩ := hP
    have := HasCardinalFilteredColimits.hasColimitsOfShape C κ J
    exact ⟨colimit (F ⋙ ObjectProperty.ι _),
      ⟨IsColimit.coconePointUniqueUpToIso
      (isColimitOfPreserves
        (Presheaf.restrictedShrinkYoneda.{w} (isCardinalPresentable C κ).ι)
        (colimit.isColimit (F ⋙ ObjectProperty.ι _)))
      ((IsColimit.precomposeInvEquiv
        (Functor.isoWhiskerLeft _ (asIso (shrinkYonedaMap₂.{w} _)) ≪≫
          (Functor.associator _ _ _).symm) _).symm h)⟩⟩

@[implicit_reducible, simps! obj_obj map_hom]
noncomputable def toCardinalIndObject :
    C ⥤ CardinalInd (isCardinalPresentable C κ).FullSubcategory κ :=
  ObjectProperty.lift _ (Presheaf.restrictedShrinkYoneda.{w} (ObjectProperty.ι _))
    inferInstance

/-- The functor `toCardinalIndObject C κ` is induced by the restricted
Yoneda functor. -/
@[simps! +dsimpLhs]
noncomputable def toCardinalIndObjectCompIso :
    toCardinalIndObject C κ ⋙ ObjectProperty.ι _ ≅
      Presheaf.restrictedShrinkYoneda.{w} (ObjectProperty.ι _) := Iso.refl _

instance isEquivalence_toCardinalIndObject :
    (toCardinalIndObject C κ).IsEquivalence := by
  dsimp [toCardinalIndObject]
  rw [ObjectProperty.isEquivalence_lift_iff,
    IsCardinalAccessible.essImage_restrictedShrinkYoneda_isCardinalPresentable_ι]

end IsCardinalAccessible

namespace IsCardinalLocallyPresentable

variable [IsCardinalLocallyPresentable C κ]

/-- When `C` is a locally `w`-small category with colimits, this is the fully faithful
functor from `C` to the category of `κ`-continuous presheaves of the full subcategory
of `κ`-presentable objects in `C`. This is an equivalence of categories when `C`
is locally `κ`-presentable. -/
@[implicit_reducible, simps! obj_obj map_hom]
noncomputable def toCardinalContinuousFunctor :
    C ⥤ CardinalContinuousFunctor (isCardinalPresentable C κ).FullSubcategoryᵒᵖ (Type w) κ :=
  ObjectProperty.lift _ (Presheaf.restrictedShrinkYoneda.{w} (ObjectProperty.ι _))
    inferInstance

/-- The functor `toCardinalContinuousFunctor C κ` is induced by the restricted
Yoneda functor. -/
@[simps! +dsimpLhs]
noncomputable def toCardinalContinuousFunctorCompIso :
    toCardinalContinuousFunctor C κ ⋙ ObjectProperty.ι _ ≅
      Presheaf.restrictedShrinkYoneda.{w} (ObjectProperty.ι _) := Iso.refl _

instance isEquivalence_toCardinalContinuousFunctor :
    (toCardinalContinuousFunctor C κ).IsEquivalence := by
  dsimp [toCardinalContinuousFunctor]
  rw [ObjectProperty.isEquivalence_lift_iff,
    IsCardinalAccessible.essImage_restrictedShrinkYoneda_isCardinalPresentable_ι,
    Presheaf.isCardinalIndObject_eq_isCardinalContinuous]
  intro J _ hJ
  have := isClosedUnderColimitsOfShape_isCardinalPresentable C hJ
  infer_instance

include κ in
lemma hasLimitsOfSize : HasLimitsOfSize.{w, w} C :=
  Adjunction.has_limits_of_equivalence
    (IsCardinalLocallyPresentable.toCardinalContinuousFunctor C κ)

include κ in
lemma hasFiniteLimits : HasFiniteLimits C := by
  have := hasLimitsOfSize C κ
  exact hasFiniteLimits_of_hasLimitsOfSize.{w, w} C

instance (J : Type*) [Category* J] [EssentiallySmall.{w} J] :
    IsCardinalLocallyPresentable (J ⥤ C) κ := by
  have := IsCardinalLocallyPresentable.hasFiniteLimits C κ
  infer_instance

end IsCardinalLocallyPresentable

end

namespace IsLocallyPresentable

instance (C : Type*) [Category* C] [IsLocallyPresentable.{w} C] :
    HasLimitsOfSize.{w, w} C := by
  obtain ⟨κ, _, _⟩ := IsLocallyPresentable.exists_cardinal.{w} C
  exact IsCardinalLocallyPresentable.hasLimitsOfSize C κ

instance (C : Type*) [Category* C] [IsLocallyPresentable.{w} C] :
    HasFiniteLimits C :=
  hasFiniteLimits_of_hasLimitsOfSize.{w, w} C

example (C J : Type*) [Category* C] [Category* J] [EssentiallySmall.{w} J]
    [IsLocallyPresentable.{w} C] :
    IsLocallyPresentable.{w} (J ⥤ C) := by
  infer_instance

end IsLocallyPresentable

end CategoryTheory
