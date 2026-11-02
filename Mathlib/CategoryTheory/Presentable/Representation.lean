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

namespace IsCardinalLocallyPresentable

variable (C : Type*) [Category* C] (κ : Cardinal.{w}) [Fact κ.IsRegular]

section

variable [LocallySmall.{w} C] [HasColimitsOfSize.{w, w} C]

instance (X : C) :
    Functor.IsCardinalContinuous
      ((Presheaf.restrictedShrinkYoneda.{w} (isCardinalPresentable C κ).ι).obj X) κ where
  preservesLimitsOfShape J _ _ := by
    have : (isCardinalPresentable C κ).IsClosedUnderColimitsOfShape Jᵒᵖ :=
      isClosedUnderColimitsOfShape_isCardinalPresentable _ (by simpa)
    have : PreservesLimitsOfShape J (isCardinalPresentable C κ).ι.op :=
      preservesLimitsOfShape_op _ _
    dsimp [Presheaf.restrictedShrinkYoneda]
    infer_instance

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

end

variable [IsCardinalLocallyPresentable C κ]

instance : (toCardinalContinuousFunctor C κ).Faithful := by
  have := Functor.Faithful.of_iso (toCardinalContinuousFunctorCompIso C κ).symm
  exact Functor.Faithful.of_comp _ (ObjectProperty.ι _)

instance : (toCardinalContinuousFunctor C κ).Full := by
  have := Functor.Full.of_iso (toCardinalContinuousFunctorCompIso C κ).symm
  exact Functor.Full.of_comp_faithful _ (ObjectProperty.ι _)

instance : (toCardinalContinuousFunctor C κ).EssSurj where
  mem_essImage := fun F ↦ by
    obtain ⟨J, _, hJ, G, ι, ⟨h⟩⟩ :=
      Presheaf.exists_presentation_of_isCardinalContinuous.{w} κ (fun J _ hJ ↦ by
        have := isClosedUnderColimitsOfShape_isCardinalPresentable C hJ
        infer_instance) F.obj
    let c' : Cocone (G ⋙ shrinkYoneda.{w}) :=
      { pt :=
          (isCardinalPresentable C κ).ι.op ⋙
            shrinkYoneda.{w}.obj (colimit (G ⋙ ObjectProperty.ι _))
        ι.app j :=
          shrinkYonedaMap (isCardinalPresentable C κ).ι (G.obj j) ≫
            Functor.whiskerLeft _ (shrinkYoneda.map (colimit.ι (G ⋙ ObjectProperty.ι _) j))
        ι.naturality _ _ f := by
          ext : 2
          simp [← colimit.w (G ⋙ ObjectProperty.ι _) f,
            shrinkYonedaMap_naturality_app_assoc.{w}] }
    have h' : IsColimit c' :=
      evaluationJointlyReflectsColimits _ (fun ⟨X⟩ ↦ by
        have := Functor.preservesColimitsOfShape_of_isCardinalAccessible
          (shrinkCoyoneda.{w}.obj (op X.1)) κ J
        refine (IsColimit.equivOfNatIsoOfIso (Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft _ (asIso (shrinkCoyonedaMap _ _)) ≪≫
            (Functor.associator _ _ _).symm) _ _ ?_).2
              (isColimitOfPreserves
                (shrinkCoyoneda.{w}.obj (op X.1)) (colimit.isColimit (G ⋙ ObjectProperty.ι _)))
        exact Cocone.ext (Iso.refl _) (fun j ↦ by simp [c', shrinkCoyonedaMap_app]))
    exact ⟨colimit (G ⋙ ObjectProperty.ι _),
      ⟨ObjectProperty.isoMk _ (IsColimit.coconePointUniqueUpToIso h' h)⟩⟩

instance isEquivalence_toCardinalContinuousFunctor :
    (toCardinalContinuousFunctor C κ).IsEquivalence where

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

namespace IsCardinalPresentable

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

end IsCardinalPresentable

end CategoryTheory
