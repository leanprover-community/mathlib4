/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.WithTerminal.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# The Augmented simplex category

This file defines the `AugmentedSimplexCategory` as the category obtained by adding an initial
object to `SimplexCategory` (using `CategoryTheory.WithInitial`).

This definition provides a canonical full and faithful inclusion functor
`inclusion : SimplexCategory ⥤ AugmentedSimplexCategory`.

We prove that functors out of `AugmentedSimplexCategory` are equivalent to augmented cosimplicial
objects and that functors out of `AugmentedSimplexCategoryᵒᵖ` are equivalent to augmented simplicial
objects, and we provide a translation of the main constructions on augmented (co)simplicial objects
(i.e `drop`, `point` and `toArrow`) in terms of these equivalences.

-/

@[expose] public section

open CategoryTheory

/-- The `AugmentedSimplexCategory` is the category obtained from `SimplexCategory` by adjoining an
initial object. -/
abbrev AugmentedSimplexCategory := WithInitial SimplexCategory

namespace AugmentedSimplexCategory

variable {C : Type*} [Category* C]

/-- The canonical inclusion from `SimplexCategory` to `AugmentedSimplexCategory`. -/
@[simps!]
def inclusion : SimplexCategory ⥤ AugmentedSimplexCategory := WithInitial.incl

instance : inclusion.Full := inferInstanceAs WithInitial.incl.Full
instance : inclusion.Faithful := inferInstanceAs WithInitial.incl.Faithful

instance : Limits.HasInitial AugmentedSimplexCategory :=
  inferInstanceAs <| Limits.HasInitial <| WithInitial _

/-- The equivalence between functors out of `AugmentedSimplexCategory` and augmented
cosimplicial objects. -/
@[simps!]
def equivAugmentedCosimplicialObject :
    (AugmentedSimplexCategory ⥤ C) ≌ CosimplicialObject.Augmented C :=
  WithInitial.equivComma

/-- Through the equivalence `(AugmentedSimplexCategory ⥤ C) ≌ CosimplicialObject.Augmented C`,
dropping the augmentation corresponds to precomposition with
`inclusion : SimplexCategory ⥤ AugmentedSimplexCategory`. -/
@[simps!]
def equivAugmentedCosimplicialObjectFunctorCompDropIso :
    equivAugmentedCosimplicialObject.functor ⋙ CosimplicialObject.Augmented.drop ≅
    (Functor.whiskeringLeft _ _ C).obj inclusion :=
  .refl _

/-- Through the equivalence `(AugmentedSimplexCategory ⥤ C) ≌ CosimplicialObject.Augmented C`,
taking the point of the augmentation corresponds to evaluation at the initial object. -/
@[simps!]
def equivAugmentedCosimplicialObjectFunctorCompPointIso :
    equivAugmentedCosimplicialObject.functor ⋙ CosimplicialObject.Augmented.point ≅
    ((evaluation _ _).obj .star : (AugmentedSimplexCategory ⥤ C) ⥤ C) :=
  .refl _

@[deprecated (since := "2025-08-22")] alias equivAugmentedCosimplicialObjecFunctorCompPointIso :=
  equivAugmentedCosimplicialObjectFunctorCompPointIso

/-- Through the equivalence `(AugmentedSimplexCategory ⥤ C) ≌ CosimplicialObject.Augmented C`,
the arrow attached to the cosimplicial object is the one obtained by evaluation at the unique arrow
`star ⟶ of [0]`. -/
@[simps!]
def equivAugmentedCosimplicialObjectFunctorCompToArrowIso :
    equivAugmentedCosimplicialObject.functor ⋙ CosimplicialObject.Augmented.toArrow ≅
    Functor.mapArrowFunctor _ C ⋙
      (evaluation _ _ |>.obj <| .mk <| WithInitial.homTo <| .mk 0) :=
  .refl _

/-- The equivalence between functors out of `AugmentedSimplexCategory` and augmented simplicial
objects. -/
@[simps!]
def equivAugmentedSimplicialObject :
    (AugmentedSimplexCategoryᵒᵖ ⥤ C) ≌ SimplicialObject.Augmented C :=
  WithInitial.opEquiv SimplexCategory |>.congrLeft |>.trans WithTerminal.equivComma

/-- Through the equivalence `(AugmentedSimplexCategoryᵒᵖ ⥤ C) ≌ SimplicialObject.Augmented C`,
dropping the augmentation corresponds to precomposition with
`inclusionᵒᵖ : SimplexCategoryᵒᵖ ⥤ AugmentedSimplexCategoryᵒᵖ`. -/
@[simps!]
def equivAugmentedSimplicialObjectFunctorCompDropIso :
    equivAugmentedSimplicialObject.functor ⋙ SimplicialObject.Augmented.drop ≅
    (Functor.whiskeringLeft _ _ C).obj inclusion.op :=
  .refl _

/-- Through the equivalence `(AugmentedSimplexCategory ⥤ C) ≌ CosimplicialObject.Augmented C`,
taking the point of the augmentation corresponds to evaluation at the initial object. -/
@[simps!]
def equivAugmentedSimplicialObjectFunctorCompPointIso :
    equivAugmentedSimplicialObject.functor ⋙ SimplicialObject.Augmented.point ≅
    (evaluation _ C).obj (.op .star) :=
  .refl _

/-- Through the equivalence `(AugmentedSimplexCategory ⥤ C) ≌ CosimplicialObject.Augmented C`,
the arrow attached to the cosimplicial object is the one obtained by evaluation at the unique arrow
`star ⟶ of [0]`. -/
@[simps!]
def equivAugmentedSimplicialObjectFunctorCompToArrowIso :
    equivAugmentedSimplicialObject.functor ⋙ SimplicialObject.Augmented.toArrow ≅
    Functor.mapArrowFunctor _ C ⋙
      (evaluation _ _ |>.obj <| .mk <| .op <| WithInitial.homTo <| .mk 0) :=
  .refl _

end AugmentedSimplexCategory
