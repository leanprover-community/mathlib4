/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/

import Mathlib.CategoryTheory.WithTerminal
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# The Augmented simplex category

This file defines the `AugmentedSimplexCategory` as the category obtained by adding an initial
object to `SimplexCategory` (using `CategoryTheory.WithInitial`).

This definition provides a canonical full and faithful inclusion functor
`inclusion : SimplexCategory ⥤ AugmentedSimplexCategory`.

We prove that functors out of `AugmentedSimplexCategory` are equivalent to augmented cosimplicial objects
and that functors out of `AugmentedSimplexCategoryᵒᵖ` are equivalent to augmented simplicial objects,
and we provide a translation of the main constrcutions on (co)simplicial objects
(i.e `drop`, `point` and `toArrow`) in terms of these equivalences.

## TODOs
* Define a monoidal structure on `AugmentedSimplexCategory`.
-/

open CategoryTheory

/-- The `AugmentedSimplexCategory` is the category obtained from `SimplexCategory` by adjoining an
initial object. -/
def AugmentedSimplexCategory := WithInitial SimplexCategory
  deriving SmallCategory

namespace AugmentedSimplexCategory

variable {C : Type*} [Category C]

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
def equivAugmentedCosimplicialObjectDrop :
    equivAugmentedCosimplicialObject.functor ⋙ CosimplicialObject.Augmented.drop ≅
    (whiskeringLeft _ _ C).obj inclusion :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

/-- Through the equivalence `(AugmentedSimplexCategory ⥤ C) ≌ CosimplicialObject.Augmented C`,
taking the point of the augmentation corresponds to evaluation at the initial object. -/
@[simps!]
def equivAugmentedCosimplicialObjectPoint :
    equivAugmentedCosimplicialObject.functor ⋙ CosimplicialObject.Augmented.point ≅
    ((evaluation _ _).obj (.star) : ((AugmentedSimplexCategory ⥤ C) ⥤ C)) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

/-- Through the equivalence `(AugmentedSimplexCategory ⥤ C) ≌ CosimplicialObject.Augmented C`,
the arrow attached to the cosimplicial object is the one obtained by evaluation at the unique arrow
`star ⟶ of [0]`. -/
@[simps!]
def equivAugmentedCosimplicialObjectToArrow :
    equivAugmentedCosimplicialObject.functor ⋙ CosimplicialObject.Augmented.toArrow ≅
    Functor.mapArrowFunctor _ C ⋙
      (evaluation _ _ |>.obj <| .mk <| WithInitial.homTo <| .mk 0) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

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
def equivAugmentedSimplicialObjectDrop :
    equivAugmentedSimplicialObject.functor ⋙ SimplicialObject.Augmented.drop ≅
    (whiskeringLeft _ _ C).obj inclusion.op :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

/-- Through the equivalence `(AugmentedSimplexCategory ⥤ C) ≌ CosimplicialObject.Augmented C`,
taking the point of the augmentation corresponds to evaluation at the initial object. -/
@[simps!]
def equivAugmentedSimplicialObjectPoint :
    equivAugmentedSimplicialObject.functor ⋙ SimplicialObject.Augmented.point ≅
    (evaluation _ C).obj (.op .star) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

/-- Through the equivalence `(AugmentedSimplexCategory ⥤ C) ≌ CosimplicialObject.Augmented C`,
the arrow attached to the cosimplicial object is the one obtained by evaluation at the unique arrow
`star ⟶ of [0]`. -/
@[simps!]
def equivAugmentedSimplicialObjectToArrow :
    equivAugmentedSimplicialObject.functor ⋙ SimplicialObject.Augmented.toArrow ≅
    Functor.mapArrowFunctor _ C ⋙
      (evaluation _ _ |>.obj <| .mk <| .op <| WithInitial.homTo <| .mk 0) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

end AugmentedSimplexCategory
