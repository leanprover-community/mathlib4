/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# Limits over essentially small indexing categories

If `C` has limits of size `w` and `J` is `w`-essentially small, then `C` has limits of shape `J`.

See also the file `FinallySmall.lean` for more general results.

-/

@[expose] public section


universe w₁ w₂ v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

namespace CategoryTheory.Limits

variable (J : Type u₂) [Category.{v₂} J] (C : Type u₁) [Category.{v₁} C]

theorem hasLimitsOfShape_of_essentiallySmall [EssentiallySmall.{w₁} J]
    [HasLimitsOfSize.{w₁, w₁} C] : HasLimitsOfShape J C :=
  hasLimitsOfShape_of_equivalence <| Equivalence.symm <| equivSmallModel.{w₁} J

theorem hasColimitsOfShape_of_essentiallySmall [EssentiallySmall.{w₁} J]
    [HasColimitsOfSize.{w₁, w₁} C] : HasColimitsOfShape J C :=
  hasColimitsOfShape_of_equivalence <| Equivalence.symm <| equivSmallModel.{w₁} J

theorem hasProductsOfShape_of_small (β : Type w₂) [Small.{w₁} β] [HasProducts.{w₁} C] :
    HasProductsOfShape β C :=
  hasLimitsOfShape_of_equivalence <| Discrete.equivalence <| Equiv.symm <| equivShrink β

theorem hasCoproductsOfShape_of_small (β : Type w₂) [Small.{w₁} β] [HasCoproducts.{w₁} C] :
    HasCoproductsOfShape β C :=
  hasColimitsOfShape_of_equivalence <| Discrete.equivalence <| Equiv.symm <| equivShrink β

end CategoryTheory.Limits
