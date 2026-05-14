/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.CategoryTheory.Limits.Preorder
public import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Set
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.CategoryTheory.CategoryStar
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# The evaluation functor on subcomplexes

We define an evaluation functor `SSet.Subcomplex.evaluation : X.Subcomplex ⥤ Set (X.obj j)`
when `X : SSet` and `j : SimplexCategoryᵒᵖ`. We use it to show that the functor
`Subcomplex.toSSetFunctor : X.Subcomplex ⥤ SSet` preserves filtered colimits.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SSet.Subcomplex

/-- The evaluation functor `X.Subcomplex ⥤ Set (X.obj j)` when `X : SSet`
and `j : SimplexCategoryᵒᵖ`. -/
@[simps]
def evaluation (X : SSet.{u}) (j : SimplexCategoryᵒᵖ) :
    X.Subcomplex ⥤ Set (X.obj j) where
  obj A := A.obj j
  map f := CategoryTheory.homOfLE (leOfHom f j)

instance {J : Type*} [Category* J] {X : SSet.{u}} [IsFilteredOrEmpty J] :
    PreservesColimitsOfShape J (Subcomplex.toSSetFunctor (X := X)) where
  preservesColimit {F} :=
    preservesColimit_of_preserves_colimit_cocone
      (Preorder.colimitCoconeOfIsLUB F isLUB_iSup).isColimit
        (evaluationJointlyReflectsColimits _ (fun j ↦ IsColimit.ofIsoColimit
          (isColimitOfPreserves Set.functorToTypes
              ((Preorder.colimitCoconeOfIsLUB (F ⋙ evaluation _ j) isLUB_iSup).isColimit))
                (Cocone.ext (Set.functorToTypes.mapIso
                  (CategoryTheory.eqToIso (by cat_disch))))))

end SSet.Subcomplex
