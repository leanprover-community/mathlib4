/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preorder
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Set
public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# ...

-/

@[expose] public section

universe w v₁ v₂

namespace CategoryTheory.Subfunctor

open Limits

variable {C : Type*} [Category* C]

@[simps]
def evaluation (F : C ⥤ Type w) (j : C) :
    Subfunctor F ⥤ Set (F.obj j) where
  obj A := A.obj j
  map f := CategoryTheory.homOfLE (leOfHom f j)

-- deduplicate `SimplicialSet/SubcomplexEvaluation.lean`
instance {J : Type*} [Category* J]
    {F : C ⥤ Type w} [IsFilteredOrEmpty J] :
    PreservesColimitsOfShape J (Subfunctor.toFunctorFunctor (F := F)) where
  preservesColimit {G} :=
    preservesColimit_of_preserves_colimit_cocone
      (Preorder.colimitCoconeOfIsLUB G isLUB_iSup).isColimit
        (evaluationJointlyReflectsColimits _ (fun j ↦ IsColimit.ofIsoColimit
          (isColimitOfPreserves Set.functorToTypes
             ((Preorder.colimitCoconeOfIsLUB (G ⋙ evaluation _ j) isLUB_iSup).isColimit))
                (Cocone.ext (Set.functorToTypes.mapIso
                  (CategoryTheory.eqToIso (by cat_disch))))))

end CategoryTheory.Subfunctor
