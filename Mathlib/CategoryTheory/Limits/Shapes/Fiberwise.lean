/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!

# Computing Colimits Fiberwise

In this file, we consider a category `J` equipped with a functor `F : J ⥤ D` to a discrete category
`D`. Then the colimit of any diagram `diagram : J ⥤ C` can be computed fiberwise, using the
following algorithm:

1. For each `d : D`, construct a colimit cocone over the restricted diagram
   `fiberInclusion F d ⋙ diagram`.
2. Take a colimit cofan of the values of these cocones over all `d : D`.

## Main Results

- `colimitOfFiber`: As above, given colimits on each restriction, and coproduct of the values, this
  gives the colimit of the original diagram `diagram`.

-/

universe v v₁ v₂ u u₁ u₂

open CategoryTheory Functor Category Fiber

variable {J : Type u} {D : Type u₁}
  [Category.{v} J] [Category.{v₁} D] [IsDiscrete D]
  (F : J ⥤ D)
  {C : Type u₂} [Category.{v₂} C] (diagram : J ⥤ C)

namespace CategoryTheory

namespace Limits

open Functor

variable (fiberwiseCocone : ∀ d : D, Cocone (fiberInclusion (p := F) (S := d) ⋙ diagram))
  (cofan : Cofan fun d : D ↦ (fiberwiseCocone d).pt)

/-- Given a functor `F : J ⥤ D` to a discrete category `D`, and a diagram `diagram : J ⥤ C`,
we can construct a cocone over `diagram` using the following algorithm:

1. For each `d : D`, construct a cocone over the restricted diagram `fiberInclusion F d ⋙ diagram`.
2. Take a cofan on the cocone points of these cocones over all `d : D`.
-/
@[simps] def coconeOfFiberOfIsDiscrete : Cocone diagram where
  pt := cofan.pt
  ι :=
  { app j := (fiberwiseCocone (F.obj j)).ι.app (.mk rfl) ≫ cofan.inj (F.obj j)
    naturality j₁ j₂ f := by
      simp only [const_obj_obj, const_obj_map, comp_id]
      refine F.fiber_inductionOn_of_isDiscrete f fun d j₁ j₂ f ↦ ?_
      rw [← (fiberwiseCocone (F.obj j₁.1)).w (F.fiberPreimageOfIsDiscrete (.mk rfl)
        (.mk (j₂.2.trans j₁.2.symm)) f.1), Functor.comp_map, assoc]
      congr 1
      grind }

variable (fiberwiseColimit : ∀ d : D, IsColimit (fiberwiseCocone d))
  (colimitCofan : IsColimit cofan)

/-- Given a functor `F : J ⥤ D` to a discrete category, the colimit of any diagram `J ⥤ C` can
be computed using this algorithm:

1. For each `d : D`, compute the colimit of the restricted diagram `fiberInclusion F d ⋙ diagram`.
2. Take the coproduct of these colimits over all `d : D`.
-/
@[simps] def colimitOfFiberOfIsDiscrete :
    IsColimit (coconeOfFiberOfIsDiscrete F diagram fiberwiseCocone cofan) where
  desc c := Cofan.IsColimit.desc colimitCofan fun d ↦ (fiberwiseColimit d).desc
    (c.whisker (fiberInclusion))
  uniq c s w := by
    refine Cofan.IsColimit.hom_ext colimitCofan _ _ fun d ↦
      (fiberwiseColimit d).hom_ext fun j ↦ ?_
    rw [Cofan.IsColimit.fac, IsColimit.fac, Cocone.whisker_ι, whiskerLeft_app, ← w,
      coconeOfFiberOfIsDiscrete_ι_app, assoc]
    obtain ⟨j, rfl⟩ := j
    rfl

-- Not an instance because `D` cannot be inferred.
theorem hasColimit_of_fiber_of_isDiscrete
    [∀ d, HasColimit (fiberInclusion (p := F) (S := d) ⋙ diagram)]
    [HasColimit (Discrete.functor fun d ↦
      colimit (fiberInclusion (p := F) (S := d) ⋙ diagram))] :
    HasColimit diagram :=
  ⟨⟨⟨_, colimitOfFiberOfIsDiscrete F diagram _ _
    (fun d ↦ colimit.isColimit (fiberInclusion (p := F) (S := d) ⋙ diagram))
    (coproductIsCoproduct fun d ↦ colimit (fiberInclusion (p := F) (S := d) ⋙ diagram))⟩⟩⟩

-- Not an instance because `D` cannot be inferred.
theorem hasColimitOfShapes_of_fiber_of_isDiscrete
    [∀ d, HasColimitsOfShape (F.Fiber d) C] [HasCoproductsOfShape D C] :
    HasColimitsOfShape J C :=
  ⟨fun diagram ↦ hasColimit_of_fiber_of_isDiscrete F diagram⟩

end Limits

end CategoryTheory
