/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Order.InitialSeg
import Mathlib.Order.SuccPred.InitialSeg
import Mathlib.Order.Interval.Set.InitialSeg
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.IsLimit

/-!
# Cocones associated to principal segments

If `f : α <i β` is a principal segment and `F : β ⥤ C`,
there is a cocone for `f.monotone.functor ⋙ F : α ⥤ C`
the point of which is `F.obj f.top`.

-/

open CategoryTheory Category Limits

variable {α α' β : Type*} [PartialOrder α] [PartialOrder α'] [PartialOrder β]

variable {C : Type*} [Category C]

/-- When `f : α <i β` and a functor `F : β ⥤ C`, this is the cocone
for `f.monotone.functor ⋙ F : α ⥤ C` whose point if `F.obj f.top`. -/
@[simps]
def PrincipalSeg.cocone (f : α <i β) (F : β ⥤ C) :
    Cocone (f.monotone.functor ⋙ F) where
  pt := F.obj f.top
  ι :=
    { app i := F.map (homOfLE (f.lt_top i).le)
      naturality i j f := by
        dsimp
        rw [← F.map_comp, comp_id]
        rfl }

/-- If `f : α <i β` is a principal segment and `F : β ⥤ C`, then `f.cocone F`
is colimit if `(Set.principalSegIio f.top).cocone F` is. -/
noncomputable def PrincipalSeg.coconeIsColimitOfIsColimit (f : α <i β) (F : β ⥤ C)
    (h : IsColimit ((Set.principalSegIio f.top).cocone F)) :
    IsColimit (f.cocone F) :=
  h.whiskerEquivalence f.orderIsoIio.equivalence
