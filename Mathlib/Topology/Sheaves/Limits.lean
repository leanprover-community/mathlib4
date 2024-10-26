/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Presheaves in `C` have limits and colimits when `C` does.
-/


noncomputable section

universe v u w

open CategoryTheory

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {J : Type v} [SmallCategory J]

namespace TopCat

instance [HasLimits C] (X : TopCat.{v}) : HasLimits.{v} (Presheaf C X) :=
  Limits.functorCategoryHasLimitsOfSize.{v, v}

instance [HasColimits.{v, u} C] (X : TopCat.{w}) : HasColimitsOfSize.{v, v} (Presheaf C X) :=
  Limits.functorCategoryHasColimitsOfSize

instance [HasLimits C] (X : TopCat) : CreatesLimits.{v, v} (Sheaf.forget C X) :=
  Sheaf.createsLimits.{u, v, v}

instance [HasLimits C] (X : TopCat.{v}) : HasLimitsOfSize.{v, v} (Sheaf.{v} C X) :=
  hasLimits_of_hasLimits_createsLimits (Sheaf.forget C X)

theorem isSheaf_of_isLimit [HasLimits C] {X : TopCat} (F : J ⥤ Presheaf.{v} C X)
    (H : ∀ j, (F.obj j).IsSheaf) {c : Cone F} (hc : IsLimit c) : c.pt.IsSheaf := by
  let F' : J ⥤ Sheaf C X :=
    { obj := fun j => ⟨F.obj j, H j⟩
      map := fun f => ⟨F.map f⟩ }
  let e : F' ⋙ Sheaf.forget C X ≅ F := NatIso.ofComponents fun _ => Iso.refl _
  exact Presheaf.isSheaf_of_iso
    ((isLimitOfPreserves (Sheaf.forget C X) (limit.isLimit F')).conePointsIsoOfNatIso hc e)
    (limit F').2

theorem limit_isSheaf [HasLimits C] {X : TopCat} (F : J ⥤ Presheaf.{v} C X)
    (H : ∀ j, (F.obj j).IsSheaf) : (limit F).IsSheaf :=
  isSheaf_of_isLimit F H (limit.isLimit F)

end TopCat
