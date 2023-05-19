/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module topology.sheaves.limits
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Sheaves.Sheaf
import Mathbin.CategoryTheory.Sites.Limits
import Mathbin.CategoryTheory.Limits.FunctorCategory

/-!
# Presheaves in `C` have limits and colimits when `C` does.
-/


noncomputable section

universe v u

open CategoryTheory

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {J : Type v} [SmallCategory J]

namespace TopCat

instance [HasLimits C] (X : TopCat) : HasLimits (Presheaf C X) :=
  Limits.functorCategoryHasLimitsOfSize.{v, v}

instance [HasColimits C] (X : TopCat) : HasColimitsOfSize.{v} (Presheaf C X) :=
  Limits.functorCategoryHasColimitsOfSize

instance [HasLimits C] (X : TopCat) : CreatesLimits (Sheaf.forget C X) :=
  Sheaf.CategoryTheory.SheafToPresheaf.CategoryTheory.createsLimits.{u, v, v}

instance [HasLimits C] (X : TopCat) : HasLimitsOfSize.{v} (Sheaf.{v} C X) :=
  has_limits_of_has_limits_creates_limits (Sheaf.forget C X)

theorem isSheaf_of_isLimit [HasLimits C] {X : TopCat} (F : J ⥤ Presheaf.{v} C X)
    (H : ∀ j, (F.obj j).IsSheaf) {c : Cone F} (hc : IsLimit c) : c.pt.IsSheaf :=
  by
  let F' : J ⥤ sheaf C X :=
    { obj := fun j => ⟨F.obj j, H j⟩
      map := fun X Y f => ⟨F.map f⟩ }
  let e : F' ⋙ sheaf.forget C X ≅ F := nat_iso.of_components (fun _ => iso.refl _) (by tidy)
  exact
    presheaf.is_sheaf_of_iso
      ((is_limit_of_preserves (sheaf.forget C X) (limit.is_limit F')).conePointsIsoOfNatIso hc e)
      (limit F').2
#align Top.is_sheaf_of_is_limit TopCat.isSheaf_of_isLimit

theorem limit_isSheaf [HasLimits C] {X : TopCat} (F : J ⥤ Presheaf.{v} C X)
    (H : ∀ j, (F.obj j).IsSheaf) : (limit F).IsSheaf :=
  isSheaf_of_isLimit F H (limit.isLimit F)
#align Top.limit_is_sheaf TopCat.limit_isSheaf

end TopCat

