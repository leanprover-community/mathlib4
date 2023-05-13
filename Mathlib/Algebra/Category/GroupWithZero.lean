/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module algebra.category.GroupWithZero
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Category.Bipointed
import Mathbin.Algebra.Category.Mon.Basic

/-!
# The category of groups with zero

This file defines `GroupWithZero`, the category of groups with zero.
-/


universe u

open CategoryTheory Order

/-- The category of groups with zero. -/
def GroupWithZeroCat :=
  Bundled GroupWithZero
#align GroupWithZero GroupWithZeroCat

namespace GroupWithZeroCat

instance : CoeSort GroupWithZeroCat (Type _) :=
  Bundled.hasCoeToSort

instance (X : GroupWithZeroCat) : GroupWithZero X :=
  X.str

/-- Construct a bundled `GroupWithZero` from a `group_with_zero`. -/
def of (α : Type _) [GroupWithZero α] : GroupWithZeroCat :=
  Bundled.of α
#align GroupWithZero.of GroupWithZeroCat.of

instance : Inhabited GroupWithZeroCat :=
  ⟨of (WithZero PUnit)⟩

instance : LargeCategory.{u} GroupWithZeroCat
    where
  Hom X Y := MonoidWithZeroHom X Y
  id X := MonoidWithZeroHom.id X
  comp X Y Z f g := g.comp f
  id_comp' X Y := MonoidWithZeroHom.comp_id
  comp_id' X Y := MonoidWithZeroHom.id_comp
  assoc' W X Y Z _ _ _ := MonoidWithZeroHom.comp_assoc _ _ _

instance : ConcreteCategory GroupWithZeroCat
    where
  forget := ⟨coeSort, fun X Y => coeFn, fun X => rfl, fun X Y Z f g => rfl⟩
  forget_faithful := ⟨fun X Y f g h => FunLike.coe_injective h⟩

instance hasForgetToBipointed : HasForget₂ GroupWithZeroCat Bipointed
    where forget₂ :=
    { obj := fun X => ⟨X, 0, 1⟩
      map := fun X Y f => ⟨f, f.map_zero', f.map_one'⟩ }
#align GroupWithZero.has_forget_to_Bipointed GroupWithZeroCat.hasForgetToBipointed

instance hasForgetToMon : HasForget₂ GroupWithZeroCat MonCat
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y => MonoidWithZeroHom.toMonoidHom }
#align GroupWithZero.has_forget_to_Mon GroupWithZeroCat.hasForgetToMon

/-- Constructs an isomorphism of groups with zero from a group isomorphism between them. -/
@[simps]
def Iso.mk {α β : GroupWithZeroCat.{u}} (e : α ≃* β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply _
#align GroupWithZero.iso.mk GroupWithZeroCat.Iso.mk

end GroupWithZeroCat

