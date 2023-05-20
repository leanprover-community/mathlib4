/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module algebra.category.GroupWithZero
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Category.Bipointed
import Mathlib.Algebra.Category.MonCat.Basic

/-!
# The category of groups with zero

This file defines `GroupWithZeroCat`, the category of groups with zero.
-/


universe u

open CategoryTheory Order

/-- The category of groups with zero. -/
def GroupWithZeroCat :=
  Bundled GroupWithZero
set_option linter.uppercaseLean3 false in
#align GroupWithZero GroupWithZeroCat

namespace GroupWithZeroCat

instance : CoeSort GroupWithZeroCat (Type _) :=
  Bundled.coeSort

instance (X : GroupWithZeroCat) : GroupWithZero X :=
  X.str

/-- Construct a bundled `GroupWithZeroCat` from a `GroupWithZero`. -/
def of (α : Type _) [GroupWithZero α] : GroupWithZeroCat :=
  Bundled.of α
set_option linter.uppercaseLean3 false in
#align GroupWithZero.of GroupWithZeroCat.of

instance : Inhabited GroupWithZeroCat :=
  ⟨of (WithZero PUnit)⟩

instance : LargeCategory.{u} GroupWithZeroCat where
  Hom X Y := MonoidWithZeroHom X Y
  id X := MonoidWithZeroHom.id X
  comp f g := g.comp f
  id_comp := MonoidWithZeroHom.comp_id
  comp_id := MonoidWithZeroHom.id_comp
  assoc _ _ _ := MonoidWithZeroHom.comp_assoc _ _ _

-- porting note: was not necessary in mathlib
instance {M N : GroupWithZeroCat} : FunLike (M ⟶ N) M (fun _ => N) :=
  ⟨ fun f => f.toFun, fun f g h => by
    cases f
    cases g
    congr
    apply FunLike.coe_injective'
    exact h
     ⟩

-- porting note: added
lemma coeId {X : GroupWithZeroCat} : (𝟙 X : X → X) = id := rfl

-- porting note: added
lemma coeComp {X Y Z : GroupWithZeroCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

instance groupWithZeroConcreteCategory : ConcreteCategory GroupWithZeroCat where
  forget := { obj := fun G => G
              map := fun f => f.toFun }
  forget_faithful := ⟨ fun h => FunLike.coe_injective h ⟩

-- porting note: added
@[simp] lemma forget_map (f : X ⟶ Y) : (forget GroupWithZeroCat).map f = f := rfl


instance hasForgetToBipointed : HasForget₂ GroupWithZeroCat Bipointed
    where forget₂ :=
      { obj := fun X => ⟨X, 0, 1⟩
        map := fun f => ⟨f, f.map_zero', f.map_one'⟩
        }
set_option linter.uppercaseLean3 false in
#align GroupWithZero.has_forget_to_Bipointed GroupWithZeroCat.hasForgetToBipointed

instance hasForgetToMon : HasForget₂ GroupWithZeroCat MonCat
    where forget₂ :=
      { obj := fun X => ⟨ X , _ ⟩
        map := fun f => f.toMonoidHom }
set_option linter.uppercaseLean3 false in
#align GroupWithZero.has_forget_to_Mon GroupWithZeroCat.hasForgetToMon

-- porting note: this instance was not necessary in mathlib
instance {X Y : GroupWithZeroCat} : CoeFun (X ⟶ Y) fun _ => X → Y where
  coe (f : X →*₀ Y) := f

/-- Conversion from MulEquiv to MonoidWithZeroHom -/
-- porting note : this function was not necessary in mathlib
def toMonoidWithZeroHom {M N} [GroupWithZero M] [GroupWithZero N] (h : M ≃* N) : M →*₀ N :=
  {
    toFun := h.toFun
    map_mul' := h.map_mul'
    map_one' := h.map_one
    map_zero' := by
       rw [← mul_eq_zero_of_left rfl 1]
       rw [h.map_mul' 0 1]
       simp only [MulEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe_apply, MulEquiv.coe_toEquiv,
         map_zero, map_one, mul_one]
   }

/-- Constructs an isomorphism of groups with zero from a group isomorphism between them. -/
@[simps]
def Iso.mk {α β : GroupWithZeroCat.{u}} (e : α ≃* β) : α ≅ β where
  hom := toMonoidWithZeroHom e
  inv := toMonoidWithZeroHom (e.symm)
  hom_inv_id := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id := by
    ext
    exact e.apply_symm_apply _
set_option linter.uppercaseLean3 false in
#align GroupWithZero.iso.mk GroupWithZeroCat.Iso.mk

end GroupWithZeroCat
