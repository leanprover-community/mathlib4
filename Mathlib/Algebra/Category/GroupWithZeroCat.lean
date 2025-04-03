/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.Algebra.GroupWithZero.WithZero
import Mathlib.CategoryTheory.Category.Bipointed

#align_import algebra.category.GroupWithZero from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

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

instance : CoeSort GroupWithZeroCat Type* :=
  Bundled.coeSort

instance (X : GroupWithZeroCat) : GroupWithZero X :=
  X.str

/-- Construct a bundled `GroupWithZeroCat` from a `GroupWithZero`. -/
def of (α : Type*) [GroupWithZero α] : GroupWithZeroCat :=
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

instance {M N : GroupWithZeroCat} : FunLike (M ⟶ N) M N :=
  ⟨fun f => f.toFun, fun f g h => by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective'
    exact h⟩

-- Porting note (#10756): added lemma
lemma coe_id {X : GroupWithZeroCat} : (𝟙 X : X → X) = id := rfl

-- Porting note (#10756): added lemma
lemma coe_comp {X Y Z : GroupWithZeroCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

instance groupWithZeroConcreteCategory : ConcreteCategory GroupWithZeroCat where
  forget :=
  { obj := fun G => G
    map := fun f => f.toFun }
  forget_faithful := ⟨fun h => DFunLike.coe_injective h⟩

-- porting note (#10756): added lemma
@[simp] lemma forget_map {X Y : GroupWithZeroCat} (f : X ⟶ Y) :
  (forget GroupWithZeroCat).map f = f := rfl

instance hasForgetToBipointed : HasForget₂ GroupWithZeroCat Bipointed where
  forget₂ :=
      { obj := fun X => ⟨X, 0, 1⟩
        map := fun f => ⟨f, f.map_zero', f.map_one'⟩ }
set_option linter.uppercaseLean3 false in
#align GroupWithZero.has_forget_to_Bipointed GroupWithZeroCat.hasForgetToBipointed

instance hasForgetToMon : HasForget₂ GroupWithZeroCat MonCat where
  forget₂ :=
      { obj := fun X => ⟨ X , _ ⟩
        map := fun f => f.toMonoidHom }
set_option linter.uppercaseLean3 false in
#align GroupWithZero.has_forget_to_Mon GroupWithZeroCat.hasForgetToMon

/-- Constructs an isomorphism of groups with zero from a group isomorphism between them. -/
@[simps]
def Iso.mk {α β : GroupWithZeroCat.{u}} (e : α ≃* β) : α ≅ β where
  hom := (e : α →*₀ β)
  inv := (e.symm : β →*₀ α)
  hom_inv_id := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id := by
    ext
    exact e.apply_symm_apply _
set_option linter.uppercaseLean3 false in
#align GroupWithZero.iso.mk GroupWithZeroCat.Iso.mk

end GroupWithZeroCat
