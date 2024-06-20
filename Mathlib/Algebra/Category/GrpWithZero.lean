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

This file defines `GrpWithZero`, the category of groups with zero.
-/

universe u

open CategoryTheory Order

/-- The category of groups with zero. -/
def GrpWithZero :=
  Bundled GroupWithZero
set_option linter.uppercaseLean3 false in
#align GroupWithZero GrpWithZero

namespace GrpWithZero

instance : CoeSort GrpWithZero Type* :=
  Bundled.coeSort

instance (X : GrpWithZero) : GroupWithZero X :=
  X.str

/-- Construct a bundled `GrpWithZero` from a `GroupWithZero`. -/
def of (α : Type*) [GroupWithZero α] : GrpWithZero :=
  Bundled.of α
set_option linter.uppercaseLean3 false in
#align GroupWithZero.of GrpWithZero.of

instance : Inhabited GrpWithZero :=
  ⟨of (WithZero PUnit)⟩

instance : LargeCategory.{u} GrpWithZero where
  Hom X Y := MonoidWithZeroHom X Y
  id X := MonoidWithZeroHom.id X
  comp f g := g.comp f
  id_comp := MonoidWithZeroHom.comp_id
  comp_id := MonoidWithZeroHom.id_comp
  assoc _ _ _ := MonoidWithZeroHom.comp_assoc _ _ _

instance {M N : GrpWithZero} : FunLike (M ⟶ N) M N :=
  ⟨fun f => f.toFun, fun f g h => by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective'
    exact h⟩

lemma coe_id {X : GrpWithZero} : (𝟙 X : X → X) = id := rfl

lemma coe_comp {X Y Z : GrpWithZero} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

instance groupWithZeroConcreteCategory : ConcreteCategory GrpWithZero where
  forget :=
  { obj := fun G => G
    map := fun f => f.toFun }
  forget_faithful := ⟨fun h => DFunLike.coe_injective h⟩

@[simp] lemma forget_map {X Y : GrpWithZero} (f : X ⟶ Y) :
  (forget GrpWithZero).map f = f := rfl

instance hasForgetToBipointed : HasForget₂ GrpWithZero Bipointed where
  forget₂ :=
      { obj := fun X => ⟨X, 0, 1⟩
        map := fun f => ⟨f, f.map_zero', f.map_one'⟩ }
set_option linter.uppercaseLean3 false in
#align GroupWithZero.has_forget_to_Bipointed GrpWithZero.hasForgetToBipointed

instance hasForgetToMon : HasForget₂ GrpWithZero MonCat where
  forget₂ :=
      { obj := fun X => ⟨ X , _ ⟩
        map := fun f => f.toMonoidHom }
set_option linter.uppercaseLean3 false in
#align GroupWithZero.has_forget_to_Mon GrpWithZero.hasForgetToMon

/-- Constructs an isomorphism of groups with zero from a group isomorphism between them. -/
@[simps]
def Iso.mk {α β : GrpWithZero.{u}} (e : α ≃* β) : α ≅ β where
  hom := (e : α →*₀ β)
  inv := (e.symm : β →*₀ α)
  hom_inv_id := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id := by
    ext
    exact e.apply_symm_apply _
set_option linter.uppercaseLean3 false in
#align GroupWithZero.iso.mk GrpWithZero.Iso.mk

end GrpWithZero
