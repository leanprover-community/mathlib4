/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.Algebra.GroupWithZero.WithZero
import Mathlib.CategoryTheory.Category.Bipointed
import Mathlib.CategoryTheory.ConcreteCategory.Bundled

/-!
# The category of groups with zero

This file defines `GrpWithZero`, the category of groups with zero.
-/

universe u

open CategoryTheory

/-- The category of groups with zero. -/
def GrpWithZero :=
  Bundled GroupWithZero

namespace GrpWithZero

instance : CoeSort GrpWithZero Type* :=
  Bundled.coeSort

instance (X : GrpWithZero) : GroupWithZero X :=
  X.str

/-- Construct a bundled `GrpWithZero` from a `GroupWithZero`. -/
def of (α : Type*) [GroupWithZero α] : GrpWithZero :=
  Bundled.of α

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

instance groupWithZeroHasForget : HasForget GrpWithZero where
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

instance hasForgetToMon : HasForget₂ GrpWithZero MonCat where
  forget₂ :=
      { obj := fun X => MonCat.of X
        map := fun f => MonCat.ofHom f.toMonoidHom }

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

end GrpWithZero
