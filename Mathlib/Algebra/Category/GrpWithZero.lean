/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Category.MonCat.Basic
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.CategoryTheory.Category.Bipointed
public import Mathlib.Algebra.GroupWithZero.Equiv
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Util.CompileInductive

/-!
# The category of groups with zero

This file defines `GrpWithZero`, the category of groups with zero.
-/

@[expose] public section

assert_not_exists Ring

universe u

open CategoryTheory

/-- The category of groups with zero. -/
structure GrpWithZero where
  /-- Construct a bundled `GrpWithZero` from a `GroupWithZero`. -/
  of ::
  /-- The underlying group with zero. -/
  carrier : Type*
  [str : GroupWithZero carrier]

attribute [instance] GrpWithZero.str

namespace GrpWithZero

instance : CoeSort GrpWithZero Type* :=
  ⟨carrier⟩

instance : Inhabited GrpWithZero :=
  ⟨of (WithZero PUnit)⟩

instance : LargeCategory.{u} GrpWithZero where
  Hom X Y := MonoidWithZeroHom X Y
  id X := MonoidWithZeroHom.id X
  comp f g := g.comp f

instance groupWithZeroConcreteCategory : ConcreteCategory GrpWithZero (MonoidWithZeroHom · ·) where
  hom f := f
  ofHom f := f

/-- Typecheck a `MonoidWithZeroHom` as a morphism in `GrpWithZero`. -/
abbrev ofHom {X Y : Type u} [GroupWithZero X] [GroupWithZero Y]
    (f : MonoidWithZeroHom X Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom f

@[simp]
lemma hom_id {X : GrpWithZero} : ConcreteCategory.hom (𝟙 X : X ⟶ X) = MonoidWithZeroHom.id X := rfl

@[simp]
lemma hom_comp {X Y Z : GrpWithZero} {f : X ⟶ Y} {g : Y ⟶ Z} :
    ConcreteCategory.hom (f ≫ g) = g.comp f := rfl

lemma coe_id {X : GrpWithZero} : (𝟙 X : X → X) = id := rfl

lemma coe_comp {X Y Z : GrpWithZero} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[simp] lemma forget_map {X Y : GrpWithZero} (f : X ⟶ Y) :
    (forget GrpWithZero).map f = (f : _ → _) :=
  rfl

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
  hom := ofHom e
  inv := ofHom e.symm
  hom_inv_id := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id := by
    ext
    exact e.apply_symm_apply _

end GrpWithZero
