/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Kim Morrison, Simon Hudon
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.CategoryTheory.Groupoid

/-!
# Endomorphisms

Definition and basic properties of endomorphisms and automorphisms of an object in a category.

For each `X : C`, we define a monoid `CategoryTheory.End X` which a `1`-field structure
that is equipped with a bijection with `X ⟶ X`. Similarly, we define the
group `CategoryTheory.Aut X`, which is equipped with a bijection with `X ≅ X`.

-/

@[expose] public section


universe v v' u u'

namespace CategoryTheory

/-- Endomorphisms of an object in a category. Arguments order in multiplication agrees with
`Function.comp`, not with `CategoryTheory.CategoryStruct.comp`. -/
@[ext]
structure End {C : Type u} [CategoryStruct.{v} C] (X : C) where of ::
  /-- the underlying morphism of an endomorphism -/
  asHom : X ⟶ X

namespace End

section Struct

variable {C : Type u} [CategoryStruct.{v} C] (X : C)

variable {X} in
/-- The bijection `End X ≃ (X ⟶ X)`. -/
@[implicit_reducible, simps]
def homEquiv : End X ≃ (X ⟶ X) where
  toFun := asHom
  invFun := of

@[simps]
protected instance : One (End X) := ⟨.of (𝟙 X)⟩

protected instance inhabited : Inhabited (End X) := ⟨.of (𝟙 X)⟩

/-- Multiplication of endomorphisms agrees with `Function.comp`, not with
`CategoryTheory.CategoryStruct.comp`. -/
@[simps]
protected instance : Mul (End X) where
  mul f g := .of (g.asHom ≫ f.asHom)

variable {X}

@[deprecated (since := "2026-09-12")] alias one_def := one_asHom
@[deprecated (since := "2026-09-12")] alias mul_def := mul_asHom

end Struct

/-- Endomorphisms of an object form a monoid -/
instance monoid {C : Type u} [Category.{v} C] {X : C} : Monoid (End X) where
  mul_one := by cat_disch
  one_mul := by cat_disch
  mul_assoc := by cat_disch

section MulAction

variable {C : Type u} [Category.{v} C]

instance {X Y : C} : SMul (End Y) (X ⟶ Y) where
  smul r f := f ≫ r.asHom

instance {X Y : C} : SMul (End X)ᵐᵒᵖ (X ⟶ Y) where
  smul r f := r.unop.asHom ≫ f

@[local simp]
theorem smul_right {X Y : C} {r : End Y} {f : X ⟶ Y} : r • f = f ≫ r.asHom :=
  rfl

@[local simp]
theorem smul_left {X Y : C} {r : (End X)ᵐᵒᵖ} {f : X ⟶ Y} : r • f = r.unop.asHom ≫ f :=
  rfl

instance mulActionRight {X Y : C} : MulAction (End Y) (X ⟶ Y) where
  one_smul := by cat_disch
  mul_smul _ _ _ :=  by cat_disch

instance mulActionLeft {X Y : C} : MulAction (End X)ᵐᵒᵖ (X ⟶ Y) where
  one_smul := by cat_disch
  mul_smul _ _ _ := by cat_disch

end MulAction

/-- In a groupoid, endomorphisms form a group -/
instance group {C : Type u} [Groupoid.{v} C] (X : C) : Group (End X) where
  inv f := .of (Groupoid.inv f.asHom)
  inv_mul_cancel f := by cat_disch

end End

theorem isUnit_iff_isIso {C : Type u} [Category.{v} C] {X : C} (f : End X) :
    IsUnit (f : End X) ↔ IsIso f.asHom :=
  ⟨fun h ↦ ⟨h.unit.inv.asHom, congr($(h.unit.inv_val).asHom), congr($(h.unit.val_inv).asHom)⟩,
    fun h ↦ ⟨⟨f, .of (inv f.asHom), by cat_disch, by cat_disch⟩, rfl⟩⟩

variable {C : Type u} [Category.{v} C] (X : C)

/-- Automorphisms of an object in a category.

The order of arguments in multiplication agrees with
`Function.comp`, not with `CategoryTheory.CategoryStruct.comp`.
-/
@[ext]
structure Aut (X : C) where of ::
  /-- the underlying isomorphism of an automorphism -/
  asIso : X ≅ X

namespace Aut

/-- The bijection `Aut X ≃ (X ≅ X)`. -/
@[implicit_reducible, simps]
def isoEquiv {X : C} : Aut X ≃ (X ≅ X) where
  toFun := asIso
  invFun := of

protected instance inhabited : Inhabited (Aut X) := ⟨.of (Iso.refl X)⟩

@[simps]
instance : One (Aut X) where
  one := .of (Iso.refl X)

@[simps]
instance : Inv (Aut X) where
  inv e := .of (e.asIso.symm)

@[simps]
instance : Mul (Aut X) where
  mul x y := .of (y.asIso.trans x.asIso)

instance : Group (Aut X) where
  mul_assoc := by cat_disch
  one_mul := by cat_disch
  mul_one := by cat_disch
  inv_mul_cancel := by cat_disch

@[deprecated (since := "2026-09-12")] alias Aut_mul_def := mul_asIso
@[deprecated (since := "2026-09-12")] alias Aut_inv_def := inv_asIso

/-- The inclusion of `Aut X` to `End X` as a monoid homomorphism. -/
@[simps!]
def toEnd (X : C) : Aut X →* End X where
  toFun e := .of e.asIso.hom
  map_one' := by cat_disch
  map_mul' := by cat_disch

/-- Units in the monoid of endomorphisms of an object
are (multiplicatively) equivalent to automorphisms of that object.
-/
@[simps]
def unitsEndEquivAut : (End X)ˣ ≃* Aut X where
  toFun f := .of
    { hom := f.val.asHom
      inv := f.inv.asHom
      hom_inv_id := congr($(f.inv_val).asHom)
      inv_hom_id := congr($(f.val_inv).asHom) }
  invFun f :=
    { val := .of f.asIso.hom
      inv := .of f.asIso.inv
      val_inv := by cat_disch
      inv_val := by cat_disch }
  map_mul' f g := by cat_disch

/-- Isomorphisms induce isomorphisms of the automorphism group -/
@[simps]
def autMulEquivOfIso {X Y : C} (h : X ≅ Y) : Aut X ≃* Aut Y where
  toFun e := .of (h.symm ≪≫ e.asIso ≪≫ h)
  invFun e := .of (h ≪≫ e.asIso ≪≫ h.symm)
  left_inv := by cat_disch
  right_inv := by cat_disch
  map_mul' := by cat_disch

end Aut

namespace Functor

variable {D : Type u'} [Category.{v'} D] (f : C ⥤ D)

/-- `f.map` as a monoid hom between endomorphism monoids. -/
@[simps]
def mapEnd : End X →* End (f.obj X) where
  toFun e := .of (f.map e.asHom)
  map_mul' := by cat_disch
  map_one' := by cat_disch

/-- `f.mapIso` as a group hom between automorphism groups. -/
def mapAut : Aut X →* Aut (f.obj X) where
  toFun e := .of (f.mapIso e.asIso)
  map_mul' := by cat_disch
  map_one' := by cat_disch

namespace FullyFaithful

variable {f}
variable (hf : FullyFaithful f)

/-- `mulEquivEnd` as an isomorphism between endomorphism monoids. -/
@[simps!]
noncomputable def mulEquivEnd (X : C) :
    End X ≃* End (f.obj X) where
  toEquiv := End.homEquiv.trans (hf.homEquiv.trans End.homEquiv.symm)
  map_mul' := by cat_disch

/-- `mulEquivAut` as an isomorphism between automorphism groups. -/
@[simps!]
noncomputable def autMulEquivOfFullyFaithful (X : C) :
    Aut X ≃* Aut (f.obj X) where
  toEquiv := Aut.isoEquiv.trans (hf.isoEquiv.trans Aut.isoEquiv.symm)
  map_mul' := by cat_disch

end FullyFaithful

end Functor

/-- The multiplicative bijection `End X ≃* End (F X)` when `X : InducedCategory C F`. -/
@[simps!]
def InducedCategory.endEquiv {D : Type*} {F : D → C}
    {X : InducedCategory C F} : End X ≃* End (F X) where
  toEquiv := End.homEquiv.trans (InducedCategory.homEquiv.trans End.homEquiv.symm)
  map_mul' := by cat_disch

end CategoryTheory
