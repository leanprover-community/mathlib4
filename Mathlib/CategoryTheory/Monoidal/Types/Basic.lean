/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# The category of types is a (symmetric) monoidal category
-/

@[expose] public section


open CategoryTheory Limits MonoidalCategory

universe v u

namespace CategoryTheory

instance typesCartesianMonoidalCategory : CartesianMonoidalCategory (TypeCat.{u}) :=
  .ofChosenFiniteProducts Types.terminalLimitCone Types.binaryProductLimitCone

unif_hint tensor_eq_prod {X X' Y Y' : TypeCat.{u}} where
  X ≟ X'
  Y ≟ Y' ⊢
  X ⊗ Y ≟ X × Y

instance : BraidedCategory (TypeCat.{u}) := .ofCartesianMonoidalCategory

theorem types_tensorObj_def {X Y : TypeCat.{u}} : X ⊗ Y = (X × Y) := rfl

theorem types_tensorUnit_def : 𝟙_ (TypeCat.{u}) = PUnit := rfl

@[simp]
theorem tensor_apply {W X Y Z : TypeCat.{u}} (f : W ⟶ X) (g : Y ⟶ Z) (p : (W ⊗ Y : TypeCat)) :
    (f ⊗ₘ g) p = (f p.1, g p.2) :=
  rfl

@[simp]
theorem whiskerLeft_apply (X : TypeCat.{u}) {Y Z : TypeCat.{u}} (f : Y ⟶ Z)
    (p : (X ⊗ Y : TypeCat)) : (X ◁ f) p = (p.1, f p.2) :=
  rfl

@[simp]
theorem whiskerRight_apply {Y Z : TypeCat.{u}} (f : Y ⟶ Z) (X : TypeCat.{u})
    (p : (Y ⊗ X : TypeCat)) : (f ▷ X) p = (f p.1, p.2) :=
  rfl

@[simp]
theorem leftUnitor_hom_apply {X : TypeCat.{u}} {x : X} {p : PUnit} :
    ((λ_ X).hom : 𝟙_ (TypeCat.{u}) ⊗ X ⟶ X) (p, x) = x :=
  rfl

@[simp]
theorem leftUnitor_inv_apply {X : TypeCat.{u}} {x : X} :
    ((λ_ X).inv : X ⟶ 𝟙_ (TypeCat.{u}) ⊗ X) x = (PUnit.unit, x) :=
  rfl

@[simp]
theorem rightUnitor_hom_apply {X : TypeCat.{u}} {x : X} {p : PUnit} :
    ((ρ_ X).hom : X ⊗ 𝟙_ (TypeCat.{u}) ⟶ X) (x, p) = x :=
  rfl

@[simp]
theorem rightUnitor_inv_apply {X : TypeCat.{u}} {x : X} :
    ((ρ_ X).inv : X ⟶ X ⊗ 𝟙_ (TypeCat.{u})) x = (x, PUnit.unit) :=
  rfl

@[simp]
theorem associator_hom_apply {X Y Z : TypeCat.{u}} {x : X} {y : Y} {z : Z} :
    ((α_ X Y Z).hom : (X ⊗ Y) ⊗ Z ⟶ X ⊗ Y ⊗ Z) ((x, y), z) = (x, (y, z)) :=
  rfl

@[simp]
theorem associator_inv_apply {X Y Z : TypeCat.{u}} {x : X} {y : Y} {z : Z} :
    ((α_ X Y Z).inv : X ⊗ Y ⊗ Z ⟶ (X ⊗ Y) ⊗ Z) (x, (y, z)) = ((x, y), z) :=
  rfl

@[simp] theorem associator_hom_apply_1 {X Y Z : TypeCat.{u}} {x} :
    (((α_ X Y Z).hom : (X ⊗ Y) ⊗ Z ⟶ X ⊗ Y ⊗ Z) x).1 = x.1.1 :=
  rfl

@[simp] theorem associator_hom_apply_2_1 {X Y Z : TypeCat.{u}} {x} :
    (((α_ X Y Z).hom : (X ⊗ Y) ⊗ Z ⟶ X ⊗ Y ⊗ Z) x).2.1 = x.1.2 :=
  rfl

@[simp] theorem associator_hom_apply_2_2 {X Y Z : TypeCat.{u}} {x} :
    (((α_ X Y Z).hom : (X ⊗ Y) ⊗ Z ⟶ X ⊗ Y ⊗ Z) x).2.2 = x.2 :=
  rfl

@[simp] theorem associator_inv_apply_1_1 {X Y Z : TypeCat.{u}} {x} :
    (((α_ X Y Z).inv : X ⊗ Y ⊗ Z ⟶ (X ⊗ Y) ⊗ Z) x).1.1 = x.1 :=
  rfl

@[simp] theorem associator_inv_apply_1_2 {X Y Z : TypeCat.{u}} {x} :
    (((α_ X Y Z).inv : X ⊗ Y ⊗ Z ⟶ (X ⊗ Y) ⊗ Z) x).1.2 = x.2.1 :=
  rfl

@[simp] theorem associator_inv_apply_2 {X Y Z : TypeCat.{u}} {x} :
    (((α_ X Y Z).inv : X ⊗ Y ⊗ Z ⟶ (X ⊗ Y) ⊗ Z) x).2 = x.2.2 :=
  rfl

@[simp]
theorem braiding_hom_apply {X Y : TypeCat.{u}} {x : X} {y : Y} :
    ((β_ X Y).hom : X ⊗ Y ⟶ Y ⊗ X) (x, y) = (y, x) :=
  rfl

@[simp]
theorem braiding_inv_apply {X Y : TypeCat.{u}} {x : X} {y : Y} :
    ((β_ X Y).inv : Y ⊗ X ⟶ X ⊗ Y) (y, x) = (x, y) :=
  rfl

@[simp]
theorem CartesianMonoidalCategory.lift_apply {X Y Z : TypeCat.{u}} {f : X ⟶ Y} {g : X ⟶ Z} {x : X} :
    lift f g x = (f x, g x) :=
  rfl

-- We don't yet have an API for tensor products indexed by finite ordered types,
-- but it would be nice to state how monoidal functors preserve these.
/-- If `F` is a monoidal functor out of `Type`, it takes the (n+1)st Cartesian power
of a type to the image of that type, tensored with the image of the nth Cartesian power. -/
noncomputable def MonoidalFunctor.mapPi {C : Type*} [Category* C] [MonoidalCategory C]
    (F : TypeCat ⥤ C) [F.Monoidal] (n : ℕ) (β : Type*) :
    F.obj ((Fin (n + 1) → β)) ≅ F.obj (β) ⊗ F.obj ((Fin n → β)) :=
  Functor.mapIso _ (Fin.consEquiv _).symm.toIso ≪≫
    (Functor.Monoidal.μIso F (β) ((Fin n → β))).symm

end CategoryTheory
