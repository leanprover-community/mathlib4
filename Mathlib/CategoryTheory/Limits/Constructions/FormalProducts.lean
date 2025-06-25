/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Kenny Lau
-/

import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Formal Products and Coproducts

In this file we construct the category of formal products (and dually, formal coproducts) given
a category.

## Main definitions

* `FormalProduct`: the category of formal products, which are indexed sets of objects in a category.
  A morphism `∏ i : X.I, X.obj i ⟶ ∏ j : Y.I, Y.obj j` is given by a function `f : Y.I → X.I` and
  maps `X.obj (f i) ⟶ Y.obj i` for each `i : Y.I`.
* `FormalProduct.eval : (C ⥤ A) ⥤ (FormalProduct C ⥤ A)`: the universal property that
  a copresheaf on `C` where the target category has arbitrary products, can be extended to
  a copresheaf on `FormalProduct C`.
* `FormalCoproduct`: the category of formal coproducts, which are indexed sets of objects in a
  category. A morphism `∐ i : X.I, X.obj i ⟶ ∐ j : Y.I, Y.obj j` is given by a function
  `f : X.I → Y.I` and maps `X.obj i ⟶ Y.obj (f i)` for each `i : X.I`.
* `FormalCoproduct.eval : (Cᵒᵖ ⥤ A) ⥤ ((FormalCoproduct C)ᵒᵖ ⥤ A)`:
  the universal property that a presheaf on `C` where the target category has arbitrary coproducts,
  can be extended to a presheaf on `FormalCoproduct C`.

-/


universe v v₁ v₂ v₃ w w₁ w₂ w₃ u u₁ u₂ u₃

open Opposite

namespace CategoryTheory

namespace Limits

variable {C : Type u} [Category.{v} C] (A : Type u₁) [Category.{v₁} A]
  [∀ (I : Type w), HasProductsOfShape I A]

variable (C) in
/-- A formal product is an indexed set of objects. -/
structure FormalProduct where
  I : Type w
  obj (i : I) : C

variable (C) in
/-- A formal coproduct is an indexed set of objects. -/
structure FormalCoproduct where
  I : Type w
  obj (i : I) : C

namespace FormalProduct

structure Hom (X Y : FormalProduct.{w} C) where
  f : Y.I → X.I
  φ (i : Y.I) : X.obj (f i) ⟶ Y.obj i

-- this category identifies to the fullsubcategory of the category of
-- copresheaves of sets on `C` which are products of corepresentable presheaves
@[simps!] instance category : Category (FormalProduct.{w} C) where
  Hom := Hom
  id X := { f := id, φ := fun _ ↦ 𝟙 _ }
  comp α β := { f := α.f ∘ β.f, φ := fun _ ↦ α.φ _ ≫ β.φ _ }

@[ext (iff := false)]
lemma hom_ext {X Y : FormalProduct.{w} C} {f g : X ⟶ Y} (h₁ : f.f = g.f)
    (h₂ : ∀ (i : Y.I), eqToHom (by rw [h₁]) ≫ f.φ i = g.φ i) : f = g := by
  obtain ⟨f, F⟩ := f
  obtain ⟨g, G⟩ := g
  obtain rfl : f = g := h₁
  obtain rfl : F = G := by ext i; simpa using h₂ i
  rfl

lemma hom_ext_iff {X Y : FormalProduct.{w} C} (f g : X ⟶ Y) :
    f = g ↔ ∃ h₁ : f.f = g.f, ∀ (i : Y.I), eqToHom (by rw [h₁]) ≫ f.φ i = g.φ i :=
  ⟨(· ▸ by simp), fun ⟨h₁, h₂⟩ ↦ hom_ext h₁ h₂⟩

@[simps] noncomputable def eval : (C ⥤ A) ⥤ (FormalProduct.{w} C ⥤ A) where
  obj F := {
    obj X := ∏ᶜ fun (i : X.I) ↦ F.obj (X.obj i)
    map f := Pi.lift fun i ↦ Pi.π _ (f.f i) ≫ F.map (f.φ i)
  }
  map α := {
    app f := Pi.map fun i ↦ α.app _
  }

end FormalProduct


namespace FormalCoproduct

structure Hom (X Y : FormalCoproduct.{w} C) where
  f : X.I → Y.I
  φ (i : X.I) : X.obj i ⟶ Y.obj (f i)

-- this category identifies to the fullsubcategory of the category of
-- presheaves of sets on `C` which are coproducts of representable presheaves
@[simps!] instance category : Category (FormalCoproduct.{w} C) where
  Hom := Hom
  id X := { f := id, φ := fun _ ↦ 𝟙 _ }
  comp α β := { f := β.f ∘ α.f, φ := fun _ ↦ α.φ _ ≫ β.φ _ }

@[ext (iff := false)]
lemma hom_ext {X Y : FormalCoproduct.{w} C} {f g : X ⟶ Y} (h₁ : f.f = g.f)
    (h₂ : ∀ (i : X.I), f.φ i ≫ eqToHom (by rw [h₁]) = g.φ i) : f = g := by
  obtain ⟨f, F⟩ := f
  obtain ⟨g, G⟩ := g
  obtain rfl : f = g := h₁
  obtain rfl : F = G := by ext i; simpa using h₂ i
  rfl

@[simps] noncomputable def eval : (Cᵒᵖ ⥤ A) ⥤ ((FormalCoproduct.{w} C)ᵒᵖ ⥤ A) where
  obj F := {
    obj X := ∏ᶜ fun (i : X.unop.I) ↦ F.obj (op (X.unop.obj i))
    map f := Pi.lift fun i ↦ Pi.π _ (f.unop.f i) ≫ F.map (f.unop.φ i).op
  }
  map α := {
    app f := Pi.map fun i ↦ α.app (op (f.unop.obj i))
  }

end FormalCoproduct


end Limits

end CategoryTheory
