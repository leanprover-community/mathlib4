/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Bicategory.Basic

/-!
# `eqToHom` in bicategories

This file records some of the behavior of `eqToHom` 1-morphisms and
2-morphisms in bicategories.

Given an equality of objects `h : x = y` in a bicategory, there is a 1-morphism
`eqToHom h : x ⟶ y` just like in an ordinary category. The definitional property
of this morphism is that if `h : x = x`, `eqToHom h = 𝟙 x`. This is
implemented as the `eqToHom` morphism in the `CategoryStruct` underlying the
bicategory.

Unlike the situation in ordinary category theory, these 1-morphisms do not
compose strictly: `eqToHom h.trans h'` is merely isomorphic to
`eqToHom h ≫ eqToHom h'`. We define this isomorphism as
`CategoryTheory.Bicategory.eqToHomTransIso`.

Given an equality of 1-morphisms, we show that various bicategorical
structure morphisms such as unitors, associators and whiskering conjugate
well under `eqToHom`s.

## TODO
* Define `eqToEquiv` that puts the `eqToHom`s in an `Equivalence` between
  objects.
-/

universe w v u

namespace CategoryTheory.Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

/-- In a bicategory, `eqToHom`s do not compose strictly,
but they do up to isomorphism. -/
def eqToHomTransIso {x y z : B} (e₁ : x = y) (e₂ : y = z) :
    eqToHom (e₁.trans e₂) ≅ eqToHom e₁ ≫ eqToHom e₂ :=
  e₂ ▸ e₁ ▸ (λ_ (𝟙 x)).symm

@[simp]
lemma eqToHomTransIso_refl_refl (x : B) :
    eqToHomTransIso (rfl : x = x) rfl = (λ_ (𝟙 x)).symm :=
  rfl

lemma eqToHomTransIso_refl_right {x y : B} (e₁ : x = y) :
    eqToHomTransIso e₁ rfl = (ρ_ (eqToHom e₁)).symm := by
  ext
  subst e₁
  simp

lemma eqToHomTransIso_refl_left {x y : B} (e₁ : x = y) :
    eqToHomTransIso rfl e₁ = (λ_ (eqToHom e₁)).symm := by
  ext
  subst e₁
  simp

@[reassoc]
lemma associator_eqToHom_hom {x y z t : B}
    (e₁ : x = y) (e₂ : y = z) (e₃ : z = t) :
    (α_ (eqToHom e₁) (eqToHom e₂) (eqToHom e₃)).hom =
    (eqToHomTransIso e₁ e₂).inv ▷ eqToHom e₃ ≫
      (eqToHomTransIso (e₁.trans e₂) e₃).inv ≫
      (eqToHomTransIso e₁ (e₂.trans e₃)).hom ≫
      eqToHom e₁ ◁ (eqToHomTransIso e₂ e₃).hom := by
  subst_vars
  simp

@[reassoc]
lemma associator_eqToHom_inv {x y z t : B}
    (e₁ : x = y) (e₂ : y = z) (e₃ : z = t) :
    (α_ (eqToHom e₁) (eqToHom e₂) (eqToHom e₃)).inv =
    eqToHom e₁ ◁ (eqToHomTransIso e₂ e₃).inv ≫
      (eqToHomTransIso e₁ (e₂.trans e₃)).inv ≫
      (eqToHomTransIso (e₁.trans e₂) e₃).hom ≫
      (eqToHomTransIso e₁ e₂).hom ▷ eqToHom e₃ := by
  subst_vars
  simp

lemma associator_hom_congr {x y z t : B} {f f' : x ⟶ y} {g g' : y ⟶ z}
    {h h' : z ⟶ t} (ef : f = f') (eg : g = g') (eh : h = h') :
    (α_ f g h).hom =
    eqToHom (by grind) ≫ (α_ f' g' h').hom ≫ eqToHom (by grind) := by
  subst_vars
  simp

lemma associator_inv_congr {x y z t : B} {f f' : x ⟶ y} {g g' : y ⟶ z}
    {h h' : z ⟶ t} (ef : f = f') (eg : g = g') (eh : h = h') :
    (α_ f g h).inv =
    eqToHom (by grind) ≫ (α_ f' g' h').inv ≫ eqToHom (by grind) := by
  subst_vars
  simp

lemma congr_whiskerLeft {x y : B} {f f' : x ⟶ y} (h : f = f') {z : B}
    {g g' : y ⟶ z} (η : g ⟶ g') :
      f ◁ η = eqToHom (by rw [h]) ≫ f' ◁ η ≫ eqToHom (by rw [h]) := by
  subst h
  simp

lemma whiskerRight_congr {y z : B} {g g' : y ⟶ z} (h : g = g') {x : B}
    {f f' : x ⟶ y} (η : f ⟶ f') :
      η ▷ g = eqToHom (by rw [h]) ≫ η ▷ g' ≫ eqToHom (by rw [h]) := by
  subst h
  simp

lemma leftUnitor_hom_congr {x y : B} {f f' : x ⟶ y} (h : f = f') :
    (λ_ f).hom = 𝟙 _ ◁ (eqToHom h)  ≫ (λ_ f').hom ≫ eqToHom h.symm := by
  subst h
  simp

lemma leftUnitor_inv_congr {x y : B} {f f' : x ⟶ y} (h : f = f') :
    (λ_ f).inv = (eqToHom h) ≫ (λ_ f').inv ≫ 𝟙 _ ◁ eqToHom h.symm := by
  subst h
  simp

lemma rightUnitor_hom_congr {x y : B} {f f' : x ⟶ y} (h : f = f') :
    (ρ_ f).hom = (eqToHom h) ▷ 𝟙 _  ≫ (ρ_ f').hom ≫ eqToHom h.symm := by
  subst h
  simp

lemma rightUnitor_inv_congr {x y : B} {f f' : x ⟶ y} (h : f = f') :
    (ρ_ f).inv = (eqToHom h) ≫ (ρ_ f').inv ≫ eqToHom h.symm ▷ 𝟙 _ := by
  subst h
  simp

end CategoryTheory.Bicategory
