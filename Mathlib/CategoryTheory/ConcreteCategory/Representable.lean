/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.ChosenRepresentation
public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.CategoryTheory.Yoneda

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Representable functors in concrete categories

This file provides some API for the situation `(F ⋙ forget D).RepresentableBy Y`.
-/

@[expose] public section

namespace CategoryTheory.Functor.RepresentableBy

open Opposite

variable {C D : Type*} [Category* C] [Category* D] {F : Cᵒᵖ ⥤ D}
    {CD : D → Type*} {FD : D → D → Type*} [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)]
    [ConcreteCategory D FD] {Y : C} (α : (F ⋙ forget D).RepresentableBy Y)

/-- The natural bijection `(X ⟶ Y) ≃ F.obj (op X)`. -/
def homEquiv' {X : C} : (X ⟶ Y) ≃ ToType (F.obj (op X)) := α.homEquiv

lemma homEquiv'_comp {X X' : C} (f : X ⟶ X') (g : X' ⟶ Y) :
    α.homEquiv' (f ≫ g) = F.map f.op (α.homEquiv' g) := α.homEquiv_comp _ _

end CategoryTheory.Functor.RepresentableBy

-- For now, we just repeat everything derived from `ChosenCorepresentation` for the special case
-- when the functor is the forgetful functor, because `CC` and `FC` are not always reducibly def-eq
-- to `(forget C).obj`, `.map`.
universe w v u

namespace CategoryTheory.ConcreteCategory

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type w}
  [∀ X Y : C, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
  [c : (forget C).ChosenCorepresentation] {Z Y : C}

def couniv : CC (forget C).coreprObj := c.coreprBy.homEquiv (𝟙 _)
def homOfElement (x : CC Z) : (forget C).coreprObj ⟶ Z := c.coreprBy.homEquiv.symm x

@[simp] lemma homOfElement_apply (x : CC Z) : homOfElement x couniv = x :=
  (forget C).map_homOfElement_apply ..

@[simp] lemma homOfElement_apply' [Unique (CC (forget C).coreprObj)]
    (x : CC Z) (u : CC (forget C).coreprObj) : homOfElement x u = x :=
  (forget C).map_homOfElement_apply' x u

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma homOfElement_comp (x : CC Z) (g : Z ⟶ Y) : homOfElement x ≫ g = homOfElement (g x) :=
  c.coreprBy.homEquiv_symm_comp ..

lemma homOfElement_injective :
    Function.Injective (homOfElement : CC Z → ((forget C).coreprObj ⟶ Z)) :=
  c.coreprBy.homEquiv.symm.injective

lemma homOfElement_inj {x y : CC Z} : homOfElement x = homOfElement y ↔ x = y := by
  rw [← c.coreprBy.homEquiv.symm.injective.eq_iff]; rfl

@[simp] lemma homOfElement_couniv : homOfElement (couniv : CC (forget C).coreprObj) = 𝟙 _ := by
  simp [homOfElement, couniv]

@[ext]
lemma homOfElement_ext {f g : (forget C).coreprObj ⟶ Z} (h : f couniv = g couniv) : f = g := by
  replace h := congrArg homOfElement h
  simpa [← homOfElement_comp, homOfElement_couniv] using h

/-- When the forgetful functor of a concrete category is corepresentable, pointwise equality of
morphisms can be tested by composition with `homOfElement`. -/
lemma hom_ext_iff' {X Y : C} (f g : X ⟶ Y) :
    f = g ↔ ∀ x : CC X, homOfElement x ≫ f = homOfElement x ≫ g where
  mp h := by simp [h]
  mpr h := by
    simp_rw [homOfElement_comp, homOfElement_inj] at h
    rwa [ConcreteCategory.hom_ext_iff]

/-- When the forgetful functor of a concrete category is corepresentable, equality of morphisms at
a point can be tested via `homOfElement`. -/
lemma hom_apply_eq_iff {X Y : C} (f g : X ⟶ Y) (x : CC X) :
    f x = g x ↔ homOfElement x ≫ f = homOfElement x ≫ g where
  mp h := by simp [h]
  mpr h := by simp_rw [homOfElement_comp, homOfElement_inj] at h; exact h



alias ⟨_, hom_ext'⟩ := hom_ext_iff'

lemma apply_eq_iff_homOfElement_comp {X Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    (x : CC X) (y : CC Y) : f x = g y ↔
      ConcreteCategory.homOfElement x ≫ f = ConcreteCategory.homOfElement y ≫ g := by
  simp_rw [ConcreteCategory.homOfElement_comp, ConcreteCategory.homOfElement_inj]

end CategoryTheory.ConcreteCategory
