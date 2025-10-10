/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Kim Morrison, Floris van Doorn
-/
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Iso

/-!
# Natural isomorphisms

For the most part, natural isomorphisms are just another sort of isomorphism.

We provide some special support for extracting components:
* if `α : F ≅ G`, then `α.app X : F.obj X ≅ G.obj X`,
and building natural isomorphisms from components:
*
```
NatIso.ofComponents
  (app : ∀ X : C, F.obj X ≅ G.obj X)
  (naturality : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (app Y).hom = (app X).hom ≫ G.map f) :
F ≅ G
```
only needing to check naturality in one direction.

## Implementation

Note that `NatIso` is a namespace without a corresponding definition;
we put some declarations that are specifically about natural isomorphisms in the `Iso`
namespace so that they are available using dot notation.
-/

set_option mathlib.tactic.category.grind true

-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open NatTrans

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃}
  [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']

namespace Iso

/-- The application of a natural isomorphism to an object. We put this definition in a different
namespace, so that we can use `α.app` -/
@[simps (attr := grind =)]
def app {F G : C ⥤ D} (α : F ≅ G) (X : C) :
    F.obj X ≅ G.obj X where
  hom := α.hom.app X
  inv := α.inv.app X

@[reassoc (attr := simp), grind =]
theorem hom_inv_id_app {F G : C ⥤ D} (α : F ≅ G) (X : C) :
    α.hom.app X ≫ α.inv.app X = 𝟙 (F.obj X) := by cat_disch

@[reassoc (attr := simp), grind =]
theorem inv_hom_id_app {F G : C ⥤ D} (α : F ≅ G) (X : C) :
    α.inv.app X ≫ α.hom.app X = 𝟙 (G.obj X) := by cat_disch

@[reassoc (attr := simp)]
lemma hom_inv_id_app_app {F G : C ⥤ D ⥤ E} (e : F ≅ G) (X₁ : C) (X₂ : D) :
    (e.hom.app X₁).app X₂ ≫ (e.inv.app X₁).app X₂ = 𝟙 _ := by cat_disch

@[reassoc (attr := simp)]
lemma inv_hom_id_app_app {F G : C ⥤ D ⥤ E} (e : F ≅ G) (X₁ : C) (X₂ : D) :
    (e.inv.app X₁).app X₂ ≫ (e.hom.app X₁).app X₂ = 𝟙 _ := by cat_disch

@[reassoc (attr := simp)]
lemma hom_inv_id_app_app_app {F G : C ⥤ D ⥤ E ⥤ E'} (e : F ≅ G)
    (X₁ : C) (X₂ : D) (X₃ : E) :
    ((e.hom.app X₁).app X₂).app X₃ ≫ ((e.inv.app X₁).app X₂).app X₃ = 𝟙 _ := by cat_disch

@[reassoc (attr := simp)]
lemma inv_hom_id_app_app_app {F G : C ⥤ D ⥤ E ⥤ E'} (e : F ≅ G)
    (X₁ : C) (X₂ : D) (X₃ : E) :
    ((e.inv.app X₁).app X₂).app X₃ ≫ ((e.hom.app X₁).app X₂).app X₃ = 𝟙 _ := by cat_disch

end Iso

namespace NatIso

open CategoryTheory.Category CategoryTheory.Functor

@[simp]
theorem trans_app {F G H : C ⥤ D} (α : F ≅ G) (β : G ≅ H) (X : C) :
    (α ≪≫ β).app X = α.app X ≪≫ β.app X :=
  rfl

@[deprecated Iso.app_hom (since := "2025-03-11")]
theorem app_hom {F G : C ⥤ D} (α : F ≅ G) (X : C) : (α.app X).hom = α.hom.app X :=
  rfl

@[deprecated Iso.app_hom (since := "2025-03-11")]
theorem app_inv {F G : C ⥤ D} (α : F ≅ G) (X : C) : (α.app X).inv = α.inv.app X :=
  rfl

variable {F G : C ⥤ D}

instance hom_app_isIso (α : F ≅ G) (X : C) : IsIso (α.hom.app X) :=
  ⟨⟨α.inv.app X, ⟨by grind, by grind⟩⟩⟩

instance inv_app_isIso (α : F ≅ G) (X : C) : IsIso (α.inv.app X) :=
  ⟨⟨α.hom.app X, ⟨by grind, by grind⟩⟩⟩

section

/-!
Unfortunately we need a separate set of cancellation lemmas for components of natural isomorphisms,
because the `simp` normal form is `α.hom.app X`, rather than `α.app.hom X`.

(With the latter, the morphism would be visibly part of an isomorphism, so general lemmas about
isomorphisms would apply.)

In the future, we should consider a redesign that changes this simp norm form,
but for now it breaks too many proofs.
-/


variable (α : F ≅ G)

@[simp]
theorem cancel_natIso_hom_left {X : C} {Z : D} (g g' : G.obj X ⟶ Z) :
    α.hom.app X ≫ g = α.hom.app X ≫ g' ↔ g = g' := by simp only [cancel_epi, refl]

@[simp]
theorem cancel_natIso_inv_left {X : C} {Z : D} (g g' : F.obj X ⟶ Z) :
    α.inv.app X ≫ g = α.inv.app X ≫ g' ↔ g = g' := by simp only [cancel_epi, refl]

@[simp]
theorem cancel_natIso_hom_right {X : D} {Y : C} (f f' : X ⟶ F.obj Y) :
    f ≫ α.hom.app Y = f' ≫ α.hom.app Y ↔ f = f' := by simp only [cancel_mono, refl]

@[simp]
theorem cancel_natIso_inv_right {X : D} {Y : C} (f f' : X ⟶ G.obj Y) :
    f ≫ α.inv.app Y = f' ≫ α.inv.app Y ↔ f = f' := by simp only [cancel_mono, refl]

@[simp]
theorem cancel_natIso_hom_right_assoc {W X X' : D} {Y : C} (f : W ⟶ X) (g : X ⟶ F.obj Y)
    (f' : W ⟶ X') (g' : X' ⟶ F.obj Y) :
    f ≫ g ≫ α.hom.app Y = f' ≫ g' ≫ α.hom.app Y ↔ f ≫ g = f' ≫ g' := by
  simp only [← Category.assoc, cancel_mono, refl]

@[simp]
theorem cancel_natIso_inv_right_assoc {W X X' : D} {Y : C} (f : W ⟶ X) (g : X ⟶ G.obj Y)
    (f' : W ⟶ X') (g' : X' ⟶ G.obj Y) :
    f ≫ g ≫ α.inv.app Y = f' ≫ g' ≫ α.inv.app Y ↔ f ≫ g = f' ≫ g' := by
  simp only [← Category.assoc, cancel_mono, refl]

attribute [grind ←=] CategoryTheory.IsIso.inv_eq_of_hom_inv_id

@[simp]
theorem inv_inv_app {F G : C ⥤ D} (e : F ≅ G) (X : C) : inv (e.inv.app X) = e.hom.app X := by
  cat_disch

end

variable {X Y : C}

theorem naturality_1 (α : F ≅ G) (f : X ⟶ Y) : α.inv.app X ≫ F.map f ≫ α.hom.app Y = G.map f := by
  simp

theorem naturality_2 (α : F ≅ G) (f : X ⟶ Y) : α.hom.app X ≫ G.map f ≫ α.inv.app Y = F.map f := by
  simp

theorem naturality_1' (α : F ⟶ G) (f : X ⟶ Y) {_ : IsIso (α.app X)} :
    inv (α.app X) ≫ F.map f ≫ α.app Y = G.map f := by simp

@[reassoc (attr := simp)]
theorem naturality_2' (α : F ⟶ G) (f : X ⟶ Y) {_ : IsIso (α.app Y)} :
    α.app X ≫ G.map f ≫ inv (α.app Y) = F.map f := by cat_disch

/-- The components of a natural isomorphism are isomorphisms.
-/
instance isIso_app_of_isIso (α : F ⟶ G) [IsIso α] (X) : IsIso (α.app X) :=
  ⟨⟨(inv α).app X, ⟨by grind, by grind⟩⟩⟩

@[simp]
theorem isIso_inv_app (α : F ⟶ G) {_ : IsIso α} (X) : (inv α).app X = inv (α.app X) := by cat_disch

@[simp]
theorem inv_map_inv_app (F : C ⥤ D ⥤ E) {X Y : C} (e : X ≅ Y) (Z : D) :
    inv ((F.map e.inv).app Z) = (F.map e.hom).app Z := by cat_disch

-- TODO: `hom_inv_id` and `inv_hom_id` are not yet working via `grind`,
-- but they work fine in my minimization in the `grind` test suite.
-- Investigate on nightly-testing / the next release?
set_option mathlib.tactic.category.grind false in
/-- Construct a natural isomorphism between functors by giving object level isomorphisms,
and checking naturality only in the forward direction.
-/
@[simps (attr := grind =)]
def ofComponents (app : ∀ X : C, F.obj X ≅ G.obj X)
    (naturality : ∀ {X Y : C} (f : X ⟶ Y),
      F.map f ≫ (app Y).hom = (app X).hom ≫ G.map f := by cat_disch) :
    F ≅ G where
  hom := { app := fun X => (app X).hom }
  inv :=
    { app := fun X => (app X).inv,
      naturality := fun X Y f => by
        have h := congr_arg (fun f => (app X).inv ≫ f ≫ (app Y).inv) (naturality f).symm
        simp only [Iso.inv_hom_id_assoc, Iso.hom_inv_id, assoc, comp_id] at h
        exact h }

@[simp]
theorem ofComponents.app (app' : ∀ X : C, F.obj X ≅ G.obj X) (naturality) (X) :
    (ofComponents app' naturality).app X = app' X := by cat_disch

-- Making this an instance would cause a typeclass inference loop with `isIso_app_of_isIso`.
/-- A natural transformation is an isomorphism if all its components are isomorphisms.
-/
theorem isIso_of_isIso_app (α : F ⟶ G) [∀ X : C, IsIso (α.app X)] : IsIso α :=
  (ofComponents (fun X => asIso (α.app X)) (by simp)).isIso_hom

/-- Horizontal composition of natural isomorphisms. -/
@[simps]
def hcomp {F G : C ⥤ D} {H I : D ⥤ E} (α : F ≅ G) (β : H ≅ I) : F ⋙ H ≅ G ⋙ I where
  hom := α.hom ◫ β.hom
  inv := α.inv ◫ β.inv

theorem isIso_map_iff {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) {X Y : C} (f : X ⟶ Y) :
    IsIso (F₁.map f) ↔ IsIso (F₂.map f) := by
  revert F₁ F₂
  suffices ∀ {F₁ F₂ : C ⥤ D} (_ : F₁ ≅ F₂) (_ : IsIso (F₁.map f)), IsIso (F₂.map f) from
    fun F₁ F₂ e => ⟨this e, this e.symm⟩
  intro F₁ F₂ e hf
  exact IsIso.mk ⟨e.inv.app Y ≫ inv (F₁.map f) ≫ e.hom.app X, by cat_disch⟩

end NatIso

lemma NatTrans.isIso_iff_isIso_app {F G : C ⥤ D} (τ : F ⟶ G) :
    IsIso τ ↔ ∀ X, IsIso (τ.app X) :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ NatIso.isIso_of_isIso_app _⟩

namespace Functor

variable (F : C ⥤ D) (obj : C → D) (e : ∀ X, F.obj X ≅ obj X)

set_option mathlib.tactic.category.grind false in
/-- Constructor for a functor that is isomorphic to a given functor `F : C ⥤ D`,
while being definitionally equal on objects to a given map `obj : C → D`
such that for all `X : C`, we have an isomorphism `F.obj X ≅ obj X`. -/
@[simps obj]
def copyObj : C ⥤ D where
  obj := obj
  map f := (e _).inv ≫ F.map f ≫ (e _).hom

/-- The functor constructed with `copyObj` is isomorphic to the given functor. -/
@[simps!]
def isoCopyObj : F ≅ F.copyObj obj e :=
  NatIso.ofComponents e (by simp [Functor.copyObj])

end Functor

end CategoryTheory
