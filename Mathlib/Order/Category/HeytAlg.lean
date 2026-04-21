/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Category.BddDistLat
public import Mathlib.Order.Heyting.Hom

/-!
# The category of Heyting algebras

This file defines `HeytAlg`, the category of Heyting algebras.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


universe u

open CategoryTheory Opposite Order

/-- The category of Heyting algebras. -/
structure HeytAlg where
  /-- The underlying Heyting algebra. -/
  carrier : Type*
  [str : HeytingAlgebra carrier]

attribute [instance] HeytAlg.str

initialize_simps_projections HeytAlg (carrier → coe, -str)

namespace HeytAlg

instance : CoeSort HeytAlg (Type _) :=
  ⟨HeytAlg.carrier⟩

attribute [coe] HeytAlg.carrier

/-- Construct a bundled `HeytAlg` from the underlying type and typeclass. -/
abbrev of (X : Type*) [HeytingAlgebra X] : HeytAlg := ⟨X⟩

set_option backward.privateInPublic true in
/-- The type of morphisms in `HeytAlg R`. -/
@[ext]
structure Hom (X Y : HeytAlg.{u}) where
  private mk ::
  /-- The underlying `HeytingHom`. -/
  hom' : HeytingHom X Y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : Category HeytAlg.{u} where
  Hom X Y := Hom X Y
  id X := ⟨HeytingHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : ConcreteCategory HeytAlg (HeytingHom · ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `HeytAlg` back into a `HeytingHom`. -/
abbrev Hom.hom {X Y : HeytAlg.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := HeytAlg) f

/-- Typecheck a `HeytingHom` as a morphism in `HeytAlg`. -/
abbrev ofHom {X Y : Type u} [HeytingAlgebra X] [HeytingAlgebra Y] (f : HeytingHom X Y) :
    of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := HeytAlg) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (X Y : HeytAlg.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
lemma coe_id {X : HeytAlg} : (𝟙 X : X → X) = id := rfl

@[simp]
lemma coe_comp {X Y Z : HeytAlg} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[simp]
lemma forget_map {X Y : HeytAlg} (f : X ⟶ Y) :
    (forget HeytAlg).map f = (f : _ → _) := rfl

@[ext]
lemma ext {X Y : HeytAlg} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

-- This is not `simp` to avoid rewriting in types of terms.
theorem coe_of (X : Type u) [HeytingAlgebra X] : (HeytAlg.of X : Type u) = X := rfl

@[simp]
lemma hom_id {X : HeytAlg} : (𝟙 X : X ⟶ X).hom = HeytingHom.id _ := rfl

/- Provided for rewriting. -/
lemma id_apply (X : HeytAlg) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
lemma hom_comp {X Y Z : HeytAlg} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
lemma comp_apply {X Y Z : HeytAlg} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
lemma hom_ext {X Y : HeytAlg} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
lemma hom_ofHom {X Y : Type u} [HeytingAlgebra X] [HeytingAlgebra Y] (f : HeytingHom X Y) :
    (ofHom f).hom = f :=
  rfl

@[simp]
lemma ofHom_hom {X Y : HeytAlg} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id {X : Type u} [HeytingAlgebra X] : ofHom (HeytingHom.id _) = 𝟙 (of X) := rfl

@[simp]
lemma ofHom_comp {X Y Z : Type u} [HeytingAlgebra X] [HeytingAlgebra Y] [HeytingAlgebra Z]
    (f : HeytingHom X Y) (g : HeytingHom Y Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

lemma ofHom_apply {X Y : Type u} [HeytingAlgebra X] [HeytingAlgebra Y]
    (f : HeytingHom X Y) (x : X) :
    (ofHom f) x = f x := rfl

lemma inv_hom_apply {X Y : HeytAlg} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

lemma hom_inv_apply {X Y : HeytAlg} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp

instance : Inhabited HeytAlg :=
  ⟨of PUnit⟩

@[simps]
instance hasForgetToLat : HasForget₂ HeytAlg BddDistLat where
  forget₂.obj X := .of X
  forget₂.map f := BddDistLat.ofHom f.hom

/-- Constructs an isomorphism of Heyting algebras from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : HeytAlg.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

end HeytAlg
