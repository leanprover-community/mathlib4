/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Category.PartOrd
import Mathlib.Order.Hom.Lattice

/-!
# The category of lattices

This defines `Lat`, the category of lattices.

Note that `Lat` doesn't correspond to the literature definition of [`Lat`]
(https://ncatlab.org/nlab/show/Lat) as we don't require bottom or top elements. Instead, `Lat`
corresponds to `BddLat`.

## TODO

The free functor from `Lat` to `BddLat` is `X → WithTop (WithBot X)`.
-/

universe u

open CategoryTheory

/-- The category of lattices. -/
structure Lat where
  /-- The underlying lattices. -/
  (carrier : Type*)
  [str : Lattice carrier]

attribute [instance] Lat.str

initialize_simps_projections Lat (carrier → coe, -str)

namespace Lat

instance : CoeSort Lat (Type _) :=
  ⟨Lat.carrier⟩

attribute [coe] Lat.carrier

/-- Construct a bundled `Lat` from the underlying type and typeclass. -/
abbrev of (X : Type*) [Lattice X] : Lat := ⟨X⟩

/-- The type of morphisms in `Lat R`. -/
@[ext]
structure Hom (X Y : Lat.{u}) where
  private mk ::
  /-- The underlying `LatticeHom`. -/
  hom' : LatticeHom X Y

instance : Category Lat.{u} where
  Hom X Y := Hom X Y
  id X := ⟨LatticeHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory Lat (LatticeHom · ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `Lat` back into a `LatticeHom`. -/
abbrev Hom.hom {X Y : Lat.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := Lat) f

/-- Typecheck a `LatticeHom` as a morphism in `Lat`. -/
abbrev ofHom {X Y : Type u} [Lattice X] [Lattice Y] (f : LatticeHom X Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := Lat) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (X Y : Lat.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
lemma coe_id {X : Lat} : (𝟙 X : X → X) = id := rfl

@[simp]
lemma coe_comp {X Y Z : Lat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[simp]
lemma forget_map {X Y : Lat} (f : X ⟶ Y) :
    (forget Lat).map f = f := rfl

@[ext]
lemma ext {X Y : Lat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

-- This is not `simp` to avoid rewriting in types of terms.
theorem coe_of (X : Type u) [Lattice X] : (Lat.of X : Type u) = X := rfl

@[simp]
lemma hom_id {X : Lat} : (𝟙 X : X ⟶ X).hom = LatticeHom.id _ := rfl

/- Provided for rewriting. -/
lemma id_apply (X : Lat) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
lemma hom_comp {X Y Z : Lat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
lemma comp_apply {X Y Z : Lat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
lemma hom_ext {X Y : Lat} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
lemma hom_ofHom {X Y : Type u} [Lattice X] [Lattice Y] (f : LatticeHom X Y) : (ofHom f).hom = f :=
  rfl

@[simp]
lemma ofHom_hom {X Y : Lat} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id {X : Type u} [Lattice X] : ofHom (LatticeHom.id _) = 𝟙 (of X) := rfl

@[simp]
lemma ofHom_comp {X Y Z : Type u} [Lattice X] [Lattice Y] [Lattice Z]
    (f : LatticeHom X Y) (g : LatticeHom Y Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

lemma ofHom_apply {X Y : Type u} [Lattice X] [Lattice Y] (f : LatticeHom X Y) (x : X) :
    (ofHom f) x = f x := rfl

lemma inv_hom_apply {X Y : Lat} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

lemma hom_inv_apply {X Y : Lat} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp

instance hasForgetToPartOrd : HasForget₂ Lat PartOrd where
  forget₂.obj X := .of X
  forget₂.map f := PartOrd.ofHom f.hom

/-- Constructs an isomorphism of lattices from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : Lat.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm

/-- `OrderDual` as a functor. -/
@[simps map]
def dual : Lat ⥤ Lat where
  obj X := of Xᵒᵈ
  map f := ofHom f.hom.dual

/-- The equivalence between `Lat` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
def dualEquiv : Lat ≌ Lat where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X ↦ Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X ↦ Iso.mk <| OrderIso.dualDual X

end Lat

theorem Lat_dual_comp_forget_to_partOrd :
    Lat.dual ⋙ forget₂ Lat PartOrd = forget₂ Lat PartOrd ⋙ PartOrd.dual :=
  rfl
