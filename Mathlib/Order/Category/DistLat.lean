/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Category.Lat

/-!
# The category of distributive lattices

This file defines `DistLat`, the category of distributive lattices.

Note that [`DistLat`](https://ncatlab.org/nlab/show/DistLat) in the literature doesn't always
correspond to `DistLat` as we don't require bottom or top elements. Instead, this `DistLat`
corresponds to `BddDistLat`.
-/


universe u

open CategoryTheory

/-- The category of distributive lattices. -/
structure DistLat where
  /-- The underlying distributive lattice. -/
  carrier : Type*
  [str : DistribLattice carrier]

attribute [instance] DistLat.str

initialize_simps_projections DistLat (carrier → coe, -str)

namespace DistLat

instance : CoeSort DistLat.{u} (Type u) :=
  ⟨DistLat.carrier⟩

attribute [coe] DistLat.carrier

/-- Construct a bundled `DistLat` from the underlying type and typeclass. -/
abbrev of (X : Type*) [DistribLattice X] : DistLat := ⟨X⟩

/-- The type of morphisms in `DistLat R`. -/
@[ext]
structure Hom (X Y : DistLat.{u}) where
  private mk ::
  /-- The underlying `LatticeHom`. -/
  hom' : LatticeHom X Y

instance : Category DistLat.{u} where
  Hom X Y := Hom X Y
  id X := ⟨LatticeHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory DistLat (LatticeHom · ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `DistLat` back into a `LatticeHom`. -/
abbrev Hom.hom {X Y : DistLat.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := DistLat) f

/-- Typecheck a `LatticeHom` as a morphism in `DistLat`. -/
abbrev ofHom {X Y : Type u} [DistribLattice X] [DistribLattice Y] (f : LatticeHom X Y) :
    of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := DistLat) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (X Y : DistLat.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
lemma coe_id {X : DistLat} : (𝟙 X : X → X) = id := rfl

@[simp]
lemma coe_comp {X Y Z : DistLat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[simp]
lemma forget_map {X Y : DistLat} (f : X ⟶ Y) :
    (forget DistLat).map f = f := rfl

@[ext]
lemma ext {X Y : DistLat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

-- This is not `simp` to avoid rewriting in types of terms.
theorem coe_of (X : Type u) [DistribLattice X] : (DistLat.of X : Type u) = X := rfl

@[simp]
lemma hom_id {X : DistLat} : (𝟙 X : X ⟶ X).hom = LatticeHom.id _ := rfl

/- Provided for rewriting. -/
lemma id_apply (X : DistLat) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
lemma hom_comp {X Y Z : DistLat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
lemma comp_apply {X Y Z : DistLat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
lemma hom_ext {X Y : DistLat} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
lemma hom_ofHom {X Y : Type u} [DistribLattice X] [DistribLattice Y] (f : LatticeHom X Y) :
    (ofHom f).hom = f :=
  rfl

@[simp]
lemma ofHom_hom {X Y : DistLat} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id {X : Type u} [DistribLattice X] : ofHom (LatticeHom.id _) = 𝟙 (of X) := rfl

@[simp]
lemma ofHom_comp {X Y Z : Type u} [DistribLattice X] [DistribLattice Y] [DistribLattice Z]
    (f : LatticeHom X Y) (g : LatticeHom Y Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

lemma ofHom_apply {X Y : Type u} [DistribLattice X] [DistribLattice Y]
    (f : LatticeHom X Y) (x : X) :
    (ofHom f) x = f x := rfl

lemma inv_hom_apply {X Y : DistLat} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

lemma hom_inv_apply {X Y : DistLat} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp

instance hasForgetToLat : HasForget₂ DistLat Lat where
  forget₂.obj X := .of X
  forget₂.map f := Lat.ofHom f.hom

/-- Constructs an equivalence between distributive lattices from an order isomorphism between them.
-/
@[simps]
def Iso.mk {α β : DistLat.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm

/-- `OrderDual` as a functor. -/
@[simps map]
def dual : DistLat ⥤ DistLat where
  obj X := of Xᵒᵈ
  map f := ofHom f.hom.dual

/-- The equivalence between `DistLat` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
def dualEquiv : DistLat ≌ DistLat where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun _ => rfl
  counitIso := NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun _ => rfl

end DistLat

theorem distLat_dual_comp_forget_to_Lat :
    DistLat.dual ⋙ forget₂ DistLat Lat = forget₂ DistLat Lat ⋙ Lat.dual :=
  rfl
