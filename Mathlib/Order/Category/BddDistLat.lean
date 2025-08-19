/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Category.BddLat
import Mathlib.Order.Category.DistLat

/-!
# The category of bounded distributive lattices

This defines `BddDistLat`, the category of bounded distributive lattices.

Note that this category is sometimes called [`DistLat`](https://ncatlab.org/nlab/show/DistLat) when
being a lattice is understood to entail having a bottom and a top element.
-/


universe u

open CategoryTheory

/-- The category of bounded distributive lattices with bounded lattice morphisms. -/
structure BddDistLat extends DistLat where
  [isBoundedOrder : BoundedOrder toDistLat]

/-- The underlying distrib lattice of a bounded distributive lattice. -/
add_decl_doc BddDistLat.toDistLat

namespace BddDistLat

instance : CoeSort BddDistLat Type* :=
  ⟨fun X ↦ X.toDistLat⟩

instance (X : BddDistLat) : DistribLattice X :=
  X.toDistLat.str

attribute [instance] BddDistLat.isBoundedOrder

/-- Construct a bundled `BddDistLat` from a `BoundedOrder` `DistribLattice`. -/
abbrev of (α : Type*) [DistribLattice α] [BoundedOrder α] : BddDistLat where
  carrier := α

theorem coe_of (α : Type*) [DistribLattice α] [BoundedOrder α] : ↥(of α) = α :=
  rfl

/-- The type of morphisms in `BddDistLat R`. -/
@[ext]
structure Hom (X Y : BddDistLat.{u}) where
  private mk ::
  /-- The underlying `BoundedLatticeHom`. -/
  hom' : BoundedLatticeHom X Y

instance : Category BddDistLat.{u} where
  Hom X Y := Hom X Y
  id X := ⟨BoundedLatticeHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory BddDistLat (BoundedLatticeHom · ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `BddDistLat` back into a `BoundedLatticeHom`. -/
abbrev Hom.hom {X Y : BddDistLat.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := BddDistLat) f

/-- Typecheck a `BoundedLatticeHom` as a morphism in `BddDistLat`. -/
abbrev ofHom {X Y : Type u} [DistribLattice X] [BoundedOrder X] [DistribLattice Y] [BoundedOrder Y]
    (f : BoundedLatticeHom X Y) :
    of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := BddDistLat) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (X Y : BddDistLat.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
lemma coe_id {X : BddDistLat} : (𝟙 X : X → X) = id := rfl

@[simp]
lemma coe_comp {X Y Z : BddDistLat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[simp]
lemma forget_map {X Y : BddDistLat} (f : X ⟶ Y) :
    (forget BddDistLat).map f = f := rfl

@[ext]
lemma ext {X Y : BddDistLat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

@[simp]
lemma hom_id {X : BddDistLat} : (𝟙 X : X ⟶ X).hom = BoundedLatticeHom.id _ := rfl

/- Provided for rewriting. -/
lemma id_apply (X : BddDistLat) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
lemma hom_comp {X Y Z : BddDistLat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
lemma comp_apply {X Y Z : BddDistLat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
lemma hom_ext {X Y : BddDistLat} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
lemma hom_ofHom {X Y : Type u} [DistribLattice X] [BoundedOrder X] [DistribLattice Y]
    [BoundedOrder Y] (f : BoundedLatticeHom X Y) :
    (ofHom f).hom = f :=
  rfl

@[simp]
lemma ofHom_hom {X Y : BddDistLat} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id {X : Type u} [DistribLattice X] [BoundedOrder X] :
    ofHom (BoundedLatticeHom.id _) = 𝟙 (of X) := rfl

@[simp]
lemma ofHom_comp {X Y Z : Type u} [DistribLattice X] [BoundedOrder X] [DistribLattice Y]
    [BoundedOrder Y] [DistribLattice Z] [BoundedOrder Z]
    (f : BoundedLatticeHom X Y) (g : BoundedLatticeHom Y Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

lemma ofHom_apply {X Y : Type u} [DistribLattice X] [BoundedOrder X] [DistribLattice Y]
    [BoundedOrder Y]
    (f : BoundedLatticeHom X Y) (x : X) :
    (ofHom f) x = f x := rfl

lemma inv_hom_apply {X Y : BddDistLat} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

lemma hom_inv_apply {X Y : BddDistLat} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp

instance : Inhabited BddDistLat :=
  ⟨of PUnit⟩

/-- Turn a `BddDistLat` into a `BddLat` by forgetting it is distributive. -/
def toBddLat (X : BddDistLat) : BddLat :=
  .of X

@[simp]
theorem coe_toBddLat (X : BddDistLat) : ↥X.toBddLat = ↥X :=
  rfl

instance hasForgetToDistLat : HasForget₂ BddDistLat DistLat where
  forget₂.obj X := .of X
  forget₂.map f := DistLat.ofHom f.hom.toLatticeHom

instance hasForgetToBddLat : HasForget₂ BddDistLat BddLat where
  forget₂.obj X := .of X
  forget₂.map f := BddLat.ofHom f.hom

theorem forget_bddLat_lat_eq_forget_distLat_lat :
    forget₂ BddDistLat BddLat ⋙ forget₂ BddLat Lat =
      forget₂ BddDistLat DistLat ⋙ forget₂ DistLat Lat :=
  rfl

/-- Constructs an equivalence between bounded distributive lattices from an order isomorphism
between them. -/
@[simps]
def Iso.mk {α β : BddDistLat.{u}} (e : α ≃o β) : α ≅ β where
  hom := BddDistLat.ofHom e
  inv := BddDistLat.ofHom e.symm

/-- `OrderDual` as a functor. -/
@[simps map]
def dual : BddDistLat ⥤ BddDistLat where
  obj X := of Xᵒᵈ
  map f := BddDistLat.ofHom f.hom.dual

/-- The equivalence between `BddDistLat` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
def dualEquiv : BddDistLat ≌ BddDistLat where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X ↦ Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X ↦ Iso.mk <| OrderIso.dualDual X

end BddDistLat

theorem bddDistLat_dual_comp_forget_to_distLat :
    BddDistLat.dual ⋙ forget₂ BddDistLat DistLat =
      forget₂ BddDistLat DistLat ⋙ DistLat.dual :=
  rfl
