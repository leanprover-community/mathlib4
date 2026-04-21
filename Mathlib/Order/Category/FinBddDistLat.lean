/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Fintype.Order
public import Mathlib.Order.Category.BddDistLat
public import Mathlib.Order.Category.FinPartOrd

/-!
# The category of finite bounded distributive lattices

This file defines `FinBddDistLat`, the category of finite distributive lattices with
bounded lattice homomorphisms.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


universe u

open CategoryTheory

/-- The category of finite distributive lattices with bounded lattice morphisms. -/
structure FinBddDistLat extends BddDistLat where
  [isFintype : Fintype carrier]

namespace FinBddDistLat

instance : CoeSort FinBddDistLat Type* :=
  ⟨fun X => X.carrier⟩

instance (X : FinBddDistLat) : DistribLattice X :=
  X.str

instance (X : FinBddDistLat) : BoundedOrder X :=
  X.isBoundedOrder

attribute [instance] FinBddDistLat.isFintype

/-- Construct a bundled `FinBddDistLat` from a `Fintype` `BoundedOrder` `DistribLattice`. -/
abbrev of (α : Type*) [DistribLattice α] [BoundedOrder α] [Fintype α] : FinBddDistLat where
  carrier := α

/-- Construct a bundled `FinBddDistLat` from a `Nonempty` `Fintype` `DistribLattice`. -/
abbrev of' (α : Type*) [DistribLattice α] [Fintype α] [Nonempty α] : FinBddDistLat where
  carrier := α
  isBoundedOrder := Fintype.toBoundedOrder α

set_option backward.privateInPublic true in
/-- The type of morphisms in `FinBddDistLat R`. -/
@[ext]
structure Hom (X Y : FinBddDistLat.{u}) where
  private mk ::
  /-- The underlying `BoundedLatticeHom`. -/
  hom' : BoundedLatticeHom X Y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : Category FinBddDistLat.{u} where
  Hom X Y := Hom X Y
  id X := ⟨BoundedLatticeHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : ConcreteCategory FinBddDistLat (BoundedLatticeHom · ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `FinBddDistLat` back into a `BoundedLatticeHom`. -/
abbrev Hom.hom {X Y : FinBddDistLat.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := FinBddDistLat) f

/-- Typecheck a `BoundedLatticeHom` as a morphism in `FinBddDistLat`. -/
abbrev ofHom {X Y : Type u} [DistribLattice X] [BoundedOrder X] [Fintype X] [DistribLattice Y]
    [BoundedOrder Y] [Fintype Y]
    (f : BoundedLatticeHom X Y) :
    of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := FinBddDistLat) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (X Y : FinBddDistLat.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
lemma coe_id {X : FinBddDistLat} : (𝟙 X : X → X) = id := rfl

@[simp]
lemma coe_comp {X Y Z : FinBddDistLat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[simp]
lemma forget_map {X Y : FinBddDistLat} (f : X ⟶ Y) :
    (forget FinBddDistLat).map f = (f : _ → _) := rfl

@[ext]
lemma ext {X Y : FinBddDistLat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

@[simp]
lemma hom_id {X : FinBddDistLat} : (𝟙 X : X ⟶ X).hom = BoundedLatticeHom.id _ := rfl

/- Provided for rewriting. -/
lemma id_apply (X : FinBddDistLat) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
lemma hom_comp {X Y Z : FinBddDistLat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
lemma comp_apply {X Y Z : FinBddDistLat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
lemma hom_ext {X Y : FinBddDistLat} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
lemma hom_ofHom {X Y : Type u} [DistribLattice X] [BoundedOrder X] [Fintype X] [DistribLattice Y]
    [BoundedOrder Y] [Fintype Y] (f : BoundedLatticeHom X Y) : (ofHom f).hom = f := rfl

@[simp]
lemma ofHom_hom {X Y : FinBddDistLat} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id {X : Type u} [DistribLattice X] [BoundedOrder X] [Fintype X] :
    ofHom (BoundedLatticeHom.id _) = 𝟙 (of X) := rfl

@[simp]
lemma ofHom_comp {X Y Z : Type u} [DistribLattice X] [BoundedOrder X] [Fintype X] [DistribLattice Y]
    [BoundedOrder Y] [Fintype Y] [DistribLattice Z] [BoundedOrder Z] [Fintype Z]
    (f : BoundedLatticeHom X Y) (g : BoundedLatticeHom Y Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

lemma ofHom_apply {X Y : Type u} [DistribLattice X] [BoundedOrder X] [Fintype X] [DistribLattice Y]
    [BoundedOrder Y] [Fintype Y]
    (f : BoundedLatticeHom X Y) (x : X) :
    (ofHom f) x = f x := rfl

lemma inv_hom_apply {X Y : FinBddDistLat} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

lemma hom_inv_apply {X Y : FinBddDistLat} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp

instance : Inhabited FinBddDistLat :=
  ⟨of PUnit⟩

instance hasForgetToBddDistLat : HasForget₂ FinBddDistLat BddDistLat where
  forget₂.obj X := .of X
  forget₂.map f := BddDistLat.ofHom f.hom

instance hasForgetToFinPartOrd : HasForget₂ FinBddDistLat FinPartOrd where
  forget₂.obj X := .of X
  forget₂.map f := ConcreteCategory.ofHom (OrderHomClass.toOrderHom f.hom)

/-- Constructs an equivalence between finite distributive lattices from an order isomorphism
between them. -/
@[simps]
def Iso.mk {α β : FinBddDistLat.{u}} (e : α.carrier ≃o β.carrier) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

/-- `OrderDual` as a functor. -/
@[simps map]
def dual : FinBddDistLat ⥤ FinBddDistLat where
  obj X := of Xᵒᵈ
  map f := ofHom f.hom.dual

/-- The equivalence between `FinBddDistLat` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
def dualEquiv : FinBddDistLat ≌ FinBddDistLat where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents (fun X => Iso.mk (α := X) <| OrderIso.dualDual X)
  counitIso := NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X)

end FinBddDistLat

theorem finBddDistLat_dual_comp_forget_to_bddDistLat :
    FinBddDistLat.dual ⋙ forget₂ FinBddDistLat BddDistLat =
      forget₂ FinBddDistLat BddDistLat ⋙ BddDistLat.dual :=
  rfl
