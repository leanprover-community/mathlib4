/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Fintype.Order
import Mathlib.Order.Category.BddDistLat
import Mathlib.Order.Category.FinPartOrd

/-!
# The category of finite bounded distributive lattices

This file defines `FinBddDistLat`, the category of finite distributive lattices with
bounded lattice homomorphisms.
-/


universe u

open CategoryTheory

/-- The category of finite distributive lattices with bounded lattice morphisms. -/
structure FinBddDistLat where
  toBddDistLat : BddDistLat
  [isFintype : Fintype toBddDistLat]

namespace FinBddDistLat

instance : CoeSort FinBddDistLat Type* :=
  ⟨fun X => X.toBddDistLat⟩

instance (X : FinBddDistLat) : DistribLattice X :=
  X.toBddDistLat.toDistLat.str

instance (X : FinBddDistLat) : BoundedOrder X :=
  X.toBddDistLat.isBoundedOrder

attribute [instance] FinBddDistLat.isFintype

/-- Construct a bundled `FinBddDistLat` from a `Nonempty` `BoundedOrder` `DistribLattice`. -/
def of (α : Type*) [DistribLattice α] [BoundedOrder α] [Fintype α] : FinBddDistLat :=
  -- Porting note: was `⟨⟨⟨α⟩⟩⟩`
  -- see https://github.com/leanprover-community/mathlib4/issues/4998
  ⟨⟨{α := α}⟩⟩

/-- Construct a bundled `FinBddDistLat` from a `Nonempty` `BoundedOrder` `DistribLattice`. -/
def of' (α : Type*) [DistribLattice α] [Fintype α] [Nonempty α] : FinBddDistLat :=
  haveI := Fintype.toBoundedOrder α
  -- Porting note: was `⟨⟨⟨α⟩⟩⟩`
  -- see https://github.com/leanprover-community/mathlib4/issues/4998
  ⟨⟨{α := α}⟩⟩

instance : Inhabited FinBddDistLat :=
  ⟨of PUnit⟩

instance largeCategory : LargeCategory FinBddDistLat :=
  InducedCategory.category toBddDistLat

instance concreteCategory : ConcreteCategory FinBddDistLat :=
  InducedCategory.concreteCategory toBddDistLat

instance hasForgetToBddDistLat : HasForget₂ FinBddDistLat BddDistLat :=
  InducedCategory.hasForget₂ FinBddDistLat.toBddDistLat

instance hasForgetToFinPartOrd : HasForget₂ FinBddDistLat FinPartOrd where
  forget₂.obj X := FinPartOrd.of X
  forget₂.map {X Y} f := { hom := (show BoundedLatticeHom X Y from f.hom.hom : X →o Y) }

/-- Constructs a morphism between finite distributive lattices from a bounded
lattice homomorphism between them. -/
@[simps]
def Hom.mk {α β : FinBddDistLat.{u}} (f : BoundedLatticeHom α β) : α ⟶ β where
  hom := { hom := f }

/-- Constructs an equivalence between finite distributive lattices from an order isomorphism
between them. -/
@[simps]
def Iso.mk {α β : FinBddDistLat.{u}} (e : α ≃o β) : α ≅ β where
  hom := Hom.mk e
  inv := Hom.mk e.symm
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

/-- The bijection `(α ⟶ β) ≃ BoundedLatticeHom α β` when `α` and `β`
are objects of `FinBddDistLat`. -/
@[simps]
def homEquiv {α β : FinBddDistLat.{u}} : (α ⟶ β) ≃ BoundedLatticeHom α β where
  toFun f := f.hom.hom
  invFun f := Hom.mk f
  left_inv _ := rfl
  right_inv _ := rfl

/-- `OrderDual` as a functor. -/
@[simps]
def dual : FinBddDistLat ⥤ FinBddDistLat where
  obj X := of Xᵒᵈ
  map {X Y} f := Hom.mk (by apply BoundedLatticeHom.dual f.hom.hom)

/-- The equivalence between `FinBddDistLat` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
def dualEquiv : FinBddDistLat ≌ FinBddDistLat where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X

end FinBddDistLat

theorem finBddDistLat_dual_comp_forget_to_bddDistLat :
    FinBddDistLat.dual ⋙ forget₂ FinBddDistLat BddDistLat =
      forget₂ FinBddDistLat BddDistLat ⋙ BddDistLat.dual :=
  rfl
