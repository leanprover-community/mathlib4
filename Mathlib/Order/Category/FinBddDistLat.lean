/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.category.FinBddDistLat
! leanprover-community/mathlib commit 937b1c59c58710ef8ed91f8727ef402d49d621a2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
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
  [isFintype : Fintype to_BddDistLat]
#align FinBddDistLat FinBddDistLat

namespace FinBddDistLat

instance : CoeSort FinBddDistLat (Type _) :=
  ⟨fun X => X.toBddDistLat⟩

instance (X : FinBddDistLat) : DistribLattice X :=
  X.toBddDistLat.toDistLat.str

instance (X : FinBddDistLat) : BoundedOrder X :=
  X.toBddDistLat.isBoundedOrder

attribute [instance] FinBddDistLat.isFintype

/-- Construct a bundled `FinBddDistLat` from a `nonempty` `bounded_order` `distrib_lattice`. -/
def of (α : Type _) [DistribLattice α] [BoundedOrder α] [Fintype α] : FinBddDistLat :=
  ⟨⟨⟨α⟩⟩⟩
#align FinBddDistLat.of FinBddDistLat.of

/-- Construct a bundled `FinBddDistLat` from a `nonempty` `bounded_order` `distrib_lattice`. -/
def of' (α : Type _) [DistribLattice α] [Fintype α] [Nonempty α] : FinBddDistLat :=
  haveI := Fintype.toBoundedOrder α
  ⟨⟨⟨α⟩⟩⟩
#align FinBddDistLat.of' FinBddDistLat.of'

instance : Inhabited FinBddDistLat :=
  ⟨of PUnit⟩

instance largeCategory : LargeCategory FinBddDistLat :=
  InducedCategory.category toBddDistLat
#align FinBddDistLat.large_category FinBddDistLat.largeCategory

instance concreteCategory : ConcreteCategory FinBddDistLat :=
  InducedCategory.concreteCategory toBddDistLat
#align FinBddDistLat.concrete_category FinBddDistLat.concreteCategory

instance hasForgetToBddDistLat : HasForget₂ FinBddDistLat BddDistLat :=
  InducedCategory.hasForget₂ FinBddDistLat.toBddDistLat
#align FinBddDistLat.has_forget_to_BddDistLat FinBddDistLat.hasForgetToBddDistLat

instance hasForgetToFinPartOrd : HasForget₂ FinBddDistLat FinPartOrd
    where forget₂ :=
    { obj := fun X => FinPartOrd.of X
      map := fun X Y f => (show BoundedLatticeHom X Y from f : X →o Y) }
#align FinBddDistLat.has_forget_to_FinPartOrd FinBddDistLat.hasForgetToFinPartOrd

/-- Constructs an equivalence between finite distributive lattices from an order isomorphism
between them. -/
@[simps]
def Iso.mk {α β : FinBddDistLat.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : BoundedLatticeHom α β)
  inv := (e.symm : BoundedLatticeHom β α)
  hom_inv_id' := by ext; exact e.symm_apply_apply _
  inv_hom_id' := by ext; exact e.apply_symm_apply _
#align FinBddDistLat.iso.mk FinBddDistLat.Iso.mk

example {X Y : FinBddDistLat} : (X ⟶ Y) = BoundedLatticeHom X Y :=
  rfl

/-- `order_dual` as a functor. -/
@[simps]
def dual : FinBddDistLat ⥤ FinBddDistLat where
  obj X := of Xᵒᵈ
  map X Y := BoundedLatticeHom.dual
#align FinBddDistLat.dual FinBddDistLat.dual

/-- The equivalence between `FinBddDistLat` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : FinBddDistLat ≌ FinBddDistLat :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align FinBddDistLat.dual_equiv FinBddDistLat.dualEquiv

end FinBddDistLat

theorem finBddDistLat_dual_comp_forget_to_bddDistLat :
    FinBddDistLat.dual ⋙ forget₂ FinBddDistLat BddDistLat =
      forget₂ FinBddDistLat BddDistLat ⋙ BddDistLat.dual :=
  rfl
#align FinBddDistLat_dual_comp_forget_to_BddDistLat finBddDistLat_dual_comp_forget_to_bddDistLat

