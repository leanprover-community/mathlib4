/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Fintype.Order
import Mathlib.Order.Category.BddDistLatCat
import Mathlib.Order.Category.FinPartOrd

#align_import order.category.FinBddDistLat from "leanprover-community/mathlib"@"937b1c59c58710ef8ed91f8727ef402d49d621a2"

/-!
# The category of finite bounded distributive lattices

This file defines `FinBddDistLatCat`, the category of finite distributive lattices with
bounded lattice homomorphisms.
-/

set_option linter.uppercaseLean3 false

universe u

open CategoryTheory

/-- The category of finite distributive lattices with bounded lattice morphisms. -/
structure FinBddDistLatCat where
  toBddDistLatCat : BddDistLatCat
  [isFintype : Fintype toBddDistLatCat]
#align FinBddDistLat FinBddDistLatCat

namespace FinBddDistLatCat

instance : CoeSort FinBddDistLatCat (Type*) :=
  ⟨fun X => X.toBddDistLatCat⟩

instance (X : FinBddDistLatCat) : DistribLattice X :=
  X.toBddDistLatCat.toDistLatCat.str

instance (X : FinBddDistLatCat) : BoundedOrder X :=
  X.toBddDistLatCat.isBoundedOrder

attribute [instance] FinBddDistLatCat.isFintype

/-- Construct a bundled `FinBddDistLatCat` from a `Nonempty` `BoundedOrder` `DistribLattice`. -/
def of (α : Type*) [DistribLattice α] [BoundedOrder α] [Fintype α] : FinBddDistLatCat :=
  -- Porting note: was `⟨⟨⟨α⟩⟩⟩`
  -- see https://github.com/leanprover-community/mathlib4/issues/4998
  ⟨⟨{α := α}⟩⟩
#align FinBddDistLat.of FinBddDistLatCat.of

/-- Construct a bundled `FinBddDistLatCat` from a `Nonempty` `BoundedOrder` `DistribLattice`. -/
def of' (α : Type*) [DistribLattice α] [Fintype α] [Nonempty α] : FinBddDistLatCat :=
  haveI := Fintype.toBoundedOrder α
  -- Porting note: was `⟨⟨⟨α⟩⟩⟩`
  -- see https://github.com/leanprover-community/mathlib4/issues/4998
  ⟨⟨{α := α}⟩⟩
#align FinBddDistLat.of' FinBddDistLatCat.of'

instance : Inhabited FinBddDistLatCat :=
  ⟨of PUnit⟩

instance largeCategory : LargeCategory FinBddDistLatCat :=
  InducedCategory.category toBddDistLatCat
#align FinBddDistLat.large_category FinBddDistLatCat.largeCategory

instance concreteCategory : ConcreteCategory FinBddDistLatCat :=
  InducedCategory.concreteCategory toBddDistLatCat
#align FinBddDistLat.concrete_category FinBddDistLatCat.concreteCategory

instance hasForgetToBddDistLatCat : HasForget₂ FinBddDistLatCat BddDistLatCat :=
  InducedCategory.hasForget₂ FinBddDistLatCat.toBddDistLatCat
#align FinBddDistLat.has_forget_to_BddDistLat FinBddDistLatCat.hasForgetToBddDistLatCat

instance hasForgetToFinPartOrd : HasForget₂ FinBddDistLatCat FinPartOrd
    where forget₂ :=
    { obj := fun X => FinPartOrd.of X
      map := fun {X Y} f => (show BoundedLatticeHom X Y from f : X →o Y) }
#align FinBddDistLat.has_forget_to_FinPartOrd FinBddDistLatCat.hasForgetToFinPartOrd

/-- Constructs an equivalence between finite distributive lattices from an order isomorphism
between them. -/
@[simps]
def Iso.mk {α β : FinBddDistLatCat.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : BoundedLatticeHom α β)
  inv := (e.symm : BoundedLatticeHom β α)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _
#align FinBddDistLat.iso.mk FinBddDistLatCat.Iso.mk

example {X Y : FinBddDistLatCat} : (X ⟶ Y) = BoundedLatticeHom X Y :=
  rfl

/-- `OrderDual` as a functor. -/
@[simps]
def dual : FinBddDistLatCat ⥤ FinBddDistLatCat where
  obj X := of Xᵒᵈ
  map {X Y} := BoundedLatticeHom.dual
#align FinBddDistLat.dual FinBddDistLatCat.dual

/-- The equivalence between `FinBddDistLatCat` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
def dualEquiv : FinBddDistLatCat ≌ FinBddDistLatCat where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
#align FinBddDistLat.dual_equiv FinBddDistLatCat.dualEquiv

end FinBddDistLatCat

theorem finBddDistLatCat_dual_comp_forget_to_bddDistLatCat :
    FinBddDistLatCat.dual ⋙ forget₂ FinBddDistLatCat BddDistLatCat =
      forget₂ FinBddDistLatCat BddDistLatCat ⋙ BddDistLatCat.dual :=
  rfl
#align FinBddDistLat_dual_comp_forget_to_BddDistLat finBddDistLatCat_dual_comp_forget_to_bddDistLatCat
