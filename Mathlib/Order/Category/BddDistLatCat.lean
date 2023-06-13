/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.category.BddDistLat
! leanprover-community/mathlib commit e8ac6315bcfcbaf2d19a046719c3b553206dac75
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Order.Category.BddLatCat
import Mathlib.Order.Category.DistLatCat

/-!
# The category of bounded distributive lattices

This defines `BddDistLatCat`, the category of bounded distributive lattices.

Note that this category is sometimes called [`DistLat`](https://ncatlab.org/nlab/show/DistLat) when
being a lattice is understood to entail having a bottom and a top element.
-/


universe u

open CategoryTheory

/-- The category of bounded distributive lattices with bounded lattice morphisms. -/
structure BddDistLatCat where
  toDistLatCat : DistLatCat
  [isBoundedOrder : BoundedOrderCat to_DistLat]
#align BddDistLat BddDistLatCat

namespace BddDistLatCat

instance : CoeSort BddDistLatCat (Type _) :=
  ⟨fun X => X.toDistLat⟩

instance (X : BddDistLat) : DistribLattice X :=
  X.toDistLat.str

attribute [instance] BddDistLatCat.isBoundedOrder

/-- Construct a bundled `BddDistLatCat` from a `bounded_order` `distrib_lattice`. -/
def of (α : Type _) [DistribLattice α] [BoundedOrder α] : BddDistLat :=
  ⟨⟨α⟩⟩
#align BddDistLat.of BddDistLatCat.of

@[simp]
theorem coe_of (α : Type _) [DistribLattice α] [BoundedOrder α] : ↥(of α) = α :=
  rfl
#align BddDistLat.coe_of BddDistLatCat.coe_of

instance : Inhabited BddDistLatCat :=
  ⟨of PUnit⟩

/-- Turn a `BddDistLatCat` into a `BddLatCat` by forgetting it is distributive. -/
def toBddLat (X : BddDistLatCat) : BddLatCat :=
  BddLatCat.of X
#align BddDistLat.to_BddLat BddDistLatCat.toBddLat

@[simp]
theorem coe_toBddLat (X : BddDistLatCat) : ↥X.toBddLat = ↥X :=
  rfl
#align BddDistLatCat.coe_to_BddLat BddDistLatCat.coe_toBddLat

instance : LargeCategory.{u} BddDistLatCat :=
  InducedCategory.category toBddLat

instance : ConcreteCategory BddDistLatCat :=
  InducedCategory.concreteCategory toBddLat

instance hasForgetToDistLat : HasForget₂ BddDistLatCat DistLatCat
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y => BoundedLatticeHom.toLatticeHom }
#align BddDistLat.has_forget_to_DistLat BddDistLatCat.hasForgetToDistLat

instance hasForgetToBddLat : HasForget₂ BddDistLatCat BddLatCat :=
  InducedCategory.hasForget₂ toBddLat
#align BddDistLat.has_forget_to_BddLat BddDistLatCat.hasForgetToBddLat

theorem forget_bddLat_latCat_eq_forget_distLatCat_latCat :
    forget₂ BddDistLatCat BddLatCat ⋙ forget₂ BddLatCat LatCat =
      forget₂ BddDistLatCat DistLatCat ⋙ forget₂ DistLatCat LatCat :=
  rfl
#align BddDistLat.forget_BddLat_Lat_eq_forget_DistLat_Lat BddDistLatCat.forget_bddLat_latCat_eq_forget_distLatCat_latCat

/-- Constructs an equivalence between bounded distributive lattices from an order isomorphism
between them. -/
@[simps]
def Iso.mk {α β : BddDistLatCat.{u}} (e : α ≃o β) : α ≅ β where
  Hom := (e : BoundedLatticeHom α β)
  inv := (e.symm : BoundedLatticeHom β α)
  hom_inv_id' := by ext; exact e.symm_apply_apply _
  inv_hom_id' := by ext; exact e.apply_symm_apply _
#align BddDistLat.iso.mk BddDistLatCat.Iso.mk

/-- `order_dual` as a functor. -/
@[simps]
def dual : BddDistLatCat ⥤ BddDistLatCat where
  obj X := of Xᵒᵈ
  map X Y := BoundedLatticeHom.dual
#align BddDistLat.dual BddDistLatCat.dual

/-- The equivalence between `BddDistLatCat` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : BddDistLatCat ≌ BddDistLatCat :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align BddDistLat.dual_equiv BddDistLatCat.dualEquiv

end BddDistLat

theorem bddDistLat_dual_comp_forget_to_distLatCat :
    BddDistLatCat.dual ⋙ forget₂ BddDistLatCat DistLatCat =
      forget₂ BddDistLatCat DistLatCat ⋙ DistLatCat.dual :=
  rfl
#align BddDistLat_dual_comp_forget_to_DistLat bddDistLatCat_dual_comp_forget_to_distLatCat
