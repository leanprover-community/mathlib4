/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Category.BddLat
import Mathlib.Order.Category.DistLat

#align_import order.category.BddDistLat from "leanprover-community/mathlib"@"e8ac6315bcfcbaf2d19a046719c3b553206dac75"

/-!
# The category of bounded distributive lattices

This defines `BddDistLat`, the category of bounded distributive lattices.

Note that this category is sometimes called [`DistLat`](https://ncatlab.org/nlab/show/DistLat) when
being a lattice is understood to entail having a bottom and a top element.
-/

set_option linter.uppercaseLean3 false

universe u

open CategoryTheory

/-- The category of bounded distributive lattices with bounded lattice morphisms. -/
structure BddDistLat where
  /-- The underlying distrib lattice of a bounded distributive lattice. -/
  toDistLat : DistLat
  [isBoundedOrder : BoundedOrder toDistLat]
#align BddDistLat BddDistLat

namespace BddDistLat

instance : CoeSort BddDistLat Type* :=
  ⟨fun X => X.toDistLat⟩

instance (X : BddDistLat) : DistribLattice X :=
  X.toDistLat.str

attribute [instance] BddDistLat.isBoundedOrder

/-- Construct a bundled `BddDistLat` from a `BoundedOrder` `DistribLattice`. -/
def of (α : Type*) [DistribLattice α] [BoundedOrder α] : BddDistLat :=
  -- Porting note: was `⟨⟨α⟩⟩`
  -- see https://github.com/leanprover-community/mathlib4/issues/4998
  ⟨{α := α}⟩
#align BddDistLat.of BddDistLat.of

@[simp]
theorem coe_of (α : Type*) [DistribLattice α] [BoundedOrder α] : ↥(of α) = α :=
  rfl
#align BddDistLat.coe_of BddDistLat.coe_of

instance : Inhabited BddDistLat :=
  ⟨of PUnit⟩

/-- Turn a `BddDistLat` into a `BddLat` by forgetting it is distributive. -/
def toBddLat (X : BddDistLat) : BddLat :=
  BddLat.of X
#align BddDistLat.to_BddLat BddDistLat.toBddLat

@[simp]
theorem coe_toBddLat (X : BddDistLat) : ↥X.toBddLat = ↥X :=
  rfl
#align BddDistLat.coe_to_BddLat BddDistLat.coe_toBddLat

instance : LargeCategory.{u} BddDistLat :=
  InducedCategory.category toBddLat

instance : ConcreteCategory BddDistLat :=
  InducedCategory.concreteCategory toBddLat

instance hasForgetToDistLat : HasForget₂ BddDistLat DistLat where
  forget₂ :=
    -- Porting note: was `⟨X⟩`
    -- see https://github.com/leanprover-community/mathlib4/issues/4998
    { obj := fun X => { α := X }
      map := fun {X Y} => BoundedLatticeHom.toLatticeHom }
#align BddDistLat.has_forget_to_DistLat BddDistLat.hasForgetToDistLat

instance hasForgetToBddLat : HasForget₂ BddDistLat BddLat :=
  InducedCategory.hasForget₂ toBddLat
#align BddDistLat.has_forget_to_BddLat BddDistLat.hasForgetToBddLat

theorem forget_bddLat_lat_eq_forget_distLat_lat :
    forget₂ BddDistLat BddLat ⋙ forget₂ BddLat Lat =
      forget₂ BddDistLat DistLat ⋙ forget₂ DistLat Lat :=
  rfl
#align BddDistLat.forget_BddLat_Lat_eq_forget_DistLat_Lat BddDistLat.forget_bddLat_lat_eq_forget_distLat_lat

/-- Constructs an equivalence between bounded distributive lattices from an order isomorphism
between them. -/
@[simps]
def Iso.mk {α β : BddDistLat.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : BoundedLatticeHom α β)
  inv := (e.symm : BoundedLatticeHom β α)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _
#align BddDistLat.iso.mk BddDistLat.Iso.mk

/-- `OrderDual` as a functor. -/
@[simps]
def dual : BddDistLat ⥤ BddDistLat where
  obj X := of Xᵒᵈ
  map {X Y} := BoundedLatticeHom.dual
#align BddDistLat.dual BddDistLat.dual

/-- The equivalence between `BddDistLat` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
def dualEquiv : BddDistLat ≌ BddDistLat where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
#align BddDistLat.dual_equiv BddDistLat.dualEquiv

end BddDistLat

theorem bddDistLat_dual_comp_forget_to_distLat :
    BddDistLat.dual ⋙ forget₂ BddDistLat DistLat =
      forget₂ BddDistLat DistLat ⋙ DistLat.dual :=
  rfl
#align BddDistLat_dual_comp_forget_to_DistLat bddDistLat_dual_comp_forget_to_distLat
