/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Category.BddLatCat
import Mathlib.Order.Category.DistLatCat

#align_import order.category.BddDistLat from "leanprover-community/mathlib"@"e8ac6315bcfcbaf2d19a046719c3b553206dac75"

/-!
# The category of bounded distributive lattices

This defines `BddDistLatCat`, the category of bounded distributive lattices.

Note that this category is sometimes called [`DistLat`](https://ncatlab.org/nlab/show/DistLat) when
being a lattice is understood to entail having a bottom and a top element.
-/

set_option linter.uppercaseLean3 false

universe u

open CategoryTheory

/-- The category of bounded distributive lattices with bounded lattice morphisms. -/
structure BddDistLatCat where
  toDistLatCat : DistLatCat
  [isBoundedOrder : BoundedOrder toDistLatCat]
#align BddDistLat BddDistLatCat

namespace BddDistLatCat

instance : CoeSort BddDistLatCat (Type*) :=
  ⟨fun X => X.toDistLatCat⟩

instance (X : BddDistLatCat) : DistribLattice X :=
  X.toDistLatCat.str

attribute [instance] BddDistLatCat.isBoundedOrder

/-- Construct a bundled `BddDistLatCat` from a `BoundedOrder` `DistribLattice`. -/
def of (α : Type*) [DistribLattice α] [BoundedOrder α] : BddDistLatCat :=
  -- Porting note: was `⟨⟨α⟩⟩`
  -- see https://github.com/leanprover-community/mathlib4/issues/4998
  ⟨{α := α}⟩
#align BddDistLat.of BddDistLatCat.of

@[simp]
theorem coe_of (α : Type*) [DistribLattice α] [BoundedOrder α] : ↥(of α) = α :=
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

instance hasForgetToDistLat : HasForget₂ BddDistLatCat DistLatCat where
  forget₂ :=
    -- Porting note: was `⟨X⟩`
    -- see https://github.com/leanprover-community/mathlib4/issues/4998
    { obj := fun X => { α := X }
      map := fun {X Y} => BoundedLatticeHom.toLatticeHom }
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
  hom := (e : BoundedLatticeHom α β)
  inv := (e.symm : BoundedLatticeHom β α)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _
#align BddDistLat.iso.mk BddDistLatCat.Iso.mk

/-- `OrderDual` as a functor. -/
@[simps]
def dual : BddDistLatCat ⥤ BddDistLatCat where
  obj X := of Xᵒᵈ
  map {X Y} := BoundedLatticeHom.dual
#align BddDistLat.dual BddDistLatCat.dual

/-- The equivalence between `BddDistLatCat` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
def dualEquiv : BddDistLatCat ≌ BddDistLatCat where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
#align BddDistLat.dual_equiv BddDistLatCat.dualEquiv

end BddDistLatCat

theorem bddDistLatCat_dual_comp_forget_to_distLatCat :
    BddDistLatCat.dual ⋙ forget₂ BddDistLatCat DistLatCat =
      forget₂ BddDistLatCat DistLatCat ⋙ DistLatCat.dual :=
  rfl
#align BddDistLat_dual_comp_forget_to_DistLat bddDistLatCat_dual_comp_forget_to_distLatCat
