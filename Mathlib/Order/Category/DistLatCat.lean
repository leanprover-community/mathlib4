/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Category.LatCat

#align_import order.category.DistLat from "leanprover-community/mathlib"@"e8ac6315bcfcbaf2d19a046719c3b553206dac75"

/-!
# The category of distributive lattices

This file defines `DistLatCat`, the category of distributive lattices.

Note that [`DistLatCat`](https://ncatlab.org/nlab/show/DistLat) in the literature doesn't always
correspond to `DistLatCat` as we don't require bottom or top elements. Instead, this `DistLatCat`
corresponds to `BddDistLatCat`.
-/


universe u

open CategoryTheory

set_option linter.uppercaseLean3 false

/-- The category of distributive lattices. -/
def DistLatCat :=
  Bundled DistribLattice
#align DistLat DistLatCat

namespace DistLatCat

instance : CoeSort DistLatCat (Type*) :=
  Bundled.coeSort

instance (X : DistLatCat) : DistribLattice X :=
  X.str

/-- Construct a bundled `DistLatCat` from a `DistribLattice` underlying type and typeclass. -/
def of (α : Type*) [DistribLattice α] : DistLatCat :=
  Bundled.of α
#align DistLat.of DistLatCat.of

@[simp]
theorem coe_of (α : Type*) [DistribLattice α] : ↥(of α) = α :=
  rfl
#align DistLat.coe_of DistLatCat.coe_of

instance : Inhabited DistLatCat :=
  ⟨of PUnit⟩

instance : BundledHom.ParentProjection @DistribLattice.toLattice :=
  ⟨⟩

deriving instance LargeCategory for DistLatCat

-- Porting note: probably see https://github.com/leanprover-community/mathlib4/issues/5020
instance : ConcreteCategory DistLatCat :=
  BundledHom.concreteCategory _

instance hasForgetToLatCat : HasForget₂ DistLatCat LatCat :=
  BundledHom.forget₂ _ _
#align DistLat.has_forget_to_Lat DistLatCat.hasForgetToLatCat

/-- Constructs an equivalence between distributive lattices from an order isomorphism between them.
-/
@[simps]
def Iso.mk {α β : DistLatCat.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : LatticeHom α β)
  inv := (e.symm : LatticeHom β α)
  hom_inv_id := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id := by
    ext
    exact e.apply_symm_apply _
#align DistLat.iso.mk DistLatCat.Iso.mk

/-- `OrderDual` as a functor. -/
@[simps]
def dual : DistLatCat ⥤ DistLatCat where
  obj X := of Xᵒᵈ
  map := LatticeHom.dual
#align DistLat.dual DistLatCat.dual

/-- The equivalence between `DistLatCat` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
def dualEquiv : DistLatCat ≌ DistLatCat where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
#align DistLat.dual_equiv DistLatCat.dualEquiv

end DistLatCat

theorem distLatCat_dual_comp_forget_to_latCat :
    DistLatCat.dual ⋙ forget₂ DistLatCat LatCat = forget₂ DistLatCat LatCat ⋙ LatCat.dual :=
  rfl
#align DistLat_dual_comp_forget_to_Lat distLatCat_dual_comp_forget_to_latCat
