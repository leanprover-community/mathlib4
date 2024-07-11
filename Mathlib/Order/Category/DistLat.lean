/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Category.Lat

#align_import order.category.DistLat from "leanprover-community/mathlib"@"e8ac6315bcfcbaf2d19a046719c3b553206dac75"

/-!
# The category of distributive lattices

This file defines `DistLat`, the category of distributive lattices.

Note that [`DistLat`](https://ncatlab.org/nlab/show/DistLat) in the literature doesn't always
correspond to `DistLat` as we don't require bottom or top elements. Instead, this `DistLat`
corresponds to `BddDistLat`.
-/


universe u

open CategoryTheory

set_option linter.uppercaseLean3 false

/-- The category of distributive lattices. -/
def DistLat :=
  Bundled DistribLattice
#align DistLat DistLat

namespace DistLat

instance : CoeSort DistLat Type* :=
  Bundled.coeSort

instance (X : DistLat) : DistribLattice X :=
  X.str

/-- Construct a bundled `DistLat` from a `DistribLattice` underlying type and typeclass. -/
def of (α : Type*) [DistribLattice α] : DistLat :=
  Bundled.of α
#align DistLat.of DistLat.of

@[simp]
theorem coe_of (α : Type*) [DistribLattice α] : ↥(of α) = α :=
  rfl
#align DistLat.coe_of DistLat.coe_of

instance : Inhabited DistLat :=
  ⟨of PUnit⟩

instance : BundledHom.ParentProjection @DistribLattice.toLattice :=
  ⟨⟩

deriving instance LargeCategory for DistLat

instance : ConcreteCategory DistLat :=
  BundledHom.concreteCategory _

instance hasForgetToLat : HasForget₂ DistLat Lat :=
  BundledHom.forget₂ _ _
#align DistLat.has_forget_to_Lat DistLat.hasForgetToLat

/-- Constructs an equivalence between distributive lattices from an order isomorphism between them.
-/
@[simps]
def Iso.mk {α β : DistLat.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : LatticeHom α β)
  inv := (e.symm : LatticeHom β α)
  hom_inv_id := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id := by
    ext
    exact e.apply_symm_apply _
#align DistLat.iso.mk DistLat.Iso.mk

/-- `OrderDual` as a functor. -/
@[simps]
def dual : DistLat ⥤ DistLat where
  obj X := of Xᵒᵈ
  map := LatticeHom.dual
#align DistLat.dual DistLat.dual

/-- The equivalence between `DistLat` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
def dualEquiv : DistLat ≌ DistLat where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun _ => rfl
  counitIso := NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun _ => rfl
#align DistLat.dual_equiv DistLat.dualEquiv

end DistLat

theorem distLat_dual_comp_forget_to_Lat :
    DistLat.dual ⋙ forget₂ DistLat Lat = forget₂ DistLat Lat ⋙ Lat.dual :=
  rfl
#align DistLat_dual_comp_forget_to_Lat distLat_dual_comp_forget_to_Lat
