/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Category.PartOrd
import Mathlib.Order.Hom.Lattice

#align_import order.category.Lat from "leanprover-community/mathlib"@"e8ac6315bcfcbaf2d19a046719c3b553206dac75"

/-!
# The category of lattices

This defines `Lat`, the category of lattices.

Note that `Lat` doesn't correspond to the literature definition of [`Lat`]
(https://ncatlab.org/nlab/show/Lat) as we don't require bottom or top elements. Instead, `Lat`
corresponds to `BddLat`.

## TODO

The free functor from `Lat` to `BddLat` is `X → WithTop (WithBot X)`.
-/


universe u

open CategoryTheory

/-- The category of lattices. -/
def Lat :=
  Bundled Lattice
set_option linter.uppercaseLean3 false
#align Lat Lat

namespace Lat

instance : CoeSort Lat Type* :=
  Bundled.coeSort

instance (X : Lat) : Lattice X :=
  X.str

/-- Construct a bundled `Lat` from a `Lattice`. -/
def of (α : Type*) [Lattice α] : Lat :=
  Bundled.of α
#align Lat.of Lat.of

@[simp]
theorem coe_of (α : Type*) [Lattice α] : ↥(of α) = α :=
  rfl
#align Lat.coe_of Lat.coe_of

instance : Inhabited Lat :=
  ⟨of Bool⟩

instance : BundledHom @LatticeHom where
  toFun _ _ f := f.toFun
  id := @LatticeHom.id
  comp := @LatticeHom.comp
  hom_ext _ _ _ _ h := DFunLike.coe_injective h

instance : LargeCategory.{u} Lat :=
  BundledHom.category LatticeHom

instance : ConcreteCategory Lat :=
  BundledHom.concreteCategory LatticeHom

instance hasForgetToPartOrd : HasForget₂ Lat PartOrd where
  forget₂ :=
    { obj := fun X => Bundled.mk X inferInstance
      map := fun {X Y} (f : LatticeHom X Y) => (f : OrderHom X Y) }
#align Lat.has_forget_to_PartOrd Lat.hasForgetToPartOrd

/-- Constructs an isomorphism of lattices from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : Lat.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : LatticeHom _ _)
  inv := (e.symm : LatticeHom _ _)
  hom_inv_id := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id := by
    ext
    exact e.apply_symm_apply _
#align Lat.iso.mk Lat.Iso.mk

/-- `OrderDual` as a functor. -/
@[simps]
def dual : Lat ⥤ Lat where
  obj X := of Xᵒᵈ
  map := LatticeHom.dual
#align Lat.dual Lat.dual

/-- The equivalence between `Lat` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
def dualEquiv : Lat ≌ Lat where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
#align Lat.dual_equiv Lat.dualEquiv

end Lat

theorem Lat_dual_comp_forget_to_partOrd :
    Lat.dual ⋙ forget₂ Lat PartOrd = forget₂ Lat PartOrd ⋙ PartOrd.dual :=
  rfl
#align Lat_dual_comp_forget_to_PartOrd Lat_dual_comp_forget_to_partOrd
