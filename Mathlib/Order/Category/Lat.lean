/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.category.Lat
! leanprover-community/mathlib commit e8ac6315bcfcbaf2d19a046719c3b553206dac75
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Category.PartOrd
import Mathbin.Order.Hom.Lattice

/-!
# The category of lattices

This defines `Lat`, the category of lattices.

Note that `Lat` doesn't correspond to the literature definition of [`Lat`]
(https://ncatlab.org/nlab/show/Lat) as we don't require bottom or top elements. Instead, `Lat`
corresponds to `BddLat`.

## TODO

The free functor from `Lat` to `BddLat` is `X → with_top (with_bot X)`.
-/


universe u

open CategoryTheory

/-- The category of lattices. -/
def Lat :=
  Bundled Lattice
#align Lat Lat

namespace Lat

instance : CoeSort Lat (Type _) :=
  Bundled.hasCoeToSort

instance (X : Lat) : Lattice X :=
  X.str

/-- Construct a bundled `Lat` from a `lattice`. -/
def of (α : Type _) [Lattice α] : Lat :=
  Bundled.of α
#align Lat.of Lat.of

@[simp]
theorem coe_of (α : Type _) [Lattice α] : ↥(of α) = α :=
  rfl
#align Lat.coe_of Lat.coe_of

instance : Inhabited Lat :=
  ⟨of Bool⟩

instance : BundledHom @LatticeHom where
  toFun _ _ _ _ := coeFn
  id := @LatticeHom.id
  comp := @LatticeHom.comp
  hom_ext X Y _ _ := FunLike.coe_injective

instance : LargeCategory.{u} Lat :=
  BundledHom.category LatticeHom

instance : ConcreteCategory Lat :=
  BundledHom.concreteCategory LatticeHom

instance hasForgetToPartOrd : HasForget₂ Lat PartOrd
    where
  forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y f => f }
  forget_comp := rfl
#align Lat.has_forget_to_PartOrd Lat.hasForgetToPartOrd

/-- Constructs an isomorphism of lattices from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : Lat.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply _
#align Lat.iso.mk Lat.Iso.mk

/-- `order_dual` as a functor. -/
@[simps]
def dual : Lat ⥤ Lat where
  obj X := of Xᵒᵈ
  map X Y := LatticeHom.dual
#align Lat.dual Lat.dual

/-- The equivalence between `Lat` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : Lat ≌ Lat :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align Lat.dual_equiv Lat.dualEquiv

end Lat

theorem lat_dual_comp_forget_to_partOrd :
    Lat.dual ⋙ forget₂ Lat PartOrd = forget₂ Lat PartOrd ⋙ PartOrd.dual :=
  rfl
#align Lat_dual_comp_forget_to_PartOrd lat_dual_comp_forget_to_partOrd

