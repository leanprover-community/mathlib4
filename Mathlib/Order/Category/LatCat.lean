/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Category.PartOrdCat
import Mathlib.Order.Hom.Lattice

#align_import order.category.Lat from "leanprover-community/mathlib"@"e8ac6315bcfcbaf2d19a046719c3b553206dac75"

/-!
# The category of lattices

This defines `LatCat`, the category of lattices.

Note that `LatCat` doesn't correspond to the literature definition of [`LatCat`]
(https://ncatlab.org/nlab/show/Lat) as we don't require bottom or top elements. Instead, `LatCat`
corresponds to `BddLatCat`.

## TODO

The free functor from `LatCat` to `BddLat` is `X → WithTop (WithBot X)`.
-/


universe u

open CategoryTheory

/-- The category of lattices. -/
def LatCat :=
  Bundled Lattice
set_option linter.uppercaseLean3 false
#align Lat LatCat

namespace LatCat

instance : CoeSort LatCat (Type*) :=
  Bundled.coeSort

instance (X : LatCat) : Lattice X :=
  X.str

/-- Construct a bundled `LatCat` from a `Lattice`. -/
def of (α : Type*) [Lattice α] : LatCat :=
  Bundled.of α
#align Lat.of LatCat.of

@[simp]
theorem coe_of (α : Type*) [Lattice α] : ↥(of α) = α :=
  rfl
#align Lat.coe_of LatCat.coe_of

instance : Inhabited LatCat :=
  ⟨of Bool⟩

instance : BundledHom @LatticeHom where
  toFun _ _ f := f.toFun
  id := @LatticeHom.id
  comp := @LatticeHom.comp
  hom_ext _ _ _ _ h := FunLike.coe_injective h

instance : LargeCategory.{u} LatCat :=
  BundledHom.category LatticeHom

instance : ConcreteCategory LatCat :=
  BundledHom.concreteCategory LatticeHom

instance hasForgetToPartOrd : HasForget₂ LatCat PartOrdCat where
  forget₂ :=
    { obj := fun X => Bundled.mk X inferInstance
      map := fun {X Y} (f : LatticeHom X Y) => (f : OrderHom X Y) }
#align Lat.has_forget_to_PartOrd LatCat.hasForgetToPartOrd

/-- Constructs an isomorphism of lattices from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : LatCat.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : LatticeHom _ _)
  inv := (e.symm : LatticeHom _ _)
  hom_inv_id := by
    ext
    -- ⊢ ↑({ toSupHom := { toFun := ↑e, map_sup' := (_ : ∀ (a b : ↑α), ↑e (a ⊔ b) = ↑ …
    exact e.symm_apply_apply _
    -- 🎉 no goals
  inv_hom_id := by
    ext
    -- ⊢ ↑({ toSupHom := { toFun := ↑(OrderIso.symm e), map_sup' := (_ : ∀ (a b : ↑β) …
    exact e.apply_symm_apply _
    -- 🎉 no goals
#align Lat.iso.mk LatCat.Iso.mk

/-- `OrderDual` as a functor. -/
@[simps]
def dual : LatCat ⥤ LatCat where
  obj X := of Xᵒᵈ
  map := LatticeHom.dual
#align Lat.dual LatCat.dual

/-- The equivalence between `LatCat` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
def dualEquiv : LatCat ≌ LatCat where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
#align Lat.dual_equiv LatCat.dualEquiv

end LatCat

theorem latCat_dual_comp_forget_to_partOrdCat :
    LatCat.dual ⋙ forget₂ LatCat PartOrdCat = forget₂ LatCat PartOrdCat ⋙ PartOrdCat.dual :=
  rfl
#align Lat_dual_comp_forget_to_PartOrd latCat_dual_comp_forget_to_partOrdCat
