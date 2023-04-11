/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module order.category.LinOrd
! leanprover-community/mathlib commit e8ac6315bcfcbaf2d19a046719c3b553206dac75
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Order.Category.LatCat

/-!
# Category of linear orders

This defines `LinOrdCat`, the category of linear orders with monotone maps.
-/


open CategoryTheory

universe u

/-- The category of linear orders. -/
def LinOrdCat :=
  Bundled LinearOrder
set_option linter.uppercaseLean3 false in
#align LinOrd LinOrdCat

namespace LinOrdCat

instance : BundledHom.ParentProjection @LinearOrder.toPartialOrder :=
  ⟨⟩

deriving instance LargeCategory for LinOrdCat

instance : ConcreteCategory LinOrdCat :=
  BundledHom.concreteCategory _

instance : CoeSort LinOrdCat (Type _) :=
  Bundled.coeSort

/-- Construct a bundled `LinOrdCat` from the underlying type and typeclass. -/
def of (α : Type _) [LinearOrder α] : LinOrdCat :=
  Bundled.of α
set_option linter.uppercaseLean3 false in
#align LinOrd.of LinOrdCat.of

@[simp]
theorem coe_of (α : Type _) [LinearOrder α] : ↥(of α) = α :=
  rfl
set_option linter.uppercaseLean3 false in
#align LinOrd.coe_of LinOrdCat.coe_of

instance : Inhabited LinOrdCat :=
  ⟨of PUnit⟩

instance (α : LinOrdCat) : LinearOrder α :=
  α.str

instance hasForgetToLatCat : HasForget₂ LinOrdCat LatCat where
  forget₂ :=
    { obj := fun X => LatCat.of X
      map := fun {X Y} (f : OrderHom _ _) => OrderHomClass.toLatticeHom X Y f }
set_option linter.uppercaseLean3 false in
#align LinOrd.has_forget_to_Lat LinOrdCat.hasForgetToLatCat

/-- Constructs an equivalence between linear orders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : LinOrdCat.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : OrderHom _ _)
  inv := (e.symm : OrderHom _ _)
  hom_inv_id := by
    ext x
    exact e.symm_apply_apply x
  inv_hom_id := by
    ext x
    exact e.apply_symm_apply x
set_option linter.uppercaseLean3 false in
#align LinOrd.iso.mk LinOrdCat.Iso.mk

/-- `OrderDual` as a functor. -/
@[simps]
def dual : LinOrdCat ⥤ LinOrdCat where
  obj X := of Xᵒᵈ
  map := OrderHom.dual
set_option linter.uppercaseLean3 false in
#align LinOrd.dual LinOrdCat.dual

/-- The equivalence between `LinOrdCat` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
def dualEquiv : LinOrdCat ≌ LinOrdCat where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) (fun _ => rfl)
  counitIso := NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) (fun _ => rfl)
set_option linter.uppercaseLean3 false in
#align LinOrd.dual_equiv LinOrdCat.dualEquiv

end LinOrdCat

theorem linOrdCat_dual_comp_forget_to_latCat :
    LinOrdCat.dual ⋙ forget₂ LinOrdCat LatCat = forget₂ LinOrdCat LatCat ⋙ LatCat.dual :=
  rfl
set_option linter.uppercaseLean3 false in
#align LinOrd_dual_comp_forget_to_Lat linOrdCat_dual_comp_forget_to_latCat
