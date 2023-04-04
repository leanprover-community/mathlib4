/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module order.category.PartOrd
! leanprover-community/mathlib commit e8ac6315bcfcbaf2d19a046719c3b553206dac75
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Antisymmetrization
import Mathbin.Order.Category.Preord

/-!
# Category of partial orders

This defines `PartOrd`, the category of partial orders with monotone maps.
-/


open CategoryTheory

universe u

/-- The category of partially ordered types. -/
def PartOrd :=
  Bundled PartialOrder
#align PartOrd PartOrd

namespace PartOrd

instance : BundledHom.ParentProjection @PartialOrder.toPreorder :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for PartOrd

instance : CoeSort PartOrd (Type _) :=
  Bundled.hasCoeToSort

/-- Construct a bundled PartOrd from the underlying type and typeclass. -/
def of (α : Type _) [PartialOrder α] : PartOrd :=
  Bundled.of α
#align PartOrd.of PartOrd.of

@[simp]
theorem coe_of (α : Type _) [PartialOrder α] : ↥(of α) = α :=
  rfl
#align PartOrd.coe_of PartOrd.coe_of

instance : Inhabited PartOrd :=
  ⟨of PUnit⟩

instance (α : PartOrd) : PartialOrder α :=
  α.str

instance hasForgetToPreord : HasForget₂ PartOrd Preord :=
  BundledHom.forget₂ _ _
#align PartOrd.has_forget_to_Preord PartOrd.hasForgetToPreord

/-- Constructs an equivalence between partial orders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : PartOrd.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply x
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply x
#align PartOrd.iso.mk PartOrd.Iso.mk

/-- `order_dual` as a functor. -/
@[simps]
def dual : PartOrd ⥤ PartOrd where
  obj X := of Xᵒᵈ
  map X Y := OrderHom.dual
#align PartOrd.dual PartOrd.dual

/-- The equivalence between `PartOrd` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : PartOrd ≌ PartOrd :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align PartOrd.dual_equiv PartOrd.dualEquiv

end PartOrd

theorem partOrd_dual_comp_forget_to_preord :
    PartOrd.dual ⋙ forget₂ PartOrd Preord = forget₂ PartOrd Preord ⋙ Preord.dual :=
  rfl
#align PartOrd_dual_comp_forget_to_Preord partOrd_dual_comp_forget_to_preord

/-- `antisymmetrization` as a functor. It is the free functor. -/
def preordToPartOrd : Preord.{u} ⥤ PartOrd
    where
  obj X := PartOrd.of (Antisymmetrization X (· ≤ ·))
  map X Y f := f.Antisymmetrization
  map_id' X := by
    ext
    exact Quotient.inductionOn' x fun x => Quotient.map'_mk'' _ (fun a b => id) _
  map_comp' X Y Z f g := by
    ext
    exact Quotient.inductionOn' x fun x => OrderHom.antisymmetrization_apply_mk _ _
#align Preord_to_PartOrd preordToPartOrd

/-- `Preord_to_PartOrd` is left adjoint to the forgetful functor, meaning it is the free
functor from `Preord` to `PartOrd`. -/
def preordToPartOrdForgetAdjunction : preordToPartOrd.{u} ⊣ forget₂ PartOrd Preord :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f =>
            ⟨f ∘ toAntisymmetrization (· ≤ ·), f.mono.comp toAntisymmetrization_mono⟩
          invFun := fun f =>
            ⟨fun a => Quotient.liftOn' a f fun a b h => (AntisymmRel.image h f.mono).Eq, fun a b =>
              Quotient.inductionOn₂' a b fun a b h => f.mono h⟩
          left_inv := fun f =>
            OrderHom.ext _ _ <| funext fun x => Quotient.inductionOn' x fun x => rfl
          right_inv := fun f => OrderHom.ext _ _ <| funext fun x => rfl }
      homEquiv_naturality_left_symm := fun X Y Z f g =>
        OrderHom.ext _ _ <| funext fun x => Quotient.inductionOn' x fun x => rfl
      homEquiv_naturality_right := fun X Y Z f g => OrderHom.ext _ _ <| funext fun x => rfl }
#align Preord_to_PartOrd_forget_adjunction preordToPartOrdForgetAdjunction

/-- `Preord_to_PartOrd` and `order_dual` commute. -/
@[simps]
def preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd :
    preordToPartOrd.{u} ⋙ PartOrd.dual ≅ Preord.dual ⋙ preordToPartOrd :=
  NatIso.ofComponents (fun X => PartOrd.Iso.mk <| OrderIso.dualAntisymmetrization _) fun X Y f =>
    OrderHom.ext _ _ <| funext fun x => Quotient.inductionOn' x fun x => rfl
#align Preord_to_PartOrd_comp_to_dual_iso_to_dual_comp_Preord_to_PartOrd preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd

