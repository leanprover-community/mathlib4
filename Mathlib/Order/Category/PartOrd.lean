/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Order.Antisymmetrization
import Mathlib.Order.Category.Preord
import Mathlib.CategoryTheory.Adjunction.Basic

#align_import order.category.PartOrd from "leanprover-community/mathlib"@"e8ac6315bcfcbaf2d19a046719c3b553206dac75"

/-!
# Category of partial orders

This defines `PartOrd`, the category of partial orders with monotone maps.
-/


open CategoryTheory

universe u

/-- The category of partially ordered types. -/
def PartOrd :=
  Bundled PartialOrder
set_option linter.uppercaseLean3 false in
#align PartOrd PartOrd

namespace PartOrd

instance : BundledHom.ParentProjection @PartialOrder.toPreorder :=
  ⟨⟩

deriving instance LargeCategory for PartOrd

-- Porting note: probably see https://github.com/leanprover-community/mathlib4/issues/5020
instance : ConcreteCategory PartOrd :=
  BundledHom.concreteCategory _

instance : CoeSort PartOrd Type* :=
  Bundled.coeSort

/-- Construct a bundled PartOrd from the underlying type and typeclass. -/
def of (α : Type*) [PartialOrder α] : PartOrd :=
  Bundled.of α
set_option linter.uppercaseLean3 false in
#align PartOrd.of PartOrd.of

@[simp]
theorem coe_of (α : Type*) [PartialOrder α] : ↥(of α) = α :=
  rfl
set_option linter.uppercaseLean3 false in
#align PartOrd.coe_of PartOrd.coe_of

instance : Inhabited PartOrd :=
  ⟨of PUnit⟩

instance (α : PartOrd) : PartialOrder α :=
  α.str

instance hasForgetToPreord : HasForget₂ PartOrd Preord :=
  BundledHom.forget₂ _ _
set_option linter.uppercaseLean3 false in
#align PartOrd.has_forget_to_Preord PartOrd.hasForgetToPreord

/-- Constructs an equivalence between partial orders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : PartOrd.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : OrderHom α β)
  inv := (e.symm : OrderHom β α)
  hom_inv_id := by
    ext x
    exact e.symm_apply_apply x
  inv_hom_id := by
    ext x
    exact e.apply_symm_apply x
set_option linter.uppercaseLean3 false in
#align PartOrd.iso.mk PartOrd.Iso.mk

/-- `OrderDual` as a functor. -/
@[simps]
def dual : PartOrd ⥤ PartOrd where
  obj X := of Xᵒᵈ
  map := OrderHom.dual
set_option linter.uppercaseLean3 false in
#align PartOrd.dual PartOrd.dual

/-- The equivalence between `PartOrd` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
def dualEquiv : PartOrd ≌ PartOrd where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
set_option linter.uppercaseLean3 false in
#align PartOrd.dual_equiv PartOrd.dualEquiv

end PartOrd

theorem partOrd_dual_comp_forget_to_preord :
    PartOrd.dual ⋙ forget₂ PartOrd Preord =
      forget₂ PartOrd Preord ⋙ Preord.dual :=
  rfl
set_option linter.uppercaseLean3 false in
#align PartOrd_dual_comp_forget_to_Preord partOrd_dual_comp_forget_to_preord

/-- `Antisymmetrization` as a functor. It is the free functor. -/
def preordToPartOrd : Preord.{u} ⥤ PartOrd where
  obj X := PartOrd.of (Antisymmetrization X (· ≤ ·))
  map f := f.antisymmetrization
  map_id X := by
    ext x
    exact Quotient.inductionOn' x fun x => Quotient.map'_mk'' _ (fun a b => id) _
  map_comp f g := by
    ext x
    exact Quotient.inductionOn' x fun x => OrderHom.antisymmetrization_apply_mk _ _
set_option linter.uppercaseLean3 false in
#align Preord_to_PartOrd preordToPartOrd

/-- `preordToPartOrd` is left adjoint to the forgetful functor, meaning it is the free
functor from `Preord` to `PartOrd`. -/
def preordToPartOrdForgetAdjunction :
    preordToPartOrd.{u} ⊣ forget₂ PartOrd Preord :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ =>
        { toFun := fun f =>
            ⟨f.toFun ∘ toAntisymmetrization (· ≤ ·), f.mono.comp toAntisymmetrization_mono⟩
          invFun := fun f =>
            ⟨fun a => Quotient.liftOn' a f.toFun (fun _ _ h => (AntisymmRel.image h f.mono).eq),
              fun a b => Quotient.inductionOn₂' a b fun _ _ h => f.mono h⟩
          left_inv := fun _ =>
            OrderHom.ext _ _ <| funext fun x => Quotient.inductionOn' x fun _ => rfl
          right_inv := fun _ => OrderHom.ext _ _ <| funext fun _ => rfl }
      homEquiv_naturality_left_symm := fun _ _ =>
        OrderHom.ext _ _ <| funext fun x => Quotient.inductionOn' x fun _ => rfl
      homEquiv_naturality_right := fun _ _ => OrderHom.ext _ _ <| funext fun _ => rfl }
set_option linter.uppercaseLean3 false in
#align Preord_to_PartOrd_forget_adjunction preordToPartOrdForgetAdjunction

-- The `simpNF` linter would complain as `Functor.comp_obj`, `Preord.dual_obj` both apply to LHS
-- of `preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd_hom_app_coe`
/-- `PreordToPartOrd` and `OrderDual` commute. -/
@[simps! inv_app_coe, simps! (config := .lemmasOnly) hom_app_coe]
def preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd :
    preordToPartOrd.{u} ⋙ PartOrd.dual ≅ Preord.dual ⋙ preordToPartOrd :=
  NatIso.ofComponents (fun _ => PartOrd.Iso.mk <| OrderIso.dualAntisymmetrization _)
    (fun _ => OrderHom.ext _ _ <| funext fun x => Quotient.inductionOn' x fun _ => rfl)
set_option linter.uppercaseLean3 false in
#align Preord_to_PartOrd_comp_to_dual_iso_to_dual_comp_Preord_to_PartOrd preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd

-- This lemma was always bad, but the linter only noticed after lean4#2644
attribute [nolint simpNF] preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd_inv_app_coe
