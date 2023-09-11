/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Category.BddLatCat
import Mathlib.Order.Hom.CompleteLattice

#align_import order.category.CompleteLat from "leanprover-community/mathlib"@"e8ac6315bcfcbaf2d19a046719c3b553206dac75"

/-!
# The category of complete lattices

This file defines `CompleteLatCat`, the category of complete lattices.
-/

set_option linter.uppercaseLean3 false

universe u

open CategoryTheory

/-- The category of complete lattices. -/
def CompleteLatCat :=
  Bundled CompleteLattice
#align CompleteLat CompleteLatCat

namespace CompleteLatCat

instance : CoeSort CompleteLatCat (Type*) :=
  Bundled.coeSort

instance (X : CompleteLatCat) : CompleteLattice X :=
  X.str

/-- Construct a bundled `CompleteLatCat` from a `CompleteLattice`. -/
def of (α : Type*) [CompleteLattice α] : CompleteLatCat :=
  Bundled.of α
#align CompleteLat.of CompleteLatCat.of

@[simp]
theorem coe_of (α : Type*) [CompleteLattice α] : ↥(of α) = α :=
  rfl
#align CompleteLat.coe_of CompleteLatCat.coe_of

instance : Inhabited CompleteLatCat :=
  ⟨of PUnit⟩

instance : BundledHom @CompleteLatticeHom where
  toFun _ _ f := f.toFun
  id := @CompleteLatticeHom.id
  comp := @CompleteLatticeHom.comp
  hom_ext _ _ _ _ h := FunLike.coe_injective h

deriving instance LargeCategory for CompleteLatCat

instance : ConcreteCategory CompleteLatCat :=
  by dsimp [CompleteLatCat]; infer_instance

instance hasForgetToBddLat : HasForget₂ CompleteLatCat BddLatCat where
  forget₂ :=
    { obj := fun X => BddLatCat.of X
      map := fun {X Y} => CompleteLatticeHom.toBoundedLatticeHom }
  forget_comp := rfl
#align CompleteLat.has_forget_to_BddLat CompleteLatCat.hasForgetToBddLat

/-- Constructs an isomorphism of complete lattices from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : CompleteLatCat.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : CompleteLatticeHom _ _) -- Porting note: TODO, wrong?
  inv := (e.symm : CompleteLatticeHom _ _)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _
#align CompleteLat.iso.mk CompleteLatCat.Iso.mk

/-- `OrderDual` as a functor. -/
@[simps]
def dual : CompleteLatCat ⥤ CompleteLatCat where
  obj X := of Xᵒᵈ
  map {X Y} := CompleteLatticeHom.dual
#align CompleteLat.dual CompleteLatCat.dual

/-- The equivalence between `CompleteLatCat` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
def dualEquiv : CompleteLatCat ≌ CompleteLatCat where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
#align CompleteLat.dual_equiv CompleteLatCat.dualEquiv

end CompleteLatCat

theorem completeLatCat_dual_comp_forget_to_bddLatCat :
    CompleteLatCat.dual ⋙ forget₂ CompleteLatCat BddLatCat =
    forget₂ CompleteLatCat BddLatCat ⋙ BddLatCat.dual :=
  rfl
#align CompleteLat_dual_comp_forget_to_BddLat completeLatCat_dual_comp_forget_to_bddLatCat
