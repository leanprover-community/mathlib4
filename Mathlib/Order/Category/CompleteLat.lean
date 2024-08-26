/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Category.BddLat
import Mathlib.Order.Hom.CompleteLattice

/-!
# The category of complete lattices

This file defines `CompleteLat`, the category of complete lattices.
-/


universe u

open CategoryTheory

/-- The category of complete lattices. -/
def CompleteLat :=
  Bundled CompleteLattice

namespace CompleteLat

instance : CoeSort CompleteLat Type* :=
  Bundled.coeSort

instance (X : CompleteLat) : CompleteLattice X :=
  X.str

/-- Construct a bundled `CompleteLat` from a `CompleteLattice`. -/
def of (α : Type*) [CompleteLattice α] : CompleteLat :=
  Bundled.of α

@[simp]
theorem coe_of (α : Type*) [CompleteLattice α] : ↥(of α) = α :=
  rfl

instance : Inhabited CompleteLat :=
  ⟨of PUnit⟩

instance : BundledHom @CompleteLatticeHom where
  toFun _ _ f := f.toFun
  id := @CompleteLatticeHom.id
  comp := @CompleteLatticeHom.comp
  hom_ext _ _ _ _ h := DFunLike.coe_injective h

deriving instance LargeCategory for CompleteLat

instance : ConcreteCategory CompleteLat := by
  dsimp [CompleteLat]; infer_instance

instance hasForgetToBddLat : HasForget₂ CompleteLat BddLat where
  forget₂ :=
    { obj := fun X => BddLat.of X
      map := fun {X Y} => CompleteLatticeHom.toBoundedLatticeHom }
  forget_comp := rfl

/-- Constructs an isomorphism of complete lattices from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : CompleteLat.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : CompleteLatticeHom _ _) -- Porting note (#11215): TODO, wrong?
  inv := (e.symm : CompleteLatticeHom _ _)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

/-- `OrderDual` as a functor. -/
@[simps]
def dual : CompleteLat ⥤ CompleteLat where
  obj X := of Xᵒᵈ
  map {X Y} := CompleteLatticeHom.dual

/-- The equivalence between `CompleteLat` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
def dualEquiv : CompleteLat ≌ CompleteLat where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X

end CompleteLat

theorem completeLat_dual_comp_forget_to_bddLat :
    CompleteLat.dual ⋙ forget₂ CompleteLat BddLat =
    forget₂ CompleteLat BddLat ⋙ BddLat.dual :=
  rfl
