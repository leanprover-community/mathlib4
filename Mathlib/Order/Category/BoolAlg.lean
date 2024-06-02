/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Category.HeytAlg

#align_import order.category.BoolAlg from "leanprover-community/mathlib"@"e8ac6315bcfcbaf2d19a046719c3b553206dac75"

/-!
# The category of boolean algebras

This defines `BoolAlg`, the category of boolean algebras.
-/

set_option linter.uppercaseLean3 false

open OrderDual Opposite Set

universe u

open CategoryTheory

/-- The category of boolean algebras. -/
def BoolAlg :=
  Bundled BooleanAlgebra
#align BoolAlg BoolAlg

namespace BoolAlg

instance : CoeSort BoolAlg Type* :=
  Bundled.coeSort

instance instBooleanAlgebra (X : BoolAlg) : BooleanAlgebra X :=
  X.str

/-- Construct a bundled `BoolAlg` from a `BooleanAlgebra`. -/
def of (α : Type*) [BooleanAlgebra α] : BoolAlg :=
  Bundled.of α
#align BoolAlg.of BoolAlg.of

@[simp]
theorem coe_of (α : Type*) [BooleanAlgebra α] : ↥(of α) = α :=
  rfl
#align BoolAlg.coe_of BoolAlg.coe_of

instance : Inhabited BoolAlg :=
  ⟨of PUnit⟩

/-- Turn a `BoolAlg` into a `BddDistLat` by forgetting its complement operation. -/
def toBddDistLat (X : BoolAlg) : BddDistLat :=
  BddDistLat.of X
#align BoolAlg.to_BddDistLat BoolAlg.toBddDistLat

@[simp]
theorem coe_toBddDistLat (X : BoolAlg) : ↥X.toBddDistLat = ↥X :=
  rfl
#align BoolAlg.coe_to_BddDistLat BoolAlg.coe_toBddDistLat

instance : LargeCategory.{u} BoolAlg :=
  InducedCategory.category toBddDistLat

instance : ConcreteCategory BoolAlg :=
  InducedCategory.concreteCategory toBddDistLat

instance hasForgetToBddDistLat : HasForget₂ BoolAlg BddDistLat :=
  InducedCategory.hasForget₂ toBddDistLat
#align BoolAlg.has_forget_to_BddDistLat BoolAlg.hasForgetToBddDistLat

section

attribute [local instance] BoundedLatticeHomClass.toBiheytingHomClass

@[simps]
instance hasForgetToHeytAlg : HasForget₂ BoolAlg HeytAlg where
  forget₂ :=
    { obj := fun X => {α := X}
      -- Porting note: was `fun {X Y} f => show BoundedLatticeHom X Y from f`
      -- which already looks like a hack, but I don't understand why this hack works now and
      -- the old one didn't
      map := fun {X Y} (f : BoundedLatticeHom X Y) => show HeytingHom X Y from f }
#align BoolAlg.has_forget_to_HeytAlg BoolAlg.hasForgetToHeytAlg

end

/-- Constructs an equivalence between Boolean algebras from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : BoolAlg.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : BoundedLatticeHom α β)
  inv := (e.symm : BoundedLatticeHom β α)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _
#align BoolAlg.iso.mk BoolAlg.Iso.mk

/-- `OrderDual` as a functor. -/
@[simps]
def dual : BoolAlg ⥤ BoolAlg where
  obj X := of Xᵒᵈ
  map {X Y} := BoundedLatticeHom.dual
#align BoolAlg.dual BoolAlg.dual

/-- The equivalence between `BoolAlg` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
def dualEquiv : BoolAlg ≌ BoolAlg where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
#align BoolAlg.dual_equiv BoolAlg.dualEquiv

end BoolAlg

theorem boolAlg_dual_comp_forget_to_bddDistLat :
    BoolAlg.dual ⋙ forget₂ BoolAlg BddDistLat =
    forget₂ BoolAlg BddDistLat ⋙ BddDistLat.dual :=
  rfl
#align BoolAlg_dual_comp_forget_to_BddDistLat boolAlg_dual_comp_forget_to_bddDistLat
