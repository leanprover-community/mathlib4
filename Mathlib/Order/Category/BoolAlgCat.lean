/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Category.HeytAlgCat

#align_import order.category.BoolAlg from "leanprover-community/mathlib"@"e8ac6315bcfcbaf2d19a046719c3b553206dac75"

/-!
# The category of boolean algebras

This defines `BoolAlgCat`, the category of boolean algebras.
-/

set_option linter.uppercaseLean3 false

open OrderDual Opposite Set

universe u

open CategoryTheory

/-- The category of boolean algebras. -/
def BoolAlgCat :=
  Bundled BooleanAlgebra
#align BoolAlg BoolAlgCat

namespace BoolAlgCat

instance : CoeSort BoolAlgCat (Type*) :=
  Bundled.coeSort

instance instBooleanAlgebra (X : BoolAlgCat) : BooleanAlgebra X :=
  X.str

/-- Construct a bundled `BoolAlgCat` from a `BooleanAlgebra`. -/
def of (α : Type*) [BooleanAlgebra α] : BoolAlgCat :=
  Bundled.of α
#align BoolAlg.of BoolAlgCat.of

@[simp]
theorem coe_of (α : Type*) [BooleanAlgebra α] : ↥(of α) = α :=
  rfl
#align BoolAlg.coe_of BoolAlgCat.coe_of

instance : Inhabited BoolAlgCat :=
  ⟨of PUnit⟩

/-- Turn a `BoolAlg` into a `BddDistLat` by forgetting its complement operation. -/
def toBddDistLatCat (X : BoolAlgCat) : BddDistLatCat :=
  BddDistLatCat.of X
#align BoolAlg.to_BddDistLat BoolAlgCat.toBddDistLatCat

@[simp]
theorem coe_toBddDistLatCat (X : BoolAlgCat) : ↥X.toBddDistLatCat = ↥X :=
  rfl
#align BoolAlg.coe_to_BddDistLat BoolAlgCat.coe_toBddDistLatCat

instance : LargeCategory.{u} BoolAlgCat :=
  InducedCategory.category toBddDistLatCat

instance : ConcreteCategory BoolAlgCat :=
  InducedCategory.concreteCategory toBddDistLatCat

instance hasForgetToBddDistLatCat : HasForget₂ BoolAlgCat BddDistLatCat :=
  InducedCategory.hasForget₂ toBddDistLatCat
#align BoolAlg.has_forget_to_BddDistLat BoolAlgCat.hasForgetToBddDistLatCat

section

attribute [local instance] BoundedLatticeHomClass.toBiheytingHomClass

@[simps]
instance hasForgetToHeytAlgCat : HasForget₂ BoolAlgCat HeytAlgCat where
  forget₂ :=
    { obj := fun X => {α := X}
      -- Porting note: was `fun {X Y} f => show BoundedLatticeHom X Y from f`
      -- which already looks like a hack, but I don't understand why this hack works now and
      -- the old one didn't
      map := fun {X Y} (f : BoundedLatticeHom X Y) => show HeytingHom X Y from f }
#align BoolAlg.has_forget_to_HeytAlg BoolAlgCat.hasForgetToHeytAlgCat

end

/-- Constructs an equivalence between Boolean algebras from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : BoolAlgCat.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : BoundedLatticeHom α β)
  inv := (e.symm : BoundedLatticeHom β α)
  hom_inv_id := by ext; exact e.symm_apply_apply _
                   -- ⊢ ↑((let src := { toSupHom := { toFun := ↑e, map_sup' := (_ : ∀ (a b : ↑α), ↑e …
                        -- 🎉 no goals
  inv_hom_id := by ext; exact e.apply_symm_apply _
                   -- ⊢ ↑((let src := { toSupHom := { toFun := ↑(OrderIso.symm e), map_sup' := (_ :  …
                        -- 🎉 no goals
#align BoolAlg.iso.mk BoolAlgCat.Iso.mk

/-- `OrderDual` as a functor. -/
@[simps]
def dual : BoolAlgCat ⥤ BoolAlgCat where
  obj X := of Xᵒᵈ
  map {X Y} := BoundedLatticeHom.dual
#align BoolAlg.dual BoolAlgCat.dual

/-- The equivalence between `BoolAlgCat` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
def dualEquiv : BoolAlgCat ≌ BoolAlgCat where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
#align BoolAlg.dual_equiv BoolAlgCat.dualEquiv

end BoolAlgCat

theorem boolAlgCat_dual_comp_forget_to_bddDistLatCat :
    BoolAlgCat.dual ⋙ forget₂ BoolAlgCat BddDistLatCat =
    forget₂ BoolAlgCat BddDistLatCat ⋙ BddDistLatCat.dual :=
  rfl
#align BoolAlg_dual_comp_forget_to_BddDistLat boolAlgCat_dual_comp_forget_to_bddDistLatCat
