/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.category.FinBoolAlg
! leanprover-community/mathlib commit 937b1c59c58710ef8ed91f8727ef402d49d621a2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Category.BoolAlgCat
import Mathlib.Order.Category.FinBddDistLatCat
import Mathlib.Order.Hom.CompleteLattice

/-!
# The category of finite boolean algebras

This file defines `FinBoolAlgCat`, the category of finite boolean algebras.

## TODO

Birkhoff's representation for finite Boolean algebras.

`FintypeCat_to_FinBoolAlgCat_op.left_op ⋙ FinBoolAlgCat.dual ≅ FintypeCat_to_FinBoolAlgCat_op.left_op`

`FinBoolAlgCat` is essentially small.
-/

set_option linter.uppercaseLean3 false

universe u

open CategoryTheory OrderDual Opposite

/-- The category of finite boolean algebras with bounded lattice morphisms. -/
structure FinBoolAlgCat where
  toBoolAlgCat : BoolAlgCat
  [isFintype : Fintype toBoolAlgCat]
#align FinBoolAlg FinBoolAlgCat

namespace FinBoolAlgCat

instance : CoeSort FinBoolAlgCat (Type _) :=
  ⟨fun X => X.toBoolAlgCat⟩

instance (X : FinBoolAlgCat) : BooleanAlgebra X :=
  X.toBoolAlgCat.str

attribute [instance] FinBoolAlgCat.isFintype

-- Porting note: linter says this is a syntactic tautology now
-- @[simp]
-- theorem coe_toBoolAlgCat (X : FinBoolAlgCat) : ↥X.toBoolAlgCat = ↥X :=
--   rfl
-- #align FinBoolAlg.coe_to_BoolAlg FinBoolAlgCat.coe_toBoolAlgCat
#noalign FinBoolAlg.coe_to_BoolAlg

/-- Construct a bundled `FinBoolAlgCat` from `BooleanAlgebra` + `Fintype`. -/
def of (α : Type _) [BooleanAlgebra α] [Fintype α] : FinBoolAlgCat :=
  ⟨{α := α}⟩
#align FinBoolAlg.of FinBoolAlgCat.of

@[simp]
theorem coe_of (α : Type _) [BooleanAlgebra α] [Fintype α] : ↥(of α) = α :=
  rfl
#align FinBoolAlg.coe_of FinBoolAlgCat.coe_of

instance : Inhabited FinBoolAlgCat :=
  ⟨of PUnit⟩

instance largeCategory : LargeCategory FinBoolAlgCat :=
  InducedCategory.category FinBoolAlgCat.toBoolAlgCat
#align FinBoolAlg.large_category FinBoolAlgCat.largeCategory

instance concreteCategory : ConcreteCategory FinBoolAlgCat :=
  InducedCategory.concreteCategory FinBoolAlgCat.toBoolAlgCat
#align FinBoolAlg.concrete_category FinBoolAlgCat.concreteCategory

instance hasForgetToBoolAlg : HasForget₂ FinBoolAlgCat BoolAlgCat :=
  InducedCategory.hasForget₂ FinBoolAlgCat.toBoolAlgCat
#align FinBoolAlg.has_forget_to_BoolAlg FinBoolAlgCat.hasForgetToBoolAlg

instance hasForgetToFinBddDistLat : HasForget₂ FinBoolAlgCat FinBddDistLatCat where
  forget₂ :=
    { obj := fun X => FinBddDistLatCat.of X
      map := fun {X Y} f => f }
  forget_comp := rfl
#align FinBoolAlg.has_forget_to_FinBddDistLat FinBoolAlgCat.hasForgetToFinBddDistLat

instance forgetToBoolAlgFull : Full (forget₂ FinBoolAlgCat BoolAlgCat) :=
  InducedCategory.full _
#align FinBoolAlg.forget_to_BoolAlg_full FinBoolAlgCat.forgetToBoolAlgFull

instance forget_to_boolAlg_faithful : Faithful (forget₂ FinBoolAlgCat BoolAlgCat) :=
  InducedCategory.faithful _
#align FinBoolAlg.forget_to_BoolAlg_faithful FinBoolAlgCat.forget_to_boolAlg_faithful

@[simps]
instance hasForgetToFinPartOrd : HasForget₂ FinBoolAlgCat FinPartOrd
    where forget₂ :=
    { obj := fun X => FinPartOrd.of X
      map := fun {X Y} f => show OrderHom X Y from ↑(show BoundedLatticeHom X Y from f) }
#align FinBoolAlg.has_forget_to_FinPartOrd FinBoolAlgCat.hasForgetToFinPartOrd

instance forget_to_finPartOrd_faithful : Faithful (forget₂ FinBoolAlgCat FinPartOrd) :=
  ⟨sorry⟩
  -- ⟨fun {X Y} f g h =>
  --   haveI := congr_arg (coeFn : _ → X → Y) h
  --   FunLike.coe_injective this⟩
#align FinBoolAlg.forget_to_FinPartOrd_faithful FinBoolAlgCat.forget_to_finPartOrd_faithful

/-- Constructs an equivalence between finite Boolean algebras from an order isomorphism between
them. -/
@[simps]
def Iso.mk {α β : FinBoolAlgCat.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : BoundedLatticeHom α β)
  inv := (e.symm : BoundedLatticeHom β α)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _
#align FinBoolAlg.iso.mk FinBoolAlgCat.Iso.mk

/-- `order_dual` as a functor. -/
@[simps]
def dual : FinBoolAlgCat ⥤ FinBoolAlgCat where
  obj X := of Xᵒᵈ
  map {X Y} := BoundedLatticeHom.dual
#align FinBoolAlg.dual FinBoolAlgCat.dual

/-- The equivalence between `FinBoolAlgCat` and itself induced by `order_dual` both ways. -/
@[simps functor inverse]
def dualEquiv : FinBoolAlgCat ≌ FinBoolAlgCat where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
#align FinBoolAlg.dual_equiv FinBoolAlgCat.dualEquiv

end FinBoolAlgCat

theorem finBoolAlgCat_dual_comp_forget_to_finBddDistLatCat :
    FinBoolAlgCat.dual ⋙ forget₂ FinBoolAlgCat FinBddDistLatCat =
      forget₂ FinBoolAlgCat FinBddDistLatCat ⋙ FinBddDistLatCat.dual :=
  rfl
#align FinBoolAlg_dual_comp_forget_to_FinBddDistLat finBoolAlgCat_dual_comp_forget_to_finBddDistLatCat

/-- The powerset functor. `set` as a functor. -/
@[simps]
def fintypeToFinBoolAlgCatOp : FintypeCat ⥤ FinBoolAlgCatᵒᵖ where
  obj X := op <| FinBoolAlgCat.of (Set X)
  map {X Y} f :=
    Quiver.Hom.op <| (CompleteLatticeHom.setPreimage f : BoundedLatticeHom (Set Y) (Set X))
#align Fintype_to_FinBoolAlg_op fintypeToFinBoolAlgCatOp
