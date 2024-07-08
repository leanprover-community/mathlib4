/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Category.BoolAlg
import Mathlib.Order.Category.FinBddDistLat
import Mathlib.Order.Hom.CompleteLattice
import Mathlib.Tactic.ApplyFun
import Mathlib.Data.Set.Subsingleton

#align_import order.category.FinBoolAlg from "leanprover-community/mathlib"@"937b1c59c58710ef8ed91f8727ef402d49d621a2"

/-!
# The category of finite boolean algebras

This file defines `FinBoolAlg`, the category of finite boolean algebras.

## TODO

Birkhoff's representation for finite Boolean algebras.

```
FintypeCat_to_FinBoolAlg_op.left_op ⋙ FinBoolAlg.dual ≅
FintypeCat_to_FinBoolAlg_op.left_op
```

`FinBoolAlg` is essentially small.
-/

set_option linter.uppercaseLean3 false

universe u

open CategoryTheory OrderDual Opposite

/-- The category of finite boolean algebras with bounded lattice morphisms. -/
structure FinBoolAlg where
  toBoolAlg : BoolAlg
  [isFintype : Fintype toBoolAlg]
#align FinBoolAlg FinBoolAlg

namespace FinBoolAlg

instance : CoeSort FinBoolAlg Type* :=
  ⟨fun X => X.toBoolAlg⟩

instance (X : FinBoolAlg) : BooleanAlgebra X :=
  X.toBoolAlg.str

attribute [instance] FinBoolAlg.isFintype

-- Porting note: linter says this is a syntactic tautology now
-- @[simp]
-- theorem coe_toBoolAlg (X : FinBoolAlg) : ↥X.toBoolAlg = ↥X :=
--   rfl
-- #align FinBoolAlg.coe_to_BoolAlg FinBoolAlg.coe_toBoolAlg
#noalign FinBoolAlg.coe_to_BoolAlg

/-- Construct a bundled `FinBoolAlg` from `BooleanAlgebra` + `Fintype`. -/
def of (α : Type*) [BooleanAlgebra α] [Fintype α] : FinBoolAlg :=
  ⟨{α := α}⟩
#align FinBoolAlg.of FinBoolAlg.of

@[simp]
theorem coe_of (α : Type*) [BooleanAlgebra α] [Fintype α] : ↥(of α) = α :=
  rfl
#align FinBoolAlg.coe_of FinBoolAlg.coe_of

instance : Inhabited FinBoolAlg :=
  ⟨of PUnit⟩

instance largeCategory : LargeCategory FinBoolAlg :=
  InducedCategory.category FinBoolAlg.toBoolAlg
#align FinBoolAlg.large_category FinBoolAlg.largeCategory

instance concreteCategory : ConcreteCategory FinBoolAlg :=
  InducedCategory.concreteCategory FinBoolAlg.toBoolAlg
#align FinBoolAlg.concrete_category FinBoolAlg.concreteCategory

instance instFunLike {X Y : FinBoolAlg} : FunLike (X ⟶ Y) X Y :=
  BoundedLatticeHom.instFunLike

-- Porting note: added
-- TODO: in all of the earlier bundled order categories,
-- we should be constructing instances analogous to this,
-- rather than directly coercions to functions.
instance instBoundedLatticeHomClass {X Y : FinBoolAlg} : BoundedLatticeHomClass (X ⟶ Y) X Y :=
  BoundedLatticeHom.instBoundedLatticeHomClass

instance hasForgetToBoolAlg : HasForget₂ FinBoolAlg BoolAlg :=
  InducedCategory.hasForget₂ FinBoolAlg.toBoolAlg
#align FinBoolAlg.has_forget_to_BoolAlg FinBoolAlg.hasForgetToBoolAlg

instance hasForgetToFinBddDistLat : HasForget₂ FinBoolAlg FinBddDistLat where
  forget₂.obj X := FinBddDistLat.of X
  forget₂.map f := f
  forget_comp := rfl
#align FinBoolAlg.has_forget_to_FinBddDistLat FinBoolAlg.hasForgetToFinBddDistLat

instance forgetToBoolAlg_full : (forget₂ FinBoolAlg BoolAlg).Full :=
  InducedCategory.full _
#align FinBoolAlg.forget_to_BoolAlg_full FinBoolAlg.forgetToBoolAlg_full

instance forgetToBoolAlgFaithful : (forget₂ FinBoolAlg BoolAlg).Faithful :=
  InducedCategory.faithful _
#align FinBoolAlg.forget_to_BoolAlg_faithful FinBoolAlg.forgetToBoolAlgFaithful

@[simps]
instance hasForgetToFinPartOrd : HasForget₂ FinBoolAlg FinPartOrd where
  forget₂.obj X := FinPartOrd.of X
  forget₂.map {X Y} f := show OrderHom X Y from ↑(show BoundedLatticeHom X Y from f)
#align FinBoolAlg.has_forget_to_FinPartOrd FinBoolAlg.hasForgetToFinPartOrd

instance forgetToFinPartOrdFaithful : (forget₂ FinBoolAlg FinPartOrd).Faithful :=
  -- Porting note: original code
  -- ⟨fun {X Y} f g h =>
  --   haveI := congr_arg (coeFn : _ → X → Y) h
  --   DFunLike.coe_injective this⟩
  -- Porting note: the coercions to functions for the various bundled order categories
  -- are quite inconsistent. We need to go back through and make all these files uniform.
  ⟨fun {X Y} f g h => by
    dsimp at *
    apply DFunLike.coe_injective
    dsimp
    ext x
    apply_fun (fun f => f x) at h
    exact h ⟩
#align FinBoolAlg.forget_to_FinPartOrd_faithful FinBoolAlg.forgetToFinPartOrdFaithful

/-- Constructs an equivalence between finite Boolean algebras from an order isomorphism between
them. -/
@[simps]
def Iso.mk {α β : FinBoolAlg.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : BoundedLatticeHom α β)
  inv := (e.symm : BoundedLatticeHom β α)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _
#align FinBoolAlg.iso.mk FinBoolAlg.Iso.mk

/-- `OrderDual` as a functor. -/
@[simps]
def dual : FinBoolAlg ⥤ FinBoolAlg where
  obj X := of Xᵒᵈ
  map {X Y} := BoundedLatticeHom.dual
#align FinBoolAlg.dual FinBoolAlg.dual

/-- The equivalence between `FinBoolAlg` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
def dualEquiv : FinBoolAlg ≌ FinBoolAlg where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
#align FinBoolAlg.dual_equiv FinBoolAlg.dualEquiv

end FinBoolAlg

theorem finBoolAlg_dual_comp_forget_to_finBddDistLat :
    FinBoolAlg.dual ⋙ forget₂ FinBoolAlg FinBddDistLat =
      forget₂ FinBoolAlg FinBddDistLat ⋙ FinBddDistLat.dual :=
  rfl
#align FinBoolAlg_dual_comp_forget_to_FinBddDistLat finBoolAlg_dual_comp_forget_to_finBddDistLat

/-- The powerset functor. `Set` as a functor. -/
@[simps]
def fintypeToFinBoolAlgOp : FintypeCat ⥤ FinBoolAlgᵒᵖ where
  obj X := op <| FinBoolAlg.of (Set X)
  map {X Y} f :=
    Quiver.Hom.op <| (CompleteLatticeHom.setPreimage f : BoundedLatticeHom (Set Y) (Set X))
#align Fintype_to_FinBoolAlg_op fintypeToFinBoolAlgOp
