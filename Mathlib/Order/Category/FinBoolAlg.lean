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


universe u

open CategoryTheory OrderDual Opposite

/-- The category of finite boolean algebras with bounded lattice morphisms. -/
structure FinBoolAlg where
  toBoolAlg : BoolAlg
  [isFintype : Fintype toBoolAlg]

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

/-- Construct a bundled `FinBoolAlg` from `BooleanAlgebra` + `Fintype`. -/
def of (α : Type*) [BooleanAlgebra α] [Fintype α] : FinBoolAlg :=
  ⟨{α := α}⟩

@[simp]
theorem coe_of (α : Type*) [BooleanAlgebra α] [Fintype α] : ↥(of α) = α :=
  rfl

instance : Inhabited FinBoolAlg :=
  ⟨of PUnit⟩

instance largeCategory : LargeCategory FinBoolAlg :=
  InducedCategory.category FinBoolAlg.toBoolAlg

instance concreteCategory : ConcreteCategory FinBoolAlg :=
  InducedCategory.concreteCategory FinBoolAlg.toBoolAlg

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

instance hasForgetToFinBddDistLat : HasForget₂ FinBoolAlg FinBddDistLat where
  forget₂.obj X := FinBddDistLat.of X
  forget₂.map f := f
  forget_comp := rfl

instance forgetToBoolAlg_full : (forget₂ FinBoolAlg BoolAlg).Full :=
  InducedCategory.full _

instance forgetToBoolAlgFaithful : (forget₂ FinBoolAlg BoolAlg).Faithful :=
  InducedCategory.faithful _

@[simps]
instance hasForgetToFinPartOrd : HasForget₂ FinBoolAlg FinPartOrd where
  forget₂.obj X := FinPartOrd.of X
  forget₂.map {X Y} f := show OrderHom X Y from ↑(show BoundedLatticeHom X Y from f)

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

/-- Constructs an equivalence between finite Boolean algebras from an order isomorphism between
them. -/
@[simps]
def Iso.mk {α β : FinBoolAlg.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : BoundedLatticeHom α β)
  inv := (e.symm : BoundedLatticeHom β α)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

/-- `OrderDual` as a functor. -/
@[simps]
def dual : FinBoolAlg ⥤ FinBoolAlg where
  obj X := of Xᵒᵈ
  map {X Y} := BoundedLatticeHom.dual

/-- The equivalence between `FinBoolAlg` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
def dualEquiv : FinBoolAlg ≌ FinBoolAlg where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X

end FinBoolAlg

theorem finBoolAlg_dual_comp_forget_to_finBddDistLat :
    FinBoolAlg.dual ⋙ forget₂ FinBoolAlg FinBddDistLat =
      forget₂ FinBoolAlg FinBddDistLat ⋙ FinBddDistLat.dual :=
  rfl

/-- The powerset functor. `Set` as a functor. -/
@[simps]
def fintypeToFinBoolAlgOp : FintypeCat ⥤ FinBoolAlgᵒᵖ where
  obj X := op <| FinBoolAlg.of (Set X)
  map {X Y} f :=
    Quiver.Hom.op <| (CompleteLatticeHom.setPreimage f : BoundedLatticeHom (Set Y) (Set X))
