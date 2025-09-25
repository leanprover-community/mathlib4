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
# The category of finite Boolean algebras

This file defines `FinBoolAlg`, the category of finite Boolean algebras.

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

/-- The category of finite Boolean algebras with bounded lattice morphisms. -/
structure FinBoolAlg extends BoolAlg where
  [isFintype : Fintype toBoolAlg]

attribute [instance] FinBoolAlg.isFintype

namespace FinBoolAlg

instance : CoeSort FinBoolAlg Type* :=
  ⟨fun X => X.carrier⟩

/-- Construct a bundled `FinBoolAlg` from `BooleanAlgebra` + `Fintype`. -/
abbrev of (α : Type*) [BooleanAlgebra α] [Fintype α] : FinBoolAlg where
  carrier := α

theorem coe_of (α : Type*) [BooleanAlgebra α] [Fintype α] : ↥(of α) = α :=
  rfl

instance : Inhabited FinBoolAlg :=
  ⟨of PUnit⟩

instance largeCategory : LargeCategory FinBoolAlg :=
  InducedCategory.category FinBoolAlg.toBoolAlg

instance concreteCategory : ConcreteCategory FinBoolAlg (BoundedLatticeHom · ·) :=
  InducedCategory.concreteCategory FinBoolAlg.toBoolAlg

instance hasForgetToBoolAlg : HasForget₂ FinBoolAlg BoolAlg :=
  InducedCategory.hasForget₂ FinBoolAlg.toBoolAlg

instance hasForgetToFinBddDistLat : HasForget₂ FinBoolAlg FinBddDistLat where
  forget₂.obj X := .of X
  forget₂.map f := FinBddDistLat.ofHom f.hom

instance forgetToBoolAlg_full : (forget₂ FinBoolAlg BoolAlg).Full :=
  InducedCategory.full _

instance forgetToBoolAlgFaithful : (forget₂ FinBoolAlg BoolAlg).Faithful :=
  InducedCategory.faithful _

@[simps]
instance hasForgetToFinPartOrd : HasForget₂ FinBoolAlg FinPartOrd where
  forget₂.obj X := .of X
  forget₂.map {X Y} f := PartOrd.ofHom f.hom

instance forgetToFinPartOrdFaithful : (forget₂ FinBoolAlg FinPartOrd).Faithful where
  map_injective h := by
    ext x
    exact CategoryTheory.congr_fun h x

/-- Constructs an equivalence between finite Boolean algebras from an order isomorphism between
them. -/
@[simps]
def Iso.mk {α β : FinBoolAlg.{u}} (e : α ≃o β) : α ≅ β where
  hom := BoolAlg.ofHom e
  inv := BoolAlg.ofHom e.symm
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

/-- `OrderDual` as a functor. -/
@[simps map]
def dual : FinBoolAlg ⥤ FinBoolAlg where
  obj X := of Xᵒᵈ
  map f := BoolAlg.ofHom f.hom.dual

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
  obj X := op <| .of (Set X)
  map {X Y} f :=
    Quiver.Hom.op <| BoolAlg.ofHom <| CompleteLatticeHom.setPreimage f
