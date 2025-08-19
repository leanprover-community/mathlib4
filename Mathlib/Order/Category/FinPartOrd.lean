/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.Order.Category.PartOrd

/-!
# The category of finite partial orders

This defines `FinPartOrd`, the category of finite partial orders.

Note: `FinPartOrd` is *not* a subcategory of `BddOrd` because finite orders are not necessarily
bounded.

## TODO

`FinPartOrd` is equivalent to a small category.
-/


universe u v

open CategoryTheory


/-- The category of finite partial orders with monotone functions. -/
structure FinPartOrd extends PartOrd where
  [isFintype : Fintype toPartOrd]

namespace FinPartOrd

instance : CoeSort FinPartOrd Type* :=
  ⟨fun X ↦ X.toPartOrd⟩

instance (X : FinPartOrd) : PartialOrder X :=
  X.toPartOrd.str

attribute [instance] FinPartOrd.isFintype

/-- Construct a bundled `FinPartOrd` from `PartialOrder` + `Fintype`. -/
abbrev of (α : Type*) [PartialOrder α] [Fintype α] : FinPartOrd where
  carrier := α

instance : Inhabited FinPartOrd :=
  ⟨of PUnit⟩

instance largeCategory : LargeCategory FinPartOrd :=
  InducedCategory.category FinPartOrd.toPartOrd

instance concreteCategory : ConcreteCategory FinPartOrd (· →o ·) :=
  InducedCategory.concreteCategory FinPartOrd.toPartOrd

instance hasForgetToPartOrd : HasForget₂ FinPartOrd PartOrd :=
  InducedCategory.hasForget₂ FinPartOrd.toPartOrd

instance hasForgetToFintype : HasForget₂ FinPartOrd FintypeCat where
  forget₂.obj X := .of X
  forget₂.map f := f.hom

/-- Typecheck a `OrderHom` as a morphism in `FinPartOrd`. -/
abbrev ofHom {X Y : Type u} [PartialOrder X] [Fintype X] [PartialOrder Y] [Fintype Y] (f : X →o Y) :
    of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := FinPartOrd) f

@[simp]
lemma hom_id {X : FinPartOrd} : (𝟙 X : X ⟶ X).hom = OrderHom.id := rfl

/- Provided for rewriting. -/
lemma id_apply (X : FinPartOrd) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
lemma hom_comp {X Y Z : FinPartOrd} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
lemma comp_apply {X Y Z : FinPartOrd} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
lemma hom_ext {X Y : FinPartOrd} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  ConcreteCategory.ext hf

@[simp]
lemma hom_ofHom {X Y : Type u} [PartialOrder X] [Fintype X] [PartialOrder Y] [Fintype Y]
    (f : X →o Y) : (ofHom f).hom = f :=
  rfl

@[simp]
lemma ofHom_hom {X Y : FinPartOrd} (f : X ⟶ Y) :
    ofHom f.hom = f := rfl

/-- Constructs an isomorphism of finite partial orders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : FinPartOrd.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm

/-- `OrderDual` as a functor. -/
@[simps map]
def dual : FinPartOrd ⥤ FinPartOrd where
  obj X := of Xᵒᵈ
  map f := ofHom f.hom.dual

/-- The equivalence between `FinPartOrd` and itself induced by `OrderDual` both ways. -/
@[simps]
def dualEquiv : FinPartOrd ≌ FinPartOrd where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X ↦ Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X ↦ Iso.mk <| OrderIso.dualDual X

end FinPartOrd

theorem FinPartOrd_dual_comp_forget_to_partOrd :
    FinPartOrd.dual ⋙ forget₂ FinPartOrd PartOrd =
      forget₂ FinPartOrd PartOrd ⋙ PartOrd.dual := rfl
