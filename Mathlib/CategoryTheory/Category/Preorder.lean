/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison, Johannes Hölzl, Reid Barton
-/
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.EqToHom
import Mathlib.Order.Hom.Basic
import Mathlib.Data.ULift

#align_import category_theory.category.preorder from "leanprover-community/mathlib"@"dc6c365e751e34d100e80fe6e314c3c3e0fd2988"

/-!

# Preorders as categories

We install a category instance on any preorder. This is not to be confused with the category _of_
preorders, defined in `Order.Category.Preorder`.

We show that monotone functions between preorders correspond to functors of the associated
categories.

## Main definitions

* `homOfLE` and `leOfHom` provide translations between inequalities in the preorder, and
  morphisms in the associated category.
* `Monotone.functor` is the functor associated to a monotone function.

-/


universe u v

namespace Preorder

open CategoryTheory

-- see Note [lower instance priority]
/--
The category structure coming from a preorder. There is a morphism `X ⟶ Y` if and only if `X ≤ Y`.

Because we don't allow morphisms to live in `Prop`,
we have to define `X ⟶ Y` as `ULift (PLift (X ≤ Y))`.
See `CategoryTheory.homOfLE` and `CategoryTheory.leOfHom`.

See <https://stacks.math.columbia.edu/tag/00D3>.
-/
instance (priority := 100) smallCategory (α : Type u) [Preorder α] : SmallCategory α where
  Hom U V := ULift (PLift (U ≤ V))
  id X := ⟨⟨le_refl X⟩⟩
  comp f g := ⟨⟨le_trans _ _ _ f.down.down g.down.down⟩⟩
#align preorder.small_category Preorder.smallCategory

-- Porting note: added to ease the port of `CategoryTheory.Subobject.Basic`
instance subsingleton_hom {α : Type u} [Preorder α] (U V : α) :
  Subsingleton (U ⟶ V) := ⟨fun _ _ => ULift.ext _ _ (Subsingleton.elim _ _ )⟩

end Preorder

namespace CategoryTheory

open Opposite

variable {X : Type u} [Preorder X]

/-- Express an inequality as a morphism in the corresponding preorder category.
-/
def homOfLE {x y : X} (h : x ≤ y) : x ⟶ y :=
  ULift.up (PLift.up h)
#align category_theory.hom_of_le CategoryTheory.homOfLE

@[inherit_doc homOfLE]
abbrev _root_.LE.le.hom := @homOfLE
#align has_le.le.hom LE.le.hom

@[simp]
theorem homOfLE_refl {x : X} (h : x ≤ x) : h.hom = 𝟙 x :=
  rfl
#align category_theory.hom_of_le_refl CategoryTheory.homOfLE_refl

@[simp]
theorem homOfLE_comp {x y z : X} (h : x ≤ y) (k : y ≤ z) :
    homOfLE h ≫ homOfLE k = homOfLE (h.trans k) :=
  rfl
#align category_theory.hom_of_le_comp CategoryTheory.homOfLE_comp

/-- Extract the underlying inequality from a morphism in a preorder category.
-/
theorem leOfHom {x y : X} (h : x ⟶ y) : x ≤ y :=
  h.down.down
#align category_theory.le_of_hom CategoryTheory.leOfHom

@[nolint defLemma, inherit_doc leOfHom]
abbrev _root_.Quiver.Hom.le := @leOfHom
#align quiver.hom.le Quiver.Hom.le

-- Porting note: why does this lemma exist? With proof irrelevance, we don't need to simplify proofs
-- @[simp]
theorem leOfHom_homOfLE {x y : X} (h : x ≤ y) : h.hom.le = h :=
  rfl
#align category_theory.le_of_hom_hom_of_le CategoryTheory.leOfHom_homOfLE

-- Porting note: linter gives: "Left-hand side does not simplify, when using the simp lemma on
-- itself. This usually means that it will never apply." removing simp? It doesn't fire
-- @[simp]
theorem homOfLE_leOfHom {x y : X} (h : x ⟶ y) : h.le.hom = h :=
  rfl
#align category_theory.hom_of_le_le_of_hom CategoryTheory.homOfLE_leOfHom

/-- Construct a morphism in the opposite of a preorder category from an inequality. -/
def opHomOfLE {x y : Xᵒᵖ} (h : unop x ≤ unop y) : y ⟶ x :=
  (homOfLE h).op
#align category_theory.op_hom_of_le CategoryTheory.opHomOfLE

theorem le_of_op_hom {x y : Xᵒᵖ} (h : x ⟶ y) : unop y ≤ unop x :=
  h.unop.le
#align category_theory.le_of_op_hom CategoryTheory.le_of_op_hom

instance uniqueToTop [OrderTop X] {x : X} : Unique (x ⟶ ⊤) where
  default := homOfLE le_top
  uniq := fun a => by rfl
#align category_theory.unique_to_top CategoryTheory.uniqueToTop

instance uniqueFromBot [OrderBot X] {x : X} : Unique (⊥ ⟶ x) where
  default := homOfLE bot_le
  uniq := fun a => by rfl
#align category_theory.unique_from_bot CategoryTheory.uniqueFromBot

variable (X) in
/-- The equivalence of categories from the order dual of a preordered type `X`
to the opposite category of the preorder `X`. -/
@[simps]
def orderDualEquivalence : Xᵒᵈ ≌ Xᵒᵖ where
  functor :=
    { obj := fun x => op (OrderDual.ofDual x)
      map := fun f => (homOfLE (leOfHom f)).op }
  inverse :=
    { obj := fun x => OrderDual.toDual x.unop
      map := fun f => (homOfLE (leOfHom f.unop)) }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end CategoryTheory

section

open CategoryTheory

variable {X : Type u} {Y : Type v} [Preorder X] [Preorder Y]

/-- A monotone function between preorders induces a functor between the associated categories.
-/
def Monotone.functor {f : X → Y} (h : Monotone f) : X ⥤ Y where
  obj := f
  map g := CategoryTheory.homOfLE (h g.le)
#align monotone.functor Monotone.functor

@[simp]
theorem Monotone.functor_obj {f : X → Y} (h : Monotone f) : h.functor.obj = f :=
  rfl
#align monotone.functor_obj Monotone.functor_obj

-- Faithfulness is automatic because preorder categories are thin
instance (f : X ↪o Y) : f.monotone.functor.Full where
  map_surjective h := ⟨homOfLE (f.map_rel_iff.1 h.le), rfl⟩

/-- The equivalence of categories `X ≌ Y` induced by `e : X ≃o Y`. -/
@[simps]
def OrderIso.equivalence (e : X ≃o Y) : X ≌ Y where
  functor := e.monotone.functor
  inverse := e.symm.monotone.functor
  unitIso := NatIso.ofComponents (fun _ ↦ eqToIso (by simp))
  counitIso := NatIso.ofComponents (fun _ ↦ eqToIso (by simp))

end

namespace CategoryTheory

section Preorder

variable {X : Type u} {Y : Type v} [Preorder X] [Preorder Y]

/-- A functor between preorder categories is monotone.
-/
@[mono]
theorem Functor.monotone (f : X ⥤ Y) : Monotone f.obj := fun _ _ hxy => (f.map hxy.hom).le
#align category_theory.functor.monotone CategoryTheory.Functor.monotone

end Preorder

section PartialOrder

variable {X : Type u} {Y : Type v} [PartialOrder X] [PartialOrder Y]

theorem Iso.to_eq {x y : X} (f : x ≅ y) : x = y :=
  le_antisymm f.hom.le f.inv.le
#align category_theory.iso.to_eq CategoryTheory.Iso.to_eq

/-- A categorical equivalence between partial orders is just an order isomorphism.
-/
def Equivalence.toOrderIso (e : X ≌ Y) : X ≃o Y where
  toFun := e.functor.obj
  invFun := e.inverse.obj
  left_inv a := (e.unitIso.app a).to_eq.symm
  right_inv b := (e.counitIso.app b).to_eq
  map_rel_iff' {a a'} :=
    ⟨fun h =>
      ((Equivalence.unit e).app a ≫ e.inverse.map h.hom ≫ (Equivalence.unitInv e).app a').le,
      fun h : a ≤ a' => (e.functor.map h.hom).le⟩
#align category_theory.equivalence.to_order_iso CategoryTheory.Equivalence.toOrderIso

-- `@[simps]` on `Equivalence.toOrderIso` produces lemmas that fail the `simpNF` linter,
-- so we provide them by hand:
@[simp]
theorem Equivalence.toOrderIso_apply (e : X ≌ Y) (x : X) : e.toOrderIso x = e.functor.obj x :=
  rfl
#align category_theory.equivalence.to_order_iso_apply CategoryTheory.Equivalence.toOrderIso_apply

@[simp]
theorem Equivalence.toOrderIso_symm_apply (e : X ≌ Y) (y : Y) :
    e.toOrderIso.symm y = e.inverse.obj y :=
  rfl
#align category_theory.equivalence.to_order_iso_symm_apply CategoryTheory.Equivalence.toOrderIso_symm_apply

end PartialOrder

end CategoryTheory
