/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.Tactic.Basic
import Mathlib.Data.Subtype
import Mathlib.Logic.Equiv.Basic
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Sigma.Basic

/-!
# Fibers of a functor

This files define the type `Fiber` of a functor at a given object in the base category.

We provide the category instance on the fibers of a functor.
We show that for a functor `P`, the fiber of the opposite functor
`P.op` are isomorphic to the opposites of the fiber categories of `P`.

## Notation

We provide the following notations:
* `P ⁻¹ I` for the fiber of functor `P` at `I`.
-/

namespace CategoryTheory

open Category Opposite Functor

/-- The fiber of a functor at a given object in the codomain category. -/
def Fiber {C E : Type*} [Category C] [Category E] (P : E ⥤ C) (I : C) :=
  {X : E // P.obj X = I}

/-- The essential fiber of a functor at a given object in the codomain category. -/
structure EFiber {C E : Type*} [Category C] [Category E] (P : E ⥤ C) (I : C) where
  obj : E
  iso : P.obj obj ≅ I

/-- The lax fiber of a functor at a given object in the codomain category. -/
structure LaxFiber {C E : Type*} [Category C] [Category E] (P : E ⥤ C) (I : C) where
  obj : E
  from_base : I ⟶ P.obj obj

notation:75 (name := Fiber_stx) P " ⁻¹ " I => Fiber P I

notation:75 (name := EFiber_stx) P " ⁻¹ᵉ " I => EFiber P I

notation:75 (name := LaxFiber_stx) P " ⁻¹ˡ " I => LaxFiber P I

namespace Fiber

variable {C E : Type*} [Category C] [Category E] {P : E ⥤ C}

@[ext]
lemma ext  {I : C} (X Y : P⁻¹ I) (h : X.1 = Y.1) : X = Y := by
  cases X
  cases Y
  simp at h
  subst h
  rfl

/-- Coercion from the fiber to the domain. -/
instance {I : C} : CoeOut (P⁻¹ I) E where
coe := fun x => x.1

variable {I : C}

lemma coe_mk {X : E} (h : P.obj X = I) : ((⟨X, h⟩ : P⁻¹ I) : E) = X := rfl

lemma mk_coe {X : P⁻¹ I} : ⟨X.1, X.2⟩  = X := rfl

lemma coe_inj (X Y : P⁻¹ I) : (X : E) = Y ↔ X = Y := Subtype.coe_inj

lemma over (X : P⁻¹ I) : P.obj X = I := X.2

lemma over_eq (X Y : P⁻¹ I) : P.obj X = P.obj Y := by
  simp [over]

/-- A tautological construction of an element in the fiber of the image of a domain element. -/
@[simp]
def tauto (X : E) : P⁻¹ (P.obj X) := ⟨X, rfl⟩

/-- Regarding an element of the domain as an element in the Fiber of its image. -/
instance instTautoFib (X : E) : CoeDep (E) (X) (P ⁻¹ (P.obj X) ) where
  coe := tauto X

lemma tauto_over (X : E) : (tauto X : P⁻¹ (P.obj X)).1 = X := rfl

/-- The total space of a map. -/
@[ext]
structure Total where
  /-- The base object in `C` -/
  base : C
  /-- The object in the fiber of the base object. -/
  fiber : P⁻¹ base

/-- The category structure on the fibers of a functor. -/
instance category {I : C} : Category (P ⁻¹ I) where
  Hom X Y := {g : (X : E) ⟶ (Y : E) // P.map g = eqToHom (over_eq X Y)}
  id X := ⟨𝟙 (X : E), by simp only [Functor.map_id, eqToHom_refl]⟩
  comp g h := ⟨g.1 ≫ h.1, by rw [Functor.map_comp, g.2, h.2, eqToHom_trans]⟩

lemma id_coe {I : C} (X : P⁻¹ I) : (𝟙 X : X ⟶ X).val = 𝟙 (X : E) := rfl

lemma comp_coe {c : C} {X Y Z : P⁻¹ c} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).1 = f.1 ≫ g.1 := rfl

@[simp, aesop forward safe]
lemma fiber_hom_over {I : C} (X Y : P⁻¹ I) (g : X ⟶ Y) : P.map g.1 = eqToHom (Fiber.over_eq X Y) := g.2

/-- The forgetful functor from a fiber to the domain category. -/
@[simps]
def forget {I : C} : (P⁻¹ I) ⥤ E where
  obj := fun x => x
  map := @fun x y f => f.1

lemma fiber_comp_obj {c: C} (X Y Z : P⁻¹ c) (f: X ⟶ Y) (g: Y ⟶ Z) :
(f ≫ g).1 = f.1 ≫ g.1 := rfl

@[simp]
lemma fiber_comp_obj_eq {c: C} {X Y Z : P⁻¹ c}
    {f: X ⟶ Y} {g: Y ⟶ Z} {h : X ⟶ Z} :
    (f ≫ g = h) ↔  f.1 ≫ g.1  = h.1 := by
  constructor
  · intro H
    cases H
    rfl
  · intro H
    cases f
    cases g
    cases h
    simp at H
    subst H
    rfl

@[simp]
lemma fiber_id_obj {I : C} (X : P⁻¹ I) : (𝟙 X : X ⟶ X).val = 𝟙 (X : E) := rfl

/- Two morphisms in a fiber P⁻¹ c are equal if their underlying morphisms in E are equal. -/
lemma hom_ext {I : C} {X Y : P⁻¹ I} {f g : X ⟶ Y} (h : f.1 = g.1) : f = g := by
  cases f
  cases g
  simp at h
  subst h
  rfl

@[simps]
lemma is_iso {I : C} {X Y : P⁻¹ I} (f : X ⟶ Y) : IsIso f ↔ IsIso f.1 :=
  ⟨fun h ↦ (asIso f) |> forget.mapIso |> Iso.isIso_hom, fun h ↦ ⟨⟨⟨inv f.1, by simp⟩, by simp⟩⟩⟩

end Fiber
namespace EFiber

variable {C E : Type*} [Category C] [Category E] {P : E ⥤ C}

/-- Coercion from the fiber to the domain. -/
instance {I : C} : CoeOut (P⁻¹ᵉ I) E where
coe := fun X => X.1

/-- A tautological construction of an element in the fiber of the image of a domain element. -/
@[simps!]
def tauto (X : E) : EFiber P (P.obj X) := ⟨X , Iso.refl _⟩

/-- Regarding an element of the domain as an element in the essential fiber of its image. -/
instance instTautoFib (X : E) : CoeDep (E) (X) (EFiber P (P.obj X) ) where
  coe := tauto X

/-- The category structure on the essential fibers of a functor. -/
instance category {I : C} : Category (P⁻¹ᵉ I) where
  Hom X Y := {g : (X : E) ⟶ (Y : E) // P.map g = X.iso.hom ≫ Y.iso.inv}
  id X := ⟨𝟙 (X : E), by simp only [map_id, Iso.hom_inv_id]⟩
  comp {X Y Z} g h := ⟨g.1 ≫ h.1, by
    simp [Functor.map_comp]
    calc
      P.map g.1 ≫ P.map h.1 = X.iso.hom ≫ Y.iso.inv ≫ Y.iso.hom ≫ Z.iso.inv := by
        rw [g.2, h.2] -- simp only not working here?
        simp
      _ = X.iso.hom ≫ Z.iso.inv := by simp⟩

end EFiber

namespace Fiber.Op

open Fiber

variable {C E : Type*} [Category C] [Category E] {P : E ⥤ C}

@[simp]
lemma obj_over {I : C} (X : P.op ⁻¹ (op I)) : P.obj (unop (X.1)) = I := by
  cases' X with e h
  simpa [Functor.op] using h

/-- The Fibers of the opposite functor `P.op` are in bijection with the the Fibers of `P`.  -/
@[simps]
def equiv (I : C) : (P.op ⁻¹ (op I)) ≃ (P⁻¹ I) where
  toFun := fun X =>  (⟨unop X.1, by rw [obj_over] ⟩)
  invFun := fun X => ⟨op X.1 , by simp only [Functor.op_obj, unop_op, Fiber.over]⟩
  left_inv := fun X ↦ rfl
  right_inv := fun X ↦ rfl

/-- The Fibers of the opposite functor `P.op` are isomorphic to the the Fibers of `P`.  -/
@[simps]
def iso (I : C) : (P.op ⁻¹ (op I)) ≅ (P⁻¹ I) where
  hom := fun X =>  (⟨unop X.1, by rw [obj_over] ⟩)
  inv := fun X => ⟨op X.1 , by simp only [Functor.op_obj, unop_op, Fiber.over]⟩

lemma unop_op_map  {I : C} {X Y : (P.op) ⁻¹ (op I)} (f : X ⟶ Y) :
    unop (P.op.map f.1) = P.map f.1.unop  := rfl

lemma op_map_unop  {I : C} {X Y : (P ⁻¹ I)ᵒᵖ} (f : X ⟶ Y) :
    P.op.map (f.unop.1.op) = (P.map (f.unop.1)).op := rfl

/-- The fiber categories of the opposite functor `P.op` are isomorphic
to the opposites of the fiber categories of `P`. -/
def Iso (P : E ⥤ C) (I : C) : Cat.of (P.op ⁻¹ (op I) ) ≅ Cat.of ((P⁻¹ I)ᵒᵖ)  where
  hom := {
    obj := fun X => op (⟨unop X.1, by rw [obj_over] ⟩)
    map := @fun X Y f => ⟨f.1.unop, by dsimp; rw [← (unop_op_map f), f.2]; apply eqToHom_unop ⟩
  }
  inv := {
    obj := fun X => ⟨op X.unop.1 , by simp only [Functor.op_obj, unop_op, Fiber.over]⟩
    map := @fun X Y f => ⟨(f.unop.1).op , by dsimp;  simp [Functor.op_map]⟩
  }
  hom_inv_id := rfl
  inv_hom_id := rfl

end Fiber.Op

end CategoryTheory
