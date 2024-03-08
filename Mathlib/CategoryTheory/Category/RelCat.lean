/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Types
import Mathlib.Data.Rel

#align_import category_theory.category.Rel from "leanprover-community/mathlib"@"afad8e438d03f9d89da2914aa06cb4964ba87a18"

/-!
The category of types with binary relations as morphisms.
-/


namespace CategoryTheory

universe u

-- This file is about Lean 3 declaration "Rel".
set_option linter.uppercaseLean3 false

/-- A type synonym for `Type`, which carries the category instance for which
    morphisms are binary relations. -/
def RelCat :=
  Type u
#align category_theory.Rel CategoryTheory.RelCat

instance RelCat.inhabited : Inhabited RelCat := by unfold RelCat; infer_instance
#align category_theory.Rel.inhabited CategoryTheory.RelCat.inhabited

/-- The category of types with binary relations as morphisms. -/
instance rel : LargeCategory RelCat where
  Hom X Y := X → Y → Prop
  id X x y := x = y
  comp f g x z := ∃ y, f x y ∧ g y z
#align category_theory.rel CategoryTheory.rel

theorem rel_hom {X Y : RelCat} : (X ⟶ Y) = Rel X Y := rfl

@[ext] theorem rel_ext {X Y : RelCat} (f g : X ⟶ Y) (h : ∀ a b, f a b ↔ g a b) : f = g :=
  funext₂ (fun a b => propext (h a b))

theorem rel_id (X : RelCat) : 𝟙 X = (· = ·) := rfl

theorem rel_comp {X Y Z : RelCat} (f : X ⟶ Y) (g : Y ⟶ Z) : f ≫ g = Rel.comp f g := by
  ext _ _
  rfl

@[simp] theorem rel_id_apply₂ (X : RelCat) (x y : X) : (𝟙 X) x y ↔ x = y := by
  rw[rel_id]

@[simp] theorem rel_comp_apply₂ {X Y Z : RelCat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) (z : Z) :
    (f ≫ g) x z ↔ ∃ y, f x y ∧ g y z := by rfl

/-- The essentially surjective faithful embedding
    from the category of sets into the category of sets and relations. -/
def typeRelFunctor : Type u ⥤ RelCat.{u} where
  obj X := X
  map f := f.graph

@[simp] theorem typeRelFunctor_map {X Y : Type u} (f : X ⟶ Y) (x : X) (y : Y) :
    typeRelFunctor.map f x y ↔ f x = y := f.graph_def x y

instance typeRelFunctor_faithful : Faithful typeRelFunctor where
  map_injective h := Function.graph_inj _ _ h

/- theorem hom_inv {X Y : RelCat} (f : X ≅ Y) : f.inv = Rel.inv f.hom := by
  have eq := f.inv_hom_id_assoc (Rel.inv f.hom)
  suffices eq2 : f.hom ≫ Rel.inv f.hom = 𝟙 X by
    rw[eq2] at eq
    aesop_cat
  ext x y
  simp only [rel_comp_apply₂, rel_id_apply₂]
  constructor
  · rintro ⟨z, h1, h2⟩ -/

  


end CategoryTheory
