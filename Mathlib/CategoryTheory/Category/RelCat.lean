/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Opposites
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

instance typeRelFunctor_essSurj : EssSurj typeRelFunctor :=
    typeRelFunctor.essSurj_of_surj Function.surjective_id

open Classical
theorem rel_iso_iff {X Y : RelCat} (r : X ⟶ Y) :
    IsIso (C := RelCat) r ↔ ∃ f : (Iso (C := Type) X Y), typeRelFunctor.map f.hom = r := by
  constructor
  · intro h
    have h1 := congr_fun₂ h.hom_inv_id
    have h2 := congr_fun₂ h.inv_hom_id
    simp only [rel_comp_apply₂, rel_id_apply₂, eq_iff_iff] at h1 h2
    obtain ⟨f, hf⟩ := axiomOfChoice (fun a => (h1 a a).mpr rfl)
    obtain ⟨g, hg⟩ := axiomOfChoice (fun a => (h2 a a).mpr rfl)
    suffices hif : IsIso (C := Type) f by
      use asIso f
      ext x y
      simp only [asIso_hom, typeRelFunctor_map]
      constructor
      · rintro rfl
        exact (hf x).1
      · intro hr
        specialize h2 (f x) y
        rw[← h2]
        use x, (hf x).2, hr
    use g
    constructor
    · ext x
      apply (h1 _ _).mp
      use f x, (hg _).2, (hf _).2
    · ext y
      apply (h2 _ _).mp
      use g y, (hf (g y)).2, (hg y).2
  · rintro ⟨f, rfl⟩
    apply typeRelFunctor.map_isIso

section Opposite
open Opposite

def rel_relOp : Functor RelCat RelCatᵒᵖ where
  obj X := Opposite.op X
  map {X Y} r := op (fun y x => r x y)
  map_id X := by
    congr
    simp only [unop_op, rel_id]
    ext x y
    exact Eq.comm
  map_comp {X Y Z} f g := by
    unfold Category.opposite
    congr
    ext x y
    apply exists_congr
    exact fun a => And.comm

instance rel_relOp_full : Full rel_relOp where
  preimage f := Function.swap f.unop
  witness _ := rfl

instance rel_relOp_faithful : Faithful rel_relOp where
  map_injective {X Y f g} h := by
    ext x y
    exact iff_of_eq (congr_fun₂ (op_injective h) y x)

instance rel_relOp_essSurh : EssSurj rel_relOp :=
  rel_relOp.essSurj_of_surj _

def rel_relOp_equivalence : Equivalence (RelCat ᵒᵖ) RelCat :=


end Opposite


--def rel_relOp_equivalence : relᵒᵖ ≌ rel :=


end CategoryTheory
