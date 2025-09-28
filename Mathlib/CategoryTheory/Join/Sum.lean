/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Join.Basic
import Mathlib.CategoryTheory.Sums.Basic

/-!
# Embedding of `C ⊕ D` into `C ⋆ D`

This file constructs a canonical functor `Join.fromSum` from `C ⊕ D` to `C ⋆ D` and give
its characterization in terms of the canonical inclusions.
We also provide `Faithful` and `EssSurj` instances on this functor.

-/

namespace CategoryTheory.Join

variable (C D : Type*) [Category C] [Category D]

/-- The canonical functor from the sum to the join.
It sends `inl c` to `left c` and `inr d` to `right d`. -/
@[simps! obj] -- Maps get characterized w.r.t. the inclusions below
def fromSum : C ⊕ D ⥤ C ⋆ D := (inclLeft C D).sum' <| inclRight C D

variable {C} in
@[simp]
lemma fromSum_map_inl {c c' : C} (f : c ⟶ c') :
    (fromSum C D).map ((Sum.inl_ C D).map f) = (inclLeft C D).map f :=
  rfl

variable {D} in
@[simp]
lemma fromSum_map_inr {d d' : D} (f : d ⟶ d') :
    (fromSum C D).map ((Sum.inr_ C D).map f) = (inclRight C D).map f :=
  rfl

/-- Characterization of `fromSum` with respect to the left inclusion. -/
@[simps! hom_app inv_app]
def inlCompFromSum : Sum.inl_ C D ⋙ fromSum C D ≅ inclLeft C D := Functor.inlCompSum' _ _

/-- Characterization of `fromSum` with respect to the right inclusion. -/
@[simps! hom_app inv_app]
def inrCompFromSum : Sum.inr_ C D ⋙ fromSum C D ≅ inclRight C D := Functor.inrCompSum' _ _

instance : (fromSum C D).EssSurj where
  mem_essImage
    | left c => Functor.obj_mem_essImage _ (Sum.inl c)
    | right d => Functor.obj_mem_essImage _ (Sum.inr d)

instance : (fromSum C D).Faithful where
  map_injective {x y} h h' heq := by
    cases h <;> cases h'
    all_goals
      simp only [fromSum_obj, Sum.inl__obj, fromSum_map_inl, Sum.inr__obj, fromSum_map_inr] at heq
      simp [Functor.map_injective _ heq]

end CategoryTheory.Join
