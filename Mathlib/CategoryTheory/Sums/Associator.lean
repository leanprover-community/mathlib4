/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Sums.Basic

#align_import category_theory.sums.associator from "leanprover-community/mathlib"@"590f43db91071eb3134fef935ec9d7cd2a3bd4ce"

/-!
# Associator for binary disjoint union of categories.

The associator functor `((C ⊕ D) ⊕ E) ⥤ (C ⊕ (D ⊕ E))` and its inverse form an equivalence.
-/


universe v u

open CategoryTheory

open Sum

namespace CategoryTheory.sum

variable (C : Type u) [Category.{v} C] (D : Type u) [Category.{v} D] (E : Type u) [Category.{v} E]

/-- The associator functor `(C ⊕ D) ⊕ E ⥤ C ⊕ (D ⊕ E)` for sums of categories.
-/
def associator : Sum (Sum C D) E ⥤ Sum C (Sum D E) where
  obj X :=
    match X with
    | inl (inl X) => inl X
    | inl (inr X) => inr (inl X)
    | inr X => inr (inr X)
  map {X Y} f :=
    match X, Y, f with
    | inl (inl _), inl (inl _), f => f
    | inl (inr _), inl (inr _), f => f
    | inr _, inr _, f => f
  map_id := by rintro ((_|_)|_) <;> rfl
  map_comp := by
    rintro ((_|_)|_) ((_|_)|_) ((_|_)|_) f g <;> first | cases f | cases g | aesop_cat
#align category_theory.sum.associator CategoryTheory.sum.associator

@[simp]
theorem associator_obj_inl_inl (X) : (associator C D E).obj (inl (inl X)) = inl X :=
  rfl
#align category_theory.sum.associator_obj_inl_inl CategoryTheory.sum.associator_obj_inl_inl

@[simp]
theorem associator_obj_inl_inr (X) : (associator C D E).obj (inl (inr X)) = inr (inl X) :=
  rfl
#align category_theory.sum.associator_obj_inl_inr CategoryTheory.sum.associator_obj_inl_inr

@[simp]
theorem associator_obj_inr (X) : (associator C D E).obj (inr X) = inr (inr X) :=
  rfl
#align category_theory.sum.associator_obj_inr CategoryTheory.sum.associator_obj_inr

@[simp]
theorem associator_map_inl_inl {X Y : C} (f : inl (inl X) ⟶ inl (inl Y)) :
    (associator C D E).map f = f :=
  rfl
#align category_theory.sum.associator_map_inl_inl CategoryTheory.sum.associator_map_inl_inl

@[simp]
theorem associator_map_inl_inr {X Y : D} (f : inl (inr X) ⟶ inl (inr Y)) :
    (associator C D E).map f = f :=
  rfl
#align category_theory.sum.associator_map_inl_inr CategoryTheory.sum.associator_map_inl_inr

@[simp]
theorem associator_map_inr {X Y : E} (f : inr X ⟶ inr Y) : (associator C D E).map f = f :=
  rfl
#align category_theory.sum.associator_map_inr CategoryTheory.sum.associator_map_inr

/-- The inverse associator functor `C ⊕ (D ⊕ E) ⥤ (C ⊕ D) ⊕ E` for sums of categories.
-/
def inverseAssociator : Sum C (Sum D E) ⥤ Sum (Sum C D) E where
  obj X :=
    match X with
    | inl X => inl (inl X)
    | inr (inl X) => inl (inr X)
    | inr (inr X) => inr X
  map {X Y} f :=
    match X, Y, f with
    | inl _, inl _, f => f
    | inr (inl _), inr (inl _), f => f
    | inr (inr _), inr (inr _), f => f
  map_id := by rintro (_|(_|_)) <;> rfl
  map_comp := by
    rintro (_|(_|_)) (_|(_|_)) (_|(_|_)) f g <;> first | cases f | cases g | aesop_cat
#align category_theory.sum.inverse_associator CategoryTheory.sum.inverseAssociator

@[simp]
theorem inverseAssociator_obj_inl (X) : (inverseAssociator C D E).obj (inl X) = inl (inl X) :=
  rfl
#align category_theory.sum.inverse_associator_obj_inl CategoryTheory.sum.inverseAssociator_obj_inl

@[simp]
theorem inverseAssociator_obj_inr_inl (X) :
    (inverseAssociator C D E).obj (inr (inl X)) = inl (inr X) :=
  rfl
#align category_theory.sum.inverse_associator_obj_inr_inl CategoryTheory.sum.inverseAssociator_obj_inr_inl

@[simp]
theorem inverseAssociator_obj_inr_inr (X) : (inverseAssociator C D E).obj (inr (inr X)) = inr X :=
  rfl
#align category_theory.sum.inverse_associator_obj_inr_inr CategoryTheory.sum.inverseAssociator_obj_inr_inr

@[simp]
theorem inverseAssociator_map_inl {X Y : C} (f : inl X ⟶ inl Y) :
    (inverseAssociator C D E).map f = f :=
  rfl
#align category_theory.sum.inverse_associator_map_inl CategoryTheory.sum.inverseAssociator_map_inl

@[simp]
theorem inverseAssociator_map_inr_inl {X Y : D} (f : inr (inl X) ⟶ inr (inl Y)) :
    (inverseAssociator C D E).map f = f :=
  rfl
#align category_theory.sum.inverse_associator_map_inr_inl CategoryTheory.sum.inverseAssociator_map_inr_inl

@[simp]
theorem inverseAssociator_map_inr_inr {X Y : E} (f : inr (inr X) ⟶ inr (inr Y)) :
    (inverseAssociator C D E).map f = f :=
  rfl
#align category_theory.sum.inverse_associator_map_inr_inr CategoryTheory.sum.inverseAssociator_map_inr_inr

/-- The equivalence of categories expressing associativity of sums of categories.
-/
def associativity : Sum (Sum C D) E ≌ Sum C (Sum D E) :=
  Equivalence.mk (associator C D E) (inverseAssociator C D E)
    (NatIso.ofComponents (fun X => eqToIso
      (by rcases X with ((_|_)|_) <;> rfl)) -- Porting note: aesop_cat fails
      (by rintro ((_|_)|_) ((_|_)|_) f <;> first | cases f | aesop_cat))
    (NatIso.ofComponents (fun X => eqToIso
      (by rcases X with (_|(_|_)) <;> rfl)) -- Porting note: aesop_cat fails
      (by rintro (_|(_|_)) (_|(_|_)) f <;> first | cases f | aesop_cat))
#align category_theory.sum.associativity CategoryTheory.sum.associativity

instance associatorIsEquivalence : (associator C D E).IsEquivalence :=
  (by infer_instance : (associativity C D E).functor.IsEquivalence)
#align category_theory.sum.associator_is_equivalence CategoryTheory.sum.associatorIsEquivalence

instance inverseAssociatorIsEquivalence : (inverseAssociator C D E).IsEquivalence :=
  (by infer_instance : (associativity C D E).inverse.IsEquivalence)
#align category_theory.sum.inverse_associator_is_equivalence CategoryTheory.sum.inverseAssociatorIsEquivalence

-- TODO unitors?
-- TODO pentagon natural transformation? ...satisfying?
end CategoryTheory.sum
