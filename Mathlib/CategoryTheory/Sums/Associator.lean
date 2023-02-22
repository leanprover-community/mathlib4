/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.sums.associator
! leanprover-community/mathlib commit 590f43db91071eb3134fef935ec9d7cd2a3bd4ce
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Sums.Basic

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
def associator : Sum (Sum C D) E ⥤ Sum C (Sum D E)
    where
  obj X :=
    match X with
    | inl (inl X) => inl X
    | inl (inr X) => inr (inl X)
    | inr X => inr (inr X)
  map X Y f :=
    match X, Y, f with
    | inl (inl X), inl (inl Y), f => f
    | inl (inr X), inl (inr Y), f => f
    | inr X, inr Y, f => f
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
def inverseAssociator : Sum C (Sum D E) ⥤ Sum (Sum C D) E
    where
  obj X :=
    match X with
    | inl X => inl (inl X)
    | inr (inl X) => inl (inr X)
    | inr (inr X) => inr X
  map X Y f :=
    match X, Y, f with
    | inl X, inl Y, f => f
    | inr (inl X), inr (inl Y), f => f
    | inr (inr X), inr (inr Y), f => f
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
    (NatIso.ofComponents (fun X => eqToIso (by tidy)) (by tidy))
    (NatIso.ofComponents (fun X => eqToIso (by tidy)) (by tidy))
#align category_theory.sum.associativity CategoryTheory.sum.associativity

instance associatorIsEquivalence : IsEquivalence (associator C D E) :=
  (by infer_instance : IsEquivalence (associativity C D E).Functor)
#align category_theory.sum.associator_is_equivalence CategoryTheory.sum.associatorIsEquivalence

instance inverseAssociatorIsEquivalence : IsEquivalence (inverseAssociator C D E) :=
  (by infer_instance : IsEquivalence (associativity C D E).inverse)
#align category_theory.sum.inverse_associator_is_equivalence CategoryTheory.sum.inverseAssociatorIsEquivalence

-- TODO unitors?
-- TODO pentagon natural transformation? ...satisfying?
end CategoryTheory.sum

