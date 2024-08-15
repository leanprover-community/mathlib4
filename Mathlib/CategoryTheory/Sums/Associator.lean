/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Sums.Basic

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
def associator : (C ⊕ D) ⊕ E ⥤ C ⊕ (D ⊕ E) where
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

@[simp]
theorem associator_obj_inl_inl (X) : (associator C D E).obj (inl (inl X)) = inl X :=
  rfl

@[simp]
theorem associator_obj_inl_inr (X) : (associator C D E).obj (inl (inr X)) = inr (inl X) :=
  rfl

@[simp]
theorem associator_obj_inr (X) : (associator C D E).obj (inr X) = inr (inr X) :=
  rfl

@[simp]
theorem associator_map_inl_inl {X Y : C} (f : inl (inl X) ⟶ inl (inl Y)) :
    (associator C D E).map f = f :=
  rfl

@[simp]
theorem associator_map_inl_inr {X Y : D} (f : inl (inr X) ⟶ inl (inr Y)) :
    (associator C D E).map f = f :=
  rfl

@[simp]
theorem associator_map_inr {X Y : E} (f : inr X ⟶ inr Y) : (associator C D E).map f = f :=
  rfl

/-- The inverse associator functor `C ⊕ (D ⊕ E) ⥤ (C ⊕ D) ⊕ E` for sums of categories.
-/
def inverseAssociator : C ⊕ (D ⊕ E) ⥤ (C ⊕ D) ⊕ E where
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

@[simp]
theorem inverseAssociator_obj_inl (X) : (inverseAssociator C D E).obj (inl X) = inl (inl X) :=
  rfl

@[simp]
theorem inverseAssociator_obj_inr_inl (X) :
    (inverseAssociator C D E).obj (inr (inl X)) = inl (inr X) :=
  rfl

@[simp]
theorem inverseAssociator_obj_inr_inr (X) : (inverseAssociator C D E).obj (inr (inr X)) = inr X :=
  rfl

@[simp]
theorem inverseAssociator_map_inl {X Y : C} (f : inl X ⟶ inl Y) :
    (inverseAssociator C D E).map f = f :=
  rfl

@[simp]
theorem inverseAssociator_map_inr_inl {X Y : D} (f : inr (inl X) ⟶ inr (inl Y)) :
    (inverseAssociator C D E).map f = f :=
  rfl

@[simp]
theorem inverseAssociator_map_inr_inr {X Y : E} (f : inr (inr X) ⟶ inr (inr Y)) :
    (inverseAssociator C D E).map f = f :=
  rfl

/-- The equivalence of categories expressing associativity of sums of categories.
-/
def associativity : (C ⊕ D) ⊕ E ≌ C ⊕ (D ⊕ E) :=
  Equivalence.mk (associator C D E) (inverseAssociator C D E)
    (NatIso.ofComponents (fun X => eqToIso
      (by rcases X with ((_|_)|_) <;> rfl)) -- Porting note: aesop_cat fails
      (by rintro ((_|_)|_) ((_|_)|_) f <;> first | cases f | aesop_cat))
    (NatIso.ofComponents (fun X => eqToIso
      (by rcases X with (_|(_|_)) <;> rfl)) -- Porting note: aesop_cat fails
      (by rintro (_|(_|_)) (_|(_|_)) f <;> first | cases f | aesop_cat))

instance associatorIsEquivalence : (associator C D E).IsEquivalence :=
  (by infer_instance : (associativity C D E).functor.IsEquivalence)

instance inverseAssociatorIsEquivalence : (inverseAssociator C D E).IsEquivalence :=
  (by infer_instance : (associativity C D E).inverse.IsEquivalence)

-- TODO unitors?
-- TODO pentagon natural transformation? ...satisfying?
end CategoryTheory.sum
