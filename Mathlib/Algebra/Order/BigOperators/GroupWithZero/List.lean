/-
Copyright (c) 2021 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell, Daniel Weber
-/
import Mathlib.Algebra.BigOperators.Group.List
import Mathlib.Algebra.Order.GroupWithZero.Unbundled

/-!
# Big operators on a list in ordered groups with zeros

This file contains the results concerning the interaction of list big operators with ordered
groups with zeros.
-/

namespace List
variable {R : Type*} [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R] [PosMulMono R]

lemma prod_nonneg {s : List R} (h : ∀ a ∈ s, 0 ≤ a) : 0 ≤ s.prod := by
  induction s with
  | nil => simp
  | cons head tail hind =>
    simp only [prod_cons]
    simp only [mem_cons, forall_eq_or_imp] at h
    exact mul_nonneg h.1 (hind h.2)


lemma one_le_prod {s : List R} (h : ∀ a ∈ s, 1 ≤ a) : 1 ≤ s.prod := by
  induction s with
  | nil => simp
  | cons head tail hind =>
    simp only [prod_cons]
    simp only [mem_cons, forall_eq_or_imp] at h
    exact one_le_mul_of_one_le_of_one_le h.1 (hind h.2)

theorem prod_map_le_prod_map₀ {ι : Type*} {s : List ι} (f : ι → R) (g : ι → R)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ g i) :
    (map f s).prod ≤ (map g s).prod := by
  induction s with
  | nil => simp
  | cons a s hind =>
    simp only [map_cons, prod_cons]
    have := posMulMono_iff_mulPosMono.1 ‹PosMulMono R›
    apply mul_le_mul
    · apply h
      simp
    · apply hind
      · intro i hi
        apply h0
        simp [hi]
      · intro i hi
        apply h
        simp [hi]
    apply prod_nonneg
    · simp only [mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro a ha
      apply h0
      simp [ha]
    apply (h0 _ _).trans (h _ _) <;> simp

omit [PosMulMono R]
variable [PosMulStrictMono R] [NeZero (1 : R)]

lemma prod_pos {s : List R} (h : ∀ a ∈ s, 0 < a) : 0 < s.prod := by
  induction s with
  | nil => simp
  | cons a s hind =>
    simp only [prod_cons]
    simp only [mem_cons, forall_eq_or_imp] at h
    exact mul_pos h.1 (hind h.2)

theorem prod_map_lt_prod_map {ι : Type*} {s : List ι} (hs : s ≠ [])
    (f : ι → R) (g : ι → R) (h0 : ∀ i ∈ s, 0 < f i) (h : ∀ i ∈ s, f i < g i) :
    (map f s).prod < (map g s).prod := by
  match s with
  | [] => contradiction
  | a :: s =>
    simp only [map_cons, prod_cons]
    have := posMulStrictMono_iff_mulPosStrictMono.1 ‹PosMulStrictMono R›
    apply mul_lt_mul
    · apply h
      simp
    · apply prod_map_le_prod_map₀
      · intro i hi
        apply le_of_lt
        apply h0
        simp [hi]
      · intro i hi
        apply le_of_lt
        apply h
        simp [hi]
    apply prod_pos
    · simp only [mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro a ha
      apply h0
      simp [ha]
    apply le_of_lt ((h0 _ _).trans (h _ _)) <;> simp

end List
