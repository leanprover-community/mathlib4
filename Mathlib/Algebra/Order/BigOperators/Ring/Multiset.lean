/-
Copyright (c) 2021 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/
import Mathlib.Algebra.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.Ring.List

/-!
# Big operators on a multiset in ordered rings

This file contains the results concerning the interaction of multiset big operators with ordered
rings.
-/

namespace Multiset
variable {R : Type*}

lemma prod_nonneg {R : Type*} [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R]
    [PosMulMono R] {s : Multiset R} (h : ∀ a ∈ s, 0 ≤ a) : 0 ≤ s.prod := by
  revert h
  refine s.induction_on ?_ fun a s hs ih ↦ ?_
  · simp
  · rw [Multiset.prod_cons]
    exact mul_nonneg (ih _ <| mem_cons_self _ _) (hs fun a ha ↦ ih _ <| mem_cons_of_mem ha)

lemma one_le_prod {R : Type*} [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R]
    [PosMulMono R] {s : Multiset R} (h : ∀ a ∈ s, 1 ≤ a) : 1 ≤ s.prod := by
  revert h
  refine s.induction_on ?_ fun a s hs ih ↦ ?_
  · simp
  · rw [prod_cons]
    exact one_le_mul_of_one_le_of_one_le (ih _ <| mem_cons_self _ _)
        (hs fun a ha ↦ ih _ <| mem_cons_of_mem ha)

lemma prod_pos {R : Type*} [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R]
    [NeZero (1 : R)] [PosMulStrictMono R] {s : Multiset R} (h : ∀ a ∈ s, 0 < a) : 0 < s.prod := by
  revert h
  refine s.induction_on ?_ fun a s hs ih ↦ ?_
  · simp
  · rw [prod_cons]
    exact mul_pos (ih _ <| mem_cons_self _ _) (hs fun a ha ↦ ih _ <| mem_cons_of_mem ha)

theorem prod_map_le_prod_map₀ {ι α : Type*} [CommMonoidWithZero α] [PartialOrder α]
    [ZeroLEOneClass α] [PosMulMono α] {s : Multiset ι} (f : ι → α) (g : ι → α)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ g i) :
    (map f s).prod ≤ (map g s).prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s hind =>
    simp only [map_cons, prod_cons]
    have := posMulMono_iff_mulPosMono.1 ‹PosMulMono α›
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

theorem prod_map_lt_prod_map {ι α : Type*} [CommMonoidWithZero α] [PartialOrder α]
    [ZeroLEOneClass α] [MulPosStrictMono α] [NeZero (1 : α)] {s : Multiset ι} (hs : s ≠ 0)
    (f : ι → α) (g : ι → α) (h0 : ∀ i ∈ s, 0 < f i) (h : ∀ i ∈ s, f i < g i) :
    (map f s).prod < (map g s).prod := by
  induction s using Multiset.induction with
  | empty => contradiction
  | cons a s =>
    simp only [map_cons, prod_cons]
    have := posMulStrictMono_iff_mulPosStrictMono.2 ‹MulPosStrictMono α›
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

@[simp]
lemma _root_.CanonicallyOrderedCommSemiring.multiset_prod_pos [CanonicallyOrderedCommSemiring R]
    [Nontrivial R] {m : Multiset R} : 0 < m.prod ↔ ∀ x ∈ m, 0 < x := by
  rcases m with ⟨l⟩
  rw [Multiset.quot_mk_to_coe'', Multiset.prod_coe]
  exact CanonicallyOrderedCommSemiring.list_prod_pos

end Multiset
