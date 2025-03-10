/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Fabrizio Barroero
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.Order.Hom.Basic
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Nonarchimedean functions

A function `f : α → R` is nonarchimedean if it satisfies the strong triangle inequality
`f (a + b) ≤ max (f a) (f b)` for all `a b : α`. This file proves basic properties of
nonarchimedean functions.
-/

namespace IsNonarchimedean

variable {R : Type*} [LinearOrderedSemiring R] {a b : R} {m n : ℕ}

/-- A nonarchimedean function satisfies the triangle inequality. -/
theorem add_le {α : Type*} [Add α] {f : α → R} (hf : ∀ x : α, 0 ≤ f x)
    (hna : IsNonarchimedean f) {a b : α} : f (a + b) ≤ f a + f b := by
  apply le_trans (hna _ _)
  rw [max_le_iff, le_add_iff_nonneg_right, le_add_iff_nonneg_left]
  exact ⟨hf _, hf _⟩

open Finset in
/-- Ultrametric inequality with `Finset.Sum`. -/
lemma apply_sum_le_sup_of_isNonarchimedean {α β : Type*} [AddCommMonoid α] {f : α → R}
    (nonarch : IsNonarchimedean f) {s : Finset β} (hnonempty : s.Nonempty) {l : β → α} :
    f (∑ i ∈ s, l i) ≤ s.sup' hnonempty fun i => f (l i) := by
  induction hnonempty using Nonempty.cons_induction with
  | singleton i => simp
  | cons i s _ hs hind =>
    simp only [sum_cons, le_sup'_iff, mem_cons, exists_eq_or_imp]
    rw [← le_sup'_iff hs]
    rcases le_max_iff.mp <| nonarch (l i) (∑ i ∈ s, l i) with h₁ | h₂
    · exact .inl h₁
    · exact .inr <| le_trans h₂ hind

/-- If `f` is a nonarchimedean additive group seminorm on `α`, then for every `n : ℕ` and `a : α`,
  we have `f (n • a) ≤ (f a)`. -/
theorem nsmul_le {F α : Type*} [AddMonoid α] [FunLike F α R] [ZeroHomClass F α R]
    [NonnegHomClass F α R] {f : F} (hna : IsNonarchimedean f) {n : ℕ} {a : α} :
    f (n • a) ≤ f a := by
  induction n with
  | zero => simp
  | succ n _ =>
    rw [add_nsmul]
    apply le_trans <| hna (n • a) (1 • a)
    simpa

/-- If `f` is a nonarchimedean additive group seminorm on `α`, then for every `n : ℕ` and `a : α`,
  we have `f (n * a) ≤ (f a)`. -/
theorem nmul_le {F α : Type*} [Ring α] [FunLike F α R] [ZeroHomClass F α R] [NonnegHomClass F α R]
    {f : F} (hna : IsNonarchimedean f) {n : ℕ} {a : α} : f (n * a) ≤ f a := by
  rw [← nsmul_eq_mul]
  exact nsmul_le hna

lemma apply_natCast_le_one_of_isNonarchimedean {F α : Type*} [Semiring α] [FunLike F α R]
    [ZeroHomClass F α R] [NonnegHomClass F α R] [OneHomClass F α R] {f : F}
    (hna : IsNonarchimedean f) {n : ℕ} : f n ≤ 1 := by
  rw [← nsmul_one n]
  exact le_trans (nsmul_le hna) (le_of_eq (map_one f))

lemma apply_intCast_le_one_of_isNonarchimedean {F α : Type*} [Ring α] [FunLike F α R]
    [AddGroupSeminormClass F α R] [OneHomClass F α R] {f : F}
    (hna : IsNonarchimedean f) {n : ℤ} : f n ≤ 1 := by
  obtain ⟨a, rfl | rfl⟩ := Int.eq_nat_or_neg n <;>
  simp [map_neg] <;>
  exact apply_natCast_le_one_of_isNonarchimedean hna

lemma apply_sum_eq_of_lt {F α : Type*} [AddGroup α] [FunLike F α R]
    [AddGroupSeminormClass F α R] {f : F} (hna : IsNonarchimedean f) {x y : α}
    (h_lt : f x < f y) : f (x + y) = f y := by
  by_contra! h
  have h1 : f (x + y) ≤ f y := le_trans (hna x y) (le_of_eq <| max_eq_right_of_lt h_lt)
  apply lt_irrefl (f y)
  calc
    f y = f (-x + (x + y)) := by simp
    _   ≤ max (f (-x)) (f (x + y)) := hna (-x) (x + y)
    _   < max (f y) (f y) := by
      rw [max_self, map_neg_eq_map]
      exact max_lt h_lt <| lt_of_le_of_ne h1 h
    _   = f y := max_self (f y)

lemma apply_sum_eq_of_lt' {F α : Type*} [AddGroup α] [FunLike F α R]
    [AddGroupSeminormClass F α R] {f : F} (hna : IsNonarchimedean f) {x y : α}
    (h_lt : f y < f x) : f (x + y) = f x := by
  by_contra! h
  have h1 : f (x + y) ≤ f x := le_trans (hna x y) (le_of_eq <| max_eq_left_of_lt h_lt)
  apply lt_irrefl (f x)
  calc
    f x = f (x + y + -y) := by simp
    _   ≤ max (f (x + y)) (f (-y)) := hna (x + y) (-y)
    _   < max (f x) (f x) := by
      rw [max_self, map_neg_eq_map]
      apply max_lt (lt_of_le_of_ne h1 h) h_lt
    _   = f x := max_self (f x)

/-- If `f` is a nonarchimedean additive group seminorm on `α` and `x y : α` are such that
  `f x ≠ f y`, then `f (x + y) = max (f x) (f y)`. -/
theorem add_eq_max_of_ne {F α : Type*} [AddGroup α] [FunLike F α R]
    [AddGroupSeminormClass F α R] {f : F} (hna : IsNonarchimedean f) {x y : α} (hne : f x ≠ f y) :
    f (x + y) = max (f x) (f y) := by
  rcases hne.lt_or_lt with h_lt | h_lt
  · rw [apply_sum_eq_of_lt hna h_lt]
    exact (max_eq_right_of_lt h_lt).symm
  · rw [apply_sum_eq_of_lt' hna h_lt]
    exact Eq.symm (max_eq_left_of_lt h_lt)

end IsNonarchimedean
