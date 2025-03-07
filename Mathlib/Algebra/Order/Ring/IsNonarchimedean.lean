/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/

import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.Order.Hom.Basic
import Mathlib.Data.Nat.Choose.Sum

/-!
# Nonarchimedean functions

A function `f : α → R` is nonarchimedean if it satisfies the strong triangle inequality
`f (a + b) ≤ max (f a) (f b)` for all `a b : α`. This file proves basic properties of
nonarchimedean functions.
-/

namespace IsNonarchimedean

variable {R : Type*} [LinearOrderedSemiring R] {a b : R} {m n : ℕ}

/-- A nonarchimedean function satisfies the triangle inequality. -/
theorem add_le {F α : Type*} [Add α] [FunLike F α R] [NonnegHomClass F α R] {f : F}
    (hna : IsNonarchimedean f) {a b : α} : f (a + b) ≤ f a + f b := by
  apply le_trans (hna _ _)
  rw [max_le_iff, le_add_iff_nonneg_right, le_add_iff_nonneg_left]
  exact ⟨apply_nonneg f b, apply_nonneg f a⟩

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
    simpa only [one_nsmul, sup_le_iff, le_refl, and_true]

lemma apply_natCast_le_one_of_isNonarchimedean {F α : Type*} [Semiring α] [FunLike F α R]
    [ZeroHomClass F α R] [NonnegHomClass F α R] [MonoidHomClass F α R] {f : F}
    (hna : IsNonarchimedean f) {n : ℕ} : f n ≤ 1 := by
  rw [← nsmul_one ↑n]
  exact le_trans (nsmul_le hna) (le_of_eq (map_one f))

lemma apply_intCast_le_one_of_isNonarchimedean {F α : Type*} [Ring α] [FunLike F α R]
    [ZeroHomClass F α R] [NonnegHomClass F α R] [MonoidHomClass F α R] {f : F}
    (hna : IsNonarchimedean f) (map_neg : ∀ a, f (-a) = f a) {n : ℤ} : f n ≤ 1 := by
  obtain ⟨a, rfl | rfl⟩ := Int.eq_nat_or_neg n <;>
  simp [map_neg, apply_natCast_le_one_of_isNonarchimedean hna]

/-- If `f` is a nonarchimedean additive group seminorm on `α`, then for every `n : ℕ` and `a : α`,
  we have `f (n * a) ≤ (f a)`. -/
theorem nmul_le {F α : Type*} [Ring α] [FunLike F α R] [AddGroupSeminormClass F α R]
    {f : F} (hna : IsNonarchimedean f) {n : ℕ} {a : α} : f (n * a) ≤ f a := by
  rw [← nsmul_eq_mul]
  exact nsmul_le hna

/-- If `f` is a nonarchimedean additive group seminorm on `α` and `x y : α` are such that
  `f x ≠ f y`, then `f (x + y) = max (f x) (f y)`. -/
theorem add_eq_max_of_ne {F α : Type*} [AddGroup α] [FunLike F α R]
    [AddGroupSeminormClass F α R] {f : F} (hna : IsNonarchimedean f) {x y : α} (hne : f x ≠ f y) :
    f (x + y) = max (f x) (f y) := by
  sorry
  /- let _ := AddGroupSeminormClass.toSeminormedAddGroup f
  have := AddGroupSeminormClass.isUltrametricDist hna
  simp only [← AddGroupSeminormClass.toSeminormedAddGroup_norm_eq] at hne ⊢
  exact norm_add_eq_max_of_norm_ne_norm hne -/

/-- Given a nonarchimedean additive group seminorm `f` on `α`, a function `g : β → α` and a finset
  `t : Finset β`, we can always find `b : β`, belonging to `t` if `t` is nonempty, such that
  `f (t.sum g) ≤ f (g b)` . -/
theorem finset_image_add {F α β : Type*} [AddCommGroup α] [FunLike F α R]
    [AddGroupSeminormClass F α R] [Nonempty β] {f : F} (hna : IsNonarchimedean f)
    (g : β → α) (t : Finset β) :
    ∃ b : β, (t.Nonempty → b ∈ t) ∧ f (t.sum g) ≤ f (g b) := by
  sorry

/-- Given a nonarchimedean additive group seminorm `f` on `α`, a function `g : β → α` and a
  nonempty finset `t : Finset β`, we can always find `b : β` belonging to `t` such that
  `f (t.sum g) ≤ f (g b)` . -/
theorem finset_image_add_of_nonempty {F α β : Type*} [AddCommGroup α] [FunLike F α R]
    [AddGroupSeminormClass F α R] [Nonempty β] {f : F} (hna : IsNonarchimedean f)
    (g : β → α) {t : Finset β} (ht : t.Nonempty) :
    ∃ b : β, (b ∈ t) ∧ f (t.sum g) ≤ f (g b) := by
  obtain ⟨b, hbt, hbf⟩ := finset_image_add hna g t
  exact ⟨b, hbt ht, hbf⟩

/-- Given a nonarchimedean additive group seminorm `f` on `α`, a function `g : β → α` and a
  multiset `s : Multiset β`, we can always find `b : β`, belonging to `s` if `s` is nonempty,
  such that `f (t.sum g) ≤ f (g b)` . -/
theorem multiset_image_add {F α β : Type*} [AddCommGroup α] [FunLike F α R]
    [AddGroupSeminormClass F α R] [Nonempty β] {f : F} (hna : IsNonarchimedean f)
    (g : β → α) (s : Multiset β) :
    ∃ b : β, (s ≠ 0 → b ∈ s) ∧ f (Multiset.map g s).sum ≤ f (g b) := by
  sorry

/-- Given a nonarchimedean additive group seminorm `f` on `α`, a function `g : β → α` and a
  nonempty multiset `s : Multiset β`, we can always find `b : β` belonging to `s` such that
  `f (t.sum g) ≤ f (g b)` . -/
theorem multiset_image_add_of_nonempty {F α β : Type*} [AddCommGroup α] [FunLike F α R]
    [AddGroupSeminormClass F α R] [Nonempty β] {f : F} (hna : IsNonarchimedean f)
    (g : β → α) {s : Multiset β} (hs : s ≠ 0) :
    ∃ b : β, (b ∈ s) ∧ f (Multiset.map g s).sum ≤ f (g b) := by
  obtain ⟨b, hbs, hbf⟩ := multiset_image_add hna g s
  exact ⟨b, hbs hs, hbf⟩

/-- If `f` is a nonarchimedean additive group seminorm on a commutative ring `α`, `n : ℕ`, and
  `a b : α`, then we can find `m : ℕ` such that `m ≤ n` and
  `f ((a + b) ^ n) ≤ (f (a ^ m)) * (f (b ^ (n - m)))`. -/
theorem add_pow_le {F α : Type*} [CommRing α] [FunLike F α R]
    [RingSeminormClass F α R] {f : F} (hna : IsNonarchimedean f) (n : ℕ) (a b : α) :
    ∃ m < n + 1, f ((a + b) ^ n) ≤ f (a ^ m) * f (b ^ (n - m)) := by
  obtain ⟨m, hm_lt, hM⟩ := finset_image_add hna
    (fun m => a ^ m * b ^ (n - m) * ↑(n.choose m)) (Finset.range (n + 1))
  simp only [Finset.nonempty_range_iff, ne_eq, Nat.succ_ne_zero, not_false_iff, Finset.mem_range,
    if_true, forall_true_left] at hm_lt
  refine ⟨m, hm_lt, ?_⟩
  simp only [← add_pow] at hM
  rw [mul_comm] at hM
  exact le_trans hM (le_trans (nmul_le hna) (map_mul_le_mul _ _ _))

end IsNonarchimedean

#min_imports
