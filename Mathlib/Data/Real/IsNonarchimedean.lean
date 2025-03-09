/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Analysis.Normed.Order.Hom.Ultra
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Data.Nat.Choose.Sum

/-!
# Nonarchimedean functions

A function `f : R → ℝ≥0` is nonarchimedean if it satisfies the strong triangle inequality
`f (r + s) ≤ max (f r) (f s)` for all `r s : R`. This file proves basic properties of
nonarchimedean functions.
-/

namespace IsNonarchimedean

open IsUltrametricDist

/-- Given a nonarchimedean additive group seminorm `f` on `α`, a function `g : β → α` and a finset
  `t : Finset β`, we can always find `b : β`, belonging to `t` if `t` is nonempty, such that
  `f (t.sum g) ≤ f (g b)` . -/
theorem finset_image_add {F α β : Type*} [AddCommGroup α] [FunLike F α ℝ]
    [AddGroupSeminormClass F α ℝ] [Nonempty β] {f : F} (hna : IsNonarchimedean f)
    (g : β → α) (t : Finset β) :
    ∃ b : β, (t.Nonempty → b ∈ t) ∧ f (t.sum g) ≤ f (g b) := by
  let _ := AddGroupSeminormClass.toSeminormedAddCommGroup f
  have := AddGroupSeminormClass.isUltrametricDist hna
  simp only [← AddGroupSeminormClass.toSeminormedAddCommGroup_norm_eq]
  apply exists_norm_finset_sum_le

/-- Given a nonarchimedean additive group seminorm `f` on `α`, a function `g : β → α` and a
  nonempty finset `t : Finset β`, we can always find `b : β` belonging to `t` such that
  `f (t.sum g) ≤ f (g b)` . -/
theorem finset_image_add_of_nonempty {F α β : Type*} [AddCommGroup α] [FunLike F α ℝ]
    [AddGroupSeminormClass F α ℝ] [Nonempty β] {f : F} (hna : IsNonarchimedean f)
    (g : β → α) {t : Finset β} (ht : t.Nonempty) :
    ∃ b : β, (b ∈ t) ∧ f (t.sum g) ≤ f (g b) := by
  obtain ⟨b, hbt, hbf⟩ := finset_image_add hna g t
  exact ⟨b, hbt ht, hbf⟩

/-- Given a nonarchimedean additive group seminorm `f` on `α`, a function `g : β → α` and a
  multiset `s : Multiset β`, we can always find `b : β`, belonging to `s` if `s` is nonempty,
  such that `f (t.sum g) ≤ f (g b)` . -/
theorem multiset_image_add {F α β : Type*} [AddCommGroup α] [FunLike F α ℝ]
    [AddGroupSeminormClass F α ℝ] [Nonempty β] {f : F} (hna : IsNonarchimedean f)
    (g : β → α) (s : Multiset β) :
    ∃ b : β, (s ≠ 0 → b ∈ s) ∧ f (Multiset.map g s).sum ≤ f (g b) := by
  let _ := AddGroupSeminormClass.toSeminormedAddCommGroup f
  have := AddGroupSeminormClass.isUltrametricDist hna
  simp only [← AddGroupSeminormClass.toSeminormedAddCommGroup_norm_eq]
  apply exists_norm_multiset_sum_le

/-- Given a nonarchimedean additive group seminorm `f` on `α`, a function `g : β → α` and a
  nonempty multiset `s : Multiset β`, we can always find `b : β` belonging to `s` such that
  `f (t.sum g) ≤ f (g b)` . -/
theorem multiset_image_add_of_nonempty {F α β : Type*} [AddCommGroup α] [FunLike F α ℝ]
    [AddGroupSeminormClass F α ℝ] [Nonempty β] {f : F} (hna : IsNonarchimedean f)
    (g : β → α) {s : Multiset β} (hs : s ≠ 0) :
    ∃ b : β, (b ∈ s) ∧ f (Multiset.map g s).sum ≤ f (g b) := by
  obtain ⟨b, hbs, hbf⟩ := multiset_image_add hna g s
  exact ⟨b, hbs hs, hbf⟩

/-- If `f` is a nonarchimedean additive group seminorm on a commutative ring `α`, `n : ℕ`, and
  `a b : α`, then we can find `m : ℕ` such that `m ≤ n` and
  `f ((a + b) ^ n) ≤ (f (a ^ m)) * (f (b ^ (n - m)))`. -/
theorem add_pow_le {F α : Type*} [CommRing α] [FunLike F α ℝ]
    [RingSeminormClass F α ℝ] {f : F} (hna : IsNonarchimedean f) (n : ℕ) (a b : α) :
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
