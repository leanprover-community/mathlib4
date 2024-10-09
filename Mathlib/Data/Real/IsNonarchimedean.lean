/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Order.Hom.Ultra
import Mathlib.Data.Nat.Choose.Sum

/-!
# Nonarchimedean functions

A function `f : R → ℝ≥0` is nonarchimedean if it satisfies the strong triangle inequality
`f (r + s) ≤ max (f r) (f s)` for all `r s : R`. This file proves basic properties of
nonarchimedean functions.
-/

namespace IsNonarchimedean

open IsUltrametricDist

/-- A nonarchimedean function satisfies the triangle inequality. -/
theorem add_le {α : Type*} [Add α] {f : α → ℝ} (hf : ∀ x : α, 0 ≤ f x)
    (hna : IsNonarchimedean f) {a b : α} : f (a + b) ≤ f a + f b := by
  apply le_trans (hna _ _)
  rw [max_le_iff, le_add_iff_nonneg_right, le_add_iff_nonneg_left]
  exact ⟨hf _, hf _⟩

/-- If `f` is a nonarchimedean additive group seminorm on `α`, then for every `n : ℕ` and `a : α`,
  we have `f (n • a) ≤ (f a)`. -/
theorem nsmul_le {F α : Type*} [AddGroup α] [FunLike F α ℝ]
    [AddGroupSeminormClass F α ℝ] {f : F} (hna : IsNonarchimedean f) {n : ℕ} {a : α} :
    f (n • a) ≤ f a := by
  let _ := AddGroupSeminormClass.toSeminormedAddGroup f
  have := AddGroupSeminormClass.isUltrametricDist hna
  simp_rw [← AddGroupSeminormClass.toSeminormedAddGroup_norm_eq]
  exact norm_nsmul_le _ _

/-- If `f` is a nonarchimedean additive group seminorm on `α`, then for every `n : ℕ` and `a : α`,
  we have `f (n * a) ≤ (f a)`. -/
theorem nmul_le {F α : Type*} [Ring α] [FunLike F α ℝ] [AddGroupSeminormClass F α ℝ]
    {f : F} (hna : IsNonarchimedean f) {n : ℕ} {a : α} : f (n * a) ≤ f a := by
  rw [← nsmul_eq_mul]
  exact nsmul_le hna

/-- If `f` is a nonarchimedean additive group seminorm on `α` and `x y : α` are such that
  `f x ≠ f y`, then `f (x + y) = max (f x) (f y)`. -/
theorem add_eq_max_of_ne {F α : Type*} [AddGroup α] [FunLike F α ℝ]
    [AddGroupSeminormClass F α ℝ] {f : F} (hna : IsNonarchimedean f) {x y : α} (hne : f x ≠ f y) :
    f (x + y) = max (f x) (f y) := by
  let _ := AddGroupSeminormClass.toSeminormedAddGroup f
  have := AddGroupSeminormClass.isUltrametricDist hna
  simp_rw [← AddGroupSeminormClass.toSeminormedAddGroup_norm_eq] at hne ⊢
  exact norm_add_eq_max_of_norm_ne_norm hne

/-- Given a nonarchimedean additive group seminorm `f` on `α`, a function `g : β → α` and a finset
  `t : Finset β`, we can always find `b : β`, belonging to `t` if `t` is nonempty, such that
  `f (t.sum g) ≤ f (g b)` . -/
theorem finset_image_add {F α β : Type*} [AddCommGroup α] [FunLike F α ℝ]
    [AddGroupSeminormClass F α ℝ] [Nonempty β] {f : F} (hna : IsNonarchimedean f)
    (g : β → α) (t : Finset β) :
    ∃ b : β, (t.Nonempty → b ∈ t) ∧ f (t.sum g) ≤ f (g b) := by
  let _ := AddGroupSeminormClass.toSeminormedAddCommGroup f
  have := AddGroupSeminormClass.isUltrametricDist' hna
  simp_rw [← AddGroupSeminormClass.toSeminormedAddCommGroup_norm_eq]
  rcases t.eq_empty_or_nonempty with rfl|ht
  · simp
  have ht' : ∀ x ∈ t, ∀ y ∈ t, ∃ z ∈ t, ‖g z‖ = max ‖g x‖ ‖g y‖ := by
    intros x hx y hy
    rcases le_total ‖g x‖ ‖g y‖ with h|h
    · exact ⟨y, hy, by simp [h]⟩
    · exact ⟨x, hx, by simp [h]⟩
  obtain ⟨x, hx, hx'⟩ := Finset.sup'_mem (α := ℝ) ((‖g ·‖) '' t) (by simpa [sup_eq_max] using ht') t
    ht (‖g ·‖) (fun _ ↦ Set.mem_image_of_mem _)
  refine ⟨x, fun _ ↦ by simpa using hx, ?_⟩
  dsimp only at hx'
  rw [hx']
  exact ht.norm_sum_le_sup'_norm _

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
    ∃ b : β, (0 < Multiset.card s → b ∈ s) ∧ f (Multiset.map g s).sum ≤ f (g b) := by
  inhabit β
  induction s using Multiset.induction_on with
  | empty =>
      rw [Multiset.map_zero, Multiset.sum_zero, Multiset.card_zero, map_zero f]
      exact ⟨default, by simp only [not_lt_zero', IsEmpty.forall_iff], apply_nonneg _ _⟩
  | @cons a t hM =>
      obtain ⟨M, hMs, hM⟩ := hM
      by_cases hMa : f (g M) ≤ f (g a)
      · refine ⟨a, ?_, ?_⟩
        · simp only [Multiset.card_cons, Nat.succ_pos', Multiset.mem_cons_self, forall_true_left]
        · rw [Multiset.map_cons, Multiset.sum_cons]
          exact le_trans (hna _ _) (max_le (le_refl _) (le_trans hM hMa))
      · rw [not_le] at hMa
        by_cases ht : 0 < Multiset.card t
        · refine ⟨M, ?_, ?_⟩
          · simp only [Multiset.card_cons, Nat.succ_pos', Multiset.mem_cons, forall_true_left]
            exact Or.intro_right _ (hMs ht)
          rw [Multiset.map_cons, Multiset.sum_cons]
          exact le_trans (hna _ _) (max_le hMa.le hM)
        · refine ⟨a, ?_, ?_⟩
          · simp only [Multiset.card_cons, Nat.succ_pos', Multiset.mem_cons_self, forall_true_left]
          · have h0 : f (Multiset.map g t).sum = 0 := by
              simp only [not_lt, le_zero_iff, Multiset.card_eq_zero] at ht
              rw [ht, Multiset.map_zero, Multiset.sum_zero, map_zero f]
            rw [Multiset.map_cons, Multiset.sum_cons]
            apply le_trans (hna _ _)
            rw [h0]
            exact max_le (le_refl _) (apply_nonneg _ _)

/-- Given a nonarchimedean additive group seminorm `f` on `α`, a function `g : β → α` and a
  nonempty multiset `s : Multiset β`, we can always find `b : β` belonging to `s` such that
  `f (t.sum g) ≤ f (g b)` . -/
theorem multiset_image_add_of_nonempty {F α β : Type*} [AddCommGroup α] [FunLike F α ℝ]
    [AddGroupSeminormClass F α ℝ] [Nonempty β] {f : F} (hna : IsNonarchimedean f)
    (g : β → α) {s : Multiset β} (hs : 0 < Multiset.card s) :
    ∃ b : β, (b ∈ s) ∧ f (Multiset.map g s).sum ≤ f (g b) := by
  obtain ⟨b, hbs, hbf⟩ := multiset_image_add hna g s
  exact ⟨b, hbs hs, hbf⟩

/-- If `f` is a nonarchimedean additive group seminorm on a commutative ring `α`, `n : ℕ`, and
  `a b : α`, then we can find `m : ℕ` such that `m ≤ n` and
  `f ((a + b) ^ n) ≤ (f (a ^ m)) * (f (b ^ (n - m)))`. -/
theorem add_pow_le {F α : Type*} [CommRing α] [FunLike F α ℝ]
    [RingSeminormClass F α ℝ] {f : F} (hna : IsNonarchimedean f) (n : ℕ) (a b : α) :
    ∃ (m : ℕ) (_ : m ∈ List.range (n + 1)), f ((a + b) ^ n) ≤ f (a ^ m) * f (b ^ (n - m)) := by
  obtain ⟨m, hm_lt, hM⟩ := finset_image_add hna
    (fun m : ℕ => a ^ m * b ^ (n - m) * ↑(n.choose m)) (Finset.range (n + 1))
  simp only [Finset.nonempty_range_iff, ne_eq, Nat.succ_ne_zero, not_false_iff, Finset.mem_range,
    if_true, forall_true_left] at hm_lt
  refine ⟨m, List.mem_range.mpr hm_lt, ?_⟩
  simp only [← add_pow] at hM
  rw [mul_comm] at hM
  exact le_trans hM (le_trans (nmul_le hna) (map_mul_le_mul _ _ _))

end IsNonarchimedean
