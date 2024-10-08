/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.Algebra.Module.Defs
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

/-!
# Nonarchimedean functions

A function `f : R → ℝ≥0` is nonarchimedean if it satisfies the strong triangle inequality
`f (r + s) ≤ max (f r) (f s)` for all `r s : R`. This file proves basic properties of
nonarchimedean functions.
-/

namespace IsNonarchimedean

/-- A nonarchimedean function satisfies the triangle inequality. -/
theorem add_le {α : Type*} [Add α] {f : α → ℝ} (hf : ∀ x : α, 0 ≤ f x)
    (hna : IsNonarchimedean f) {a b : α} : f (a + b) ≤ f a + f b := by
  apply le_trans (hna _ _)
  rw [max_le_iff, le_add_iff_nonneg_right, le_add_iff_nonneg_left]
  exact ⟨hf _, hf _⟩

/-- If `f` is a nonarchimedean additive group seminorm on `α`, then for every `n : ℕ` and `a : α`,
  we have `f (n • a) ≤ (f a)`. -/
theorem nsmul_le {F α : Type*} [AddCommGroup α] [FunLike F α ℝ]
    [AddGroupSeminormClass F α ℝ] {f : F} (hna : IsNonarchimedean f) {n : ℕ} {a : α} :
    f (n • a) ≤ f a := by
  induction n with
  | zero => rw [zero_nsmul, map_zero _]; exact apply_nonneg _ _
  | succ n hn =>
    rw [add_smul, one_smul]
    exact le_trans (hna _ _) (max_le hn (le_refl _))

/-- If `f` is a nonarchimedean additive group seminorm on `α`, then for every `n : ℕ` and `a : α`,
  we have `f (n * a) ≤ (f a)`. -/
theorem nmul_le {F α : Type*} [Ring α] [FunLike F α ℝ] [AddGroupSeminormClass F α ℝ]
    {f : F} (hna : IsNonarchimedean f) {n : ℕ} {a : α} : f (n * a) ≤ f a := by
  rw [← nsmul_eq_mul]
  exact nsmul_le hna

/-- If `f` is a nonarchimedean additive group seminorm on `α` and `x y : α` are such that
  `f y ≠ f x`, then `f (x + y) = max (f x) (f y)`. -/
theorem add_eq_max_of_ne {F α : Type*} [Ring α] [FunLike F α ℝ]
    [AddGroupSeminormClass F α ℝ] {f : F} (hna : IsNonarchimedean f) {x y : α} (hne : f y ≠ f x) :
    f (x + y) = max (f x) (f y) := by
  wlog hle : f y ≤ f x generalizing y x with H
  · rw [add_comm, max_comm]
    exact H hne.symm (le_of_not_le hle)
  · have hlt : f y < f x := lt_of_le_of_ne hle hne
    have : f x ≤ max (f (x + y)) (f y) :=
      calc f x = f (x + y + -y) := by rw [add_neg_cancel_right]
        _ ≤ max (f (x + y)) (f (-y)) := (hna _ _)
        _ = max (f (x + y)) (f y) := by rw [map_neg_eq_map f y]
    have hnge : f y ≤ f (x + y) := by
      apply le_of_not_gt
      intro hgt
      rw [max_eq_right_of_lt hgt] at this
      exact not_lt_of_ge this hlt
    have : f x ≤ f (x + y) := by rwa [max_eq_left hnge] at this
    exact le_antisymm (hna _ _) (by rwa [max_eq_left_of_lt hlt])

/-- Given a nonarchimedean additive group seminorm `f` on `α`, a function `g : β → α` and a finset
  `t : Finset β`, we can always find `b : β`, belonging to `t` if `t` is nonempty, such that
  `f (t.sum g) ≤ f (g b)` . -/
theorem finset_image_add {F α : Type*} [Ring α] [FunLike F α ℝ]
    [AddGroupSeminormClass F α ℝ] {f : F} (hna : IsNonarchimedean f) {β : Type*} [hβ : Nonempty β]
    (g : β → α) (t : Finset β) :
    ∃ b : β, (t.Nonempty → b ∈ t) ∧ f (t.sum g) ≤ f (g b) := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨hβ.some, by simp only [Finset.not_nonempty_empty, IsEmpty.forall_iff],
      (map_zero f) ▸ apply_nonneg f _⟩
  | @insert a s has hM =>
      obtain ⟨M, hMs, hM⟩ := hM
      rw [Finset.sum_insert has]
      by_cases hMa : f (g M) ≤ f (g a)
      · refine ⟨a, ?_, le_trans (hna _ _) (max_le (le_refl _) (le_trans hM hMa))⟩
        simp only [Finset.nonempty_coe_sort, Finset.insert_nonempty, Finset.mem_insert,
          eq_self_iff_true, true_or, forall_true_left]
      · rw [not_le] at hMa
        by_cases hs : s.Nonempty
        · refine ⟨M, ?_, le_trans (hna _ _) (max_le hMa.le hM)⟩
          simp only [Finset.nonempty_coe_sort, Finset.insert_nonempty, Finset.mem_insert,
            forall_true_left]
          exact Or.intro_right _ (hMs hs)
        · use a, (fun _ ↦  Finset.mem_insert_self a s)
          have h0 : f (s.sum g) = 0 := by
            rw [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.sum_empty, map_zero]
          apply le_trans (hna _ _)
          rw [h0]
          exact max_le (le_refl _) (apply_nonneg _ _)

/-- Given a nonarchimedean additive group seminorm `f` on `α`, a function `g : β → α` and a
  nonempty finset `t : Finset β`, we can always find `b : β` belonging to `t` such that
  `f (t.sum g) ≤ f (g b)` . -/
theorem finset_image_add_of_nonempty {F α : Type*} [Ring α] [FunLike F α ℝ]
    [AddGroupSeminormClass F α ℝ] {f : F} (hna : IsNonarchimedean f) {β : Type*} [hβ : Nonempty β]
    (g : β → α) {t : Finset β} (ht : t.Nonempty) :
    ∃ b : β, (b ∈ t) ∧ f (t.sum g) ≤ f (g b) := by
  obtain ⟨b, hbt, hbf⟩ := finset_image_add hna g t
  exact ⟨b, hbt ht, hbf⟩

/-- Given a nonarchimedean additive group seminorm `f` on `α`, a function `g : β → α` and a
  multiset `s : Multiset β`, we can always find `b : β`, belonging to `s` if `s` is nonempty,
  such that `f (t.sum g) ≤ f (g b)` . -/
theorem multiset_image_add {F α : Type*} [Ring α] [FunLike F α ℝ]
    [AddGroupSeminormClass F α ℝ] {f : F} (hna : IsNonarchimedean f) {β : Type*} [hβ : Nonempty β]
    (g : β → α) (s : Multiset β) :
    ∃ b : β, (0 < Multiset.card s → b ∈ s) ∧ f (Multiset.map g s).sum ≤ f (g b) := by
  induction s using Multiset.induction_on with
  | empty =>
      rw [Multiset.map_zero, Multiset.sum_zero, Multiset.card_zero, map_zero f]
      exact ⟨hβ.some, by simp only [not_lt_zero', IsEmpty.forall_iff], apply_nonneg _ _⟩
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
theorem multiset_image_add_of_nonempty {F α : Type*} [Ring α] [FunLike F α ℝ]
    [AddGroupSeminormClass F α ℝ] {f : F} (hna : IsNonarchimedean f) {β : Type*} [hβ : Nonempty β]
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
