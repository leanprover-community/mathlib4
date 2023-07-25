/-
Copyright (c) 2023 Kim Liesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Liesinger
-/
import Mathlib.Data.List.Infix
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.EditDistance.Defs

/-!
# Lower bounds for Levenshtein distances

We show that there is some suffix `L'` of `L` such
that the Levenshtein distance from `L'` to `M` gives a lower bound
for the Levenshtein distance from `L` to `m :: M`.

This allows us to use the intermediate steps of a Levenshtein distance calculation
to produce lower bounds on the final result.
-/

variable {C : Levenshtein.Cost α β δ} [CanonicallyLinearOrderedAddMonoid δ]

theorem suffixLevenshtein_minimum_le_levenshtein_cons (xs : List α) (y ys) :
    (suffixLevenshtein C xs ys).1.minimum ≤ levenshtein C xs (y :: ys) := by
  induction xs with
  | nil =>
      simp only [suffixLevenshtein_nil', levenshtein_nil_cons,
        List.minimum_singleton, WithTop.coe_le_coe]
      exact le_add_of_nonneg_left (by simp)
  | cons x xs ih =>
    simp only [levenshtein_cons_cons]
    simp only [ge_iff_le, le_min_iff, min_le_iff, WithTop.coe_min, WithTop.coe_le_coe]
    refine ⟨?_, ?_, ?_⟩
    · calc
        _ ≤ (suffixLevenshtein C xs ys).1.minimum := by
            simp [suffixLevenshtein_cons₁_fst, List.minimum_cons]
        _ ≤ ↑(levenshtein C xs (y :: ys)) := ih
        _ ≤ _ := by simp
    · calc
        (suffixLevenshtein C (x :: xs) ys).1.minimum ≤ ↑(levenshtein C (x :: xs) ys) := by
            simp [suffixLevenshtein_cons₁_fst, List.minimum_cons]
        _ ≤ _ := by simp
    · calc
        (suffixLevenshtein C (x :: xs) ys).1.minimum ≤ ↑(levenshtein C xs ys) := by
            simp only [suffixLevenshtein_cons₁_fst, List.minimum_cons]
            apply min_le_of_right_le
            cases xs
            · simp [suffixLevenshtein_nil']
            · simp [suffixLevenshtein_cons₁, List.minimum_cons]
        _ ≤ _ := by simp

theorem le_suffixLevenshtein_cons_minimum (xs : List α) (y ys) :
    (suffixLevenshtein C xs ys).1.minimum ≤ (suffixLevenshtein C xs (y :: ys)).1.minimum := by
  apply List.le_minimum_of_forall_le
  simp only [suffixLevenshtein_eq_tails_map]
  simp only [List.mem_map, List.mem_tails, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro a suff
  refine (?_ : _ ≤ _).trans (suffixLevenshtein_minimum_le_levenshtein_cons _ _ _)
  simp only [suffixLevenshtein_eq_tails_map]
  apply List.le_minimum_of_forall_le
  intro b m
  simp only [List.mem_map, List.mem_tails] at m
  obtain ⟨a', suff', rfl⟩ := m
  apply List.minimum_le_of_mem'
  simp only [List.mem_map, List.mem_tails]
  exact ⟨a', suff'.trans suff, rfl⟩

theorem le_suffixLevenshtein_append_minimum (xs : List α) (ys₁ ys₂) :
    (suffixLevenshtein C xs ys₂).1.minimum ≤ (suffixLevenshtein C xs (ys₁ ++ ys₂)).1.minimum := by
  induction ys₁ with
  | nil => exact le_refl _
  | cons y ys₁ ih => exact ih.trans (le_suffixLevenshtein_cons_minimum _ _ _)

theorem suffixLevenshtein_minimum_le_levenshtein_append (xs ys₁ ys₂) :
    (suffixLevenshtein C xs ys₂).1.minimum ≤ levenshtein C xs (ys₁ ++ ys₂) := by
  cases ys₁ with
  | nil => exact List.minimum_le_of_mem' (List.get_mem _ _ _)
  | cons y ys₁ =>
      exact (le_suffixLevenshtein_append_minimum _ _ _).trans
        (suffixLevenshtein_minimum_le_levenshtein_cons _ _ _)

theorem le_levenshtein_cons (xs : List α) (y ys) :
    ∃ xs', xs' <:+ xs ∧ levenshtein C xs' ys ≤ levenshtein C xs (y :: ys) := by
  simpa [suffixLevenshtein_eq_tails_map, List.minimum_le_coe_iff] using
    @suffixLevenshtein_minimum_le_levenshtein_cons _ _ δ _ _ xs y ys

theorem le_levenshtein_append (xs : List α) (ys₁ ys₂) :
    ∃ xs', xs' <:+ xs ∧ levenshtein C xs' ys₂ ≤ levenshtein C xs (ys₁ ++ ys₂) := by
  simpa [suffixLevenshtein_eq_tails_map, List.minimum_le_coe_iff] using
    @suffixLevenshtein_minimum_le_levenshtein_append _ _ δ _ _  xs ys₁ ys₂
