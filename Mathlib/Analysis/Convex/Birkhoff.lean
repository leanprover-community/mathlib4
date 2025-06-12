/-
Copyright (c) 2024 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Matrix.DoublyStochastic
import Mathlib.Tactic.Linarith

/-!
# Birkhoff's theorem

## Main statements

* `doublyStochastic_eq_sum_perm`: If `M` is a doubly stochastic matrix, then it is a convex
  combination of permutation matrices.
* `doublyStochastic_eq_convexHull_perm`: The set of doubly stochastic matrices is the convex hull
  of the permutation matrices.
* `extremePoints_doublyStochastic`: The set of extreme points of the doubly stochastic matrices is
  the set of permutation matrices.

## TODO

* Show that for `x y : n → R`, `x` is majorized by `y` if and only if there is a doubly stochastic
  matrix `M` such that `M *ᵥ y = x`.

## Tags

Doubly stochastic, Birkhoff's theorem, Birkhoff-von Neumann theorem
-/

open Finset Function Matrix

variable {R n : Type*} [Fintype n] [DecidableEq n]

section LinearOrderedSemifield

variable [Semifield R] [LinearOrder R] [IsStrictOrderedRing R] {M : Matrix n n R}

/--
If M is a positive scalar multiple of a doubly stochastic matrix, then there is a permutation matrix
whose support is contained in the support of M.
-/
private lemma exists_perm_eq_zero_implies_eq_zero [Nonempty n] {s : R} (hs : 0 < s)
    (hM : ∃ M' ∈ doublyStochastic R n, M = s • M') :
    ∃ σ : Equiv.Perm n, ∀ i j, M i j = 0 → σ.permMatrix R i j = 0 := by
  rw [exists_mem_doublyStochastic_eq_smul_iff hs.le] at hM
  let f (i : n) : Finset n := {j | M i j ≠ 0}
  have hf (A : Finset n) : #A ≤ #(A.biUnion f) := by
    have (i) : ∑ j ∈ f i, M i j = s := by simp [f, sum_subset (filter_subset _ _), hM.2.1]
    have h₁ : ∑ i ∈ A, ∑ j ∈ f i, M i j = #A * s := by simp [this]
    have h₂ : ∑ i, ∑ j ∈ A.biUnion f, M i j = #(A.biUnion f) * s := by
      simp [sum_comm (t := A.biUnion f), hM.2.2, mul_comm s]
    suffices #A * s ≤ #(A.biUnion f) * s by exact_mod_cast le_of_mul_le_mul_right this hs
    rw [← h₁, ← h₂]
    trans ∑ i ∈ A, ∑ j ∈ A.biUnion f, M i j
    · refine sum_le_sum fun i hi => ?_
      exact sum_le_sum_of_subset_of_nonneg (subset_biUnion_of_mem f hi) (by simp [*])
    · exact sum_le_sum_of_subset_of_nonneg (by simp) fun _ _ _ => sum_nonneg fun j _ => hM.1 _ _
  obtain ⟨g, hg, hg'⟩ := (all_card_le_biUnion_card_iff_exists_injective f).1 hf
  rw [Finite.injective_iff_bijective] at hg
  refine ⟨Equiv.ofBijective g hg, fun i j hij => ?_⟩
  simp only [PEquiv.toMatrix_apply, Option.mem_def, ite_eq_right_iff, one_ne_zero, imp_false,
    Equiv.toPEquiv_apply, Equiv.ofBijective_apply, Option.some.injEq]
  rintro rfl
  simpa [f, hij] using hg' i

end LinearOrderedSemifield

section LinearOrderedField

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] {M : Matrix n n R}

/--
If M is a scalar multiple of a doubly stochastic matrix, then it is a conical combination of
permutation matrices. This is most useful when M is a doubly stochastic matrix, in which case
the combination is convex.

This particular formulation is chosen to make the inductive step easier: we no longer need to
rescale each time a permutation matrix is subtracted.
-/
private lemma doublyStochastic_sum_perm_aux (M : Matrix n n R)
    (s : R) (hs : 0 ≤ s)
    (hM : ∃ M' ∈ doublyStochastic R n, M = s • M') :
    ∃ w : Equiv.Perm n → R, (∀ σ, 0 ≤ w σ) ∧ ∑ σ, w σ • σ.permMatrix R = M := by
  rcases isEmpty_or_nonempty n
  case inl => exact ⟨1, by simp, Subsingleton.elim _ _⟩
  set d : ℕ := #{i : n × n | M i.1 i.2 ≠ 0} with ← hd
  clear_value d
  induction d using Nat.strongRecOn generalizing M s
  case ind d ih =>
  rcases eq_or_lt_of_le hs with rfl | hs'
  case inl =>
    use 0
    simp only [zero_smul, exists_and_right] at hM
    simp [hM]
  obtain ⟨σ, hσ⟩ := exists_perm_eq_zero_implies_eq_zero hs' hM
  obtain ⟨i, hi, hi'⟩ := exists_min_image _ (fun i => M i (σ i)) univ_nonempty
  rw [exists_mem_doublyStochastic_eq_smul_iff hs] at hM
  let N : Matrix n n R := M - M i (σ i) • σ.permMatrix R
  have hMi' : 0 < M i (σ i) := (hM.1 _ _).lt_of_ne' fun h => by
    simpa [Equiv.toPEquiv_apply] using hσ _ _ h
  let s' : R := s - M i (σ i)
  have hs' : 0 ≤ s' := by
    simp only [s', sub_nonneg, ← hM.2.1 i]
    exact single_le_sum (fun j _ => hM.1 i j) (by simp)
  have : ∃ M' ∈ doublyStochastic R n, N = s' • M' := by
    rw [exists_mem_doublyStochastic_eq_smul_iff hs']
    simp only [sub_apply, smul_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
      Option.some.injEq, smul_eq_mul, mul_ite, mul_one, mul_zero, sub_nonneg,
      sum_sub_distrib, sum_ite_eq, mem_univ, ↓reduceIte, N]
    refine ⟨fun i' j => ?_, by simp [s', hM.2.1], by simp [s', ← σ.eq_symm_apply, hM]⟩
    split
    case isTrue h => exact (hi' i' (by simp)).trans_eq (by rw [h])
    case isFalse h => exact hM.1 _ _
  have hd' : #{i : n × n | N i.1 i.2 ≠ 0} < d := by
    rw [← hd]
    refine card_lt_card ?_
    rw [ssubset_iff_of_subset (monotone_filter_right _ _)]
    · simp only [ne_eq, mem_filter, mem_univ, true_and, Decidable.not_not, Prod.exists]
      refine ⟨i, σ i, hMi'.ne', ?_⟩
      simp [N, Equiv.toPEquiv_apply]
    · rintro ⟨i', j'⟩ hN' hM'
      dsimp at hN' hM'
      simp only [sub_apply, hM', smul_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
        Option.mem_def, Option.some.injEq, smul_eq_mul, mul_ite, mul_one, mul_zero, zero_sub,
        neg_eq_zero, ite_eq_right_iff, Classical.not_imp, N] at hN'
      obtain ⟨rfl, _⟩ := hN'
      linarith [hi' i' (by simp)]
  obtain ⟨w, hw, hw'⟩ := ih _ hd' _ s' hs' this rfl
  refine ⟨w + fun σ' => if σ' = σ then M i (σ i) else 0, ?_⟩
  simp only [Pi.add_apply, add_smul, sum_add_distrib, hw', ite_smul, zero_smul,
    sum_ite_eq', mem_univ, ↓reduceIte, N, sub_add_cancel, and_true]
  intro σ'
  split <;> simp [add_nonneg, hw, hM.1]

/--
If M is a doubly stochastic matrix, then it is an convex combination of permutation matrices. Note
`doublyStochastic_eq_convexHull_permMatrix` shows `doublyStochastic n` is exactly the convex hull of
the permutation matrices, and this lemma is instead most useful for accessing the coefficients of
each permutation matrices directly.
-/
lemma exists_eq_sum_perm_of_mem_doublyStochastic (hM : M ∈ doublyStochastic R n) :
    ∃ w : Equiv.Perm n → R, (∀ σ, 0 ≤ w σ) ∧ ∑ σ, w σ = 1 ∧ ∑ σ, w σ • σ.permMatrix R = M := by
  rcases isEmpty_or_nonempty n
  case inl => exact ⟨fun _ => 1, by simp, by simp, Subsingleton.elim _ _⟩
  obtain ⟨w, hw1, hw3⟩ := doublyStochastic_sum_perm_aux M 1 (by simp) ⟨M, hM, by simp⟩
  refine ⟨w, hw1, ?_, hw3⟩
  inhabit n
  have : ∑ j, ∑ σ : Equiv.Perm n, w σ • σ.permMatrix R default j = 1 := by
    simp only [← smul_apply (m := n), ← Finset.sum_apply, hw3]
    rw [sum_row_of_mem_doublyStochastic hM]
  simpa [sum_comm (γ := n), Equiv.toPEquiv_apply] using this

/--
**Birkhoff's theorem**
The set of doubly stochastic matrices is the convex hull of the permutation matrices.  Note
`exists_eq_sum_perm_of_mem_doublyStochastic` gives a convex weighting of each permutation matrix
directly.  To show `doublyStochastic n` is convex, use `convex_doublyStochastic`.
-/
theorem doublyStochastic_eq_convexHull_permMatrix :
    doublyStochastic R n = convexHull R {σ.permMatrix R | σ : Equiv.Perm n} := by
  refine (convexHull_min ?g1 convex_doublyStochastic).antisymm' fun M hM => ?g2
  case g1 =>
    rintro x ⟨h, rfl⟩
    exact permMatrix_mem_doublyStochastic
  case g2 =>
    obtain ⟨w, hw1, hw2, hw3⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hM
    exact mem_convexHull_of_exists_fintype w (·.permMatrix R) hw1 hw2 (by simp) hw3

/--
The set of extreme points of the doubly stochastic matrices is the set of permutation matrices.
-/
theorem extremePoints_doublyStochastic :
    Set.extremePoints R (doublyStochastic R n) = {σ.permMatrix R | σ : Equiv.Perm n} := by
  refine subset_antisymm ?_ ?_
  · rw [doublyStochastic_eq_convexHull_permMatrix]
    exact extremePoints_convexHull_subset
  rintro _ ⟨σ, rfl⟩
  refine ⟨permMatrix_mem_doublyStochastic, fun x₁ hx₁ x₂ hx₂ hσ ↦ ?_⟩
  suffices ∀ i j : n, x₁ i j = x₂ i j by
    obtain rfl : x₁ = x₂ := by simpa [← Matrix.ext_iff]
    simp_all
  intro i j
  have h₁ : σ.permMatrix R i j ∈ openSegment R (x₁ i j) (x₂ i j) :=
    image_openSegment _ (entryLinearMap R R i j).toAffineMap x₁ x₂ ▸ ⟨_, hσ, rfl⟩
  by_contra! h
  have h₂ : openSegment R (x₁ i j) (x₂ i j) ⊆ Set.Ioo 0 1 := by
    rw [openSegment_eq_Ioo' h]
    apply Set.Ioo_subset_Ioo <;>
    simp_all [nonneg_of_mem_doublyStochastic, le_one_of_mem_doublyStochastic]
  specialize h₂ h₁
  aesop

end LinearOrderedField
