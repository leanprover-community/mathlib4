/-
Copyright (c) 2024 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import Mathlib.Analysis.Convex.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Doubly stochastic matrices

## Main definitions

* `doublyStochastic`: a square matrix is doubly stochastic if all entries are nonnegative, and left
  or right multiplication by the vector of all 1s gives the vector of all 1s. Equivalently, all
  row and column sums are equal to 1.

## Main statements

* `convex_doublyStochastic`: The set of doubly stochastic matrices is convex.
* `permMatrix_mem_doublyStochastic`: Any permutation matrix is doubly stochastic.

## TODO

Define the submonoids of row-stochastic and column-stochastic matrices.
Show that the submonoid of doubly stochastic matrices is the meet of them, or redefine it as such.

## Tags

Doubly stochastic, Birkhoff's theorem, Birkhoff-von Neumann theorem
-/

open Finset Function Matrix

variable {R n : Type*} [Fintype n] [DecidableEq n]

section OrderedSemiring
variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {M : Matrix n n R}

/--
A square matrix is doubly stochastic iff all entries are nonnegative, and left or right
multiplication by the vector of all 1s gives the vector of all 1s.
-/
def doublyStochastic (R n : Type*) [Fintype n] [DecidableEq n] [Semiring R] [PartialOrder R]
    [IsOrderedRing R] :
    Submonoid (Matrix n n R) where
  carrier := {M | (∀ i j, 0 ≤ M i j) ∧ M *ᵥ 1 = 1 ∧ 1 ᵥ* M = 1 }
  mul_mem' {M N} hM hN := by
    refine ⟨fun i j => sum_nonneg fun i _ => mul_nonneg (hM.1 _ _) (hN.1 _ _), ?_, ?_⟩
    next => rw [← mulVec_mulVec, hN.2.1, hM.2.1]
    next => rw [← vecMul_vecMul, hM.2.2, hN.2.2]
  one_mem' := by simp [zero_le_one_elem]

lemma mem_doublyStochastic :
    M ∈ doublyStochastic R n ↔ (∀ i j, 0 ≤ M i j) ∧ M *ᵥ 1 = 1 ∧ 1 ᵥ* M = 1 :=
  Iff.rfl

lemma mem_doublyStochastic_iff_sum :
    M ∈ doublyStochastic R n ↔
      (∀ i j, 0 ≤ M i j) ∧ (∀ i, ∑ j, M i j = 1) ∧ ∀ j, ∑ i, M i j = 1 := by
  simp [funext_iff, doublyStochastic, mulVec, vecMul, dotProduct]

/-- Every entry of a doubly stochastic matrix is nonnegative. -/
lemma nonneg_of_mem_doublyStochastic (hM : M ∈ doublyStochastic R n) {i j : n} : 0 ≤ M i j :=
  hM.1 _ _

/-- Each row sum of a doubly stochastic matrix is 1. -/
lemma sum_row_of_mem_doublyStochastic (hM : M ∈ doublyStochastic R n) (i : n) : ∑ j, M i j = 1 :=
  (mem_doublyStochastic_iff_sum.1 hM).2.1 _

/-- Each column sum of a doubly stochastic matrix is 1. -/
lemma sum_col_of_mem_doublyStochastic (hM : M ∈ doublyStochastic R n) (j : n) : ∑ i, M i j = 1 :=
  (mem_doublyStochastic_iff_sum.1 hM).2.2 _

/-- A doubly stochastic matrix multiplied with the all-ones column vector is 1. -/
lemma mulVec_one_of_mem_doublyStochastic (hM : M ∈ doublyStochastic R n) : M *ᵥ 1 = 1 :=
  (mem_doublyStochastic.1 hM).2.1

/-- The all-ones row vector multiplied with a doubly stochastic matrix is 1. -/
lemma one_vecMul_of_mem_doublyStochastic (hM : M ∈ doublyStochastic R n) : 1 ᵥ* M = 1 :=
  (mem_doublyStochastic.1 hM).2.2

/-- Every entry of a doubly stochastic matrix is less than or equal to 1. -/
lemma le_one_of_mem_doublyStochastic (hM : M ∈ doublyStochastic R n) {i j : n} :
    M i j ≤ 1 := by
  rw [← sum_row_of_mem_doublyStochastic hM i]
  exact single_le_sum (fun k _ => hM.1 _ k) (mem_univ j)

/-- The set of doubly stochastic matrices is convex. -/
lemma convex_doublyStochastic : Convex R (doublyStochastic R n : Set (Matrix n n R)) := by
  intro x hx y hy a b ha hb h
  simp only [SetLike.mem_coe, mem_doublyStochastic_iff_sum] at hx hy ⊢
  simp [add_nonneg, ha, hb, mul_nonneg, hx, hy, sum_add_distrib, ← mul_sum, h]

/-- Any permutation matrix is doubly stochastic. -/
lemma permMatrix_mem_doublyStochastic {σ : Equiv.Perm n} :
    σ.permMatrix R ∈ doublyStochastic R n := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => ?g1, ?g2, ?g3⟩
  case g1 => aesop
  case g2 => simp [Equiv.toPEquiv_apply]
  case g3 => simp [Equiv.toPEquiv_apply, ← Equiv.eq_symm_apply]

end OrderedSemiring

section LinearOrderedSemifield

variable [Semifield R] [LinearOrder R] [IsStrictOrderedRing R]

/--
A matrix is `s` times a doubly stochastic matrix iff all entries are nonnegative, and all row and
column sums are equal to `s`.

This lemma is useful for the proof of Birkhoff's theorem - in particular because it allows scaling
by nonnegative factors rather than positive ones only.
-/
lemma exists_mem_doublyStochastic_eq_smul_iff {M : Matrix n n R} {s : R} (hs : 0 ≤ s) :
    (∃ M' ∈ doublyStochastic R n, M = s • M') ↔
      (∀ i j, 0 ≤ M i j) ∧ (∀ i, ∑ j, M i j = s) ∧ (∀ j, ∑ i, M i j = s) := by
  classical
  constructor
  case mp =>
    rintro ⟨M', hM', rfl⟩
    rw [mem_doublyStochastic_iff_sum] at hM'
    simp only [smul_apply, smul_eq_mul, ← mul_sum]
    exact ⟨fun i j => mul_nonneg hs (hM'.1 _ _), by simp [hM']⟩
  rcases eq_or_lt_of_le hs with rfl | hs
  case inl =>
    simp only [zero_smul, exists_and_right, and_imp]
    intro h₁ h₂ _
    refine ⟨⟨1, Submonoid.one_mem _⟩, ?_⟩
    ext i j
    specialize h₂ i
    rw [sum_eq_zero_iff_of_nonneg (by simp [h₁ i])] at h₂
    exact h₂ _ (by simp)
  rintro ⟨hM₁, hM₂, hM₃⟩
  exact ⟨s⁻¹ • M, by simp [mem_doublyStochastic_iff_sum, ← mul_sum, hs.ne', *]⟩

end LinearOrderedSemifield
