/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix

/-!
# Hadamard's maximal determinant inequality

This file proves Hadamard's determinant bound for real matrices with entries bounded by one in
absolute value. It also characterizes equality in terms of `Matrix.IsHadamard`.

## Main results

* `Matrix.abs_det_le_sqrt_card_pow_card_of_abs_apply_le_one`: if `|A i j| ≤ 1`, then
  `|A.det| ≤ √ ((Fintype.card n : ℝ) ^ Fintype.card n)`.
* `Matrix.abs_det_eq_sqrt_card_pow_card_iff_isHadamard_of_abs_apply_le_one`: under the same
  entry bound, equality holds iff `A.IsHadamard`.
-/

@[expose] public section

open InnerProductSpace

namespace Matrix

variable {n : Type*}

private lemma abs_det_eq_prod_abs_inner_gramSchmidt_rows
    [Fintype n] [DecidableEq n] [LinearOrder n]
    [LocallyFiniteOrderBot n] [WellFoundedLT n] (A : Matrix n n ℝ) :
    letI v : n → EuclideanSpace ℝ n := fun i ↦ WithLp.toLp 2 (A i)
    |A.det| = ∏ i, |⟪gramSchmidtOrthonormalBasis finrank_euclideanSpace v i, v i⟫_ℝ| := by
  set v : n → EuclideanSpace ℝ n := fun i ↦ WithLp.toLp 2 (A i)
  set b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n) :=
    gramSchmidtOrthonormalBasis finrank_euclideanSpace v
  calc
    |A.det| = |b.toBasis.det (EuclideanSpace.basisFun n ℝ) * A.det| := by
      obtain (h | h) := b.det_to_matrix_orthonormalBasis_real (EuclideanSpace.basisFun n ℝ)
      all_goals simp [h]
    _ = |b.toBasis.det v| := by
      nth_rewrite 2 [(b.toBasis.det).eq_smul_basis_det (EuclideanSpace.basisFun n ℝ).toBasis]
      simp [v, EuclideanSpace.basisFun_toBasis_det_toLp]
    _ = ∏ i, |⟪b i, v i⟫_ℝ| := by
      rw [gramSchmidtOrthonormalBasis_det, Finset.abs_prod]

private lemma euclidean_row_norm_sq_le_card
    [Fintype n] {A : Matrix n n ℝ}
    (hA : ∀ i j, |A i j| ≤ 1) (i : n) :
    ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℝ n)‖ ^ 2 ≤ (Fintype.card n : ℝ) := by
  simpa [EuclideanSpace.real_norm_sq_eq] using Finset.univ.sum_le_card_nsmul
    _ 1 fun j _ => (sq_le_one_iff_abs_le_one (A i j)).2 (hA i j)

/-- Hadamard's maximal determinant inequality for real matrices with entries bounded by one:
`|A.det| ≤ √((Fintype.card n : ℝ) ^ Fintype.card n)`. -/
theorem abs_det_le_sqrt_card_pow_card_of_abs_apply_le_one
    [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : ∀ i j, |A i j| ≤ 1) :
    |A.det| ≤ √((Fintype.card n : ℝ) ^ Fintype.card n) := by
  let m := Fin (Fintype.card n)
  let e : n ≃ m := Fintype.equivFin n
  let B : Matrix m m ℝ := reindex e e A
  have hB : ∀ i j, |B i j| ≤ 1 := fun i j => by
    simpa [B, reindex_apply] using hA (e.symm i) (e.symm j)
  let v : m → EuclideanSpace ℝ m := fun i => WithLp.toLp 2 (B i)
  let b : OrthonormalBasis m ℝ (EuclideanSpace ℝ m) :=
    gramSchmidtOrthonormalBasis finrank_euclideanSpace v
  have hdet : |B.det| = ∏ i, |⟪b i, v i⟫_ℝ| := by
    simpa [b, v] using abs_det_eq_prod_abs_inner_gramSchmidt_rows B
  have hrow : ∀ i, |⟪b i, v i⟫_ℝ| ^ 2 ≤ (Fintype.card m : ℝ) := fun i =>
    ((sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2
      (by simpa [b.norm_eq_one] using abs_real_inner_le_norm (b i) (v i))).trans
      (by simpa [v] using euclidean_row_norm_sq_le_card hB i)
  have key : B.det ^ 2 ≤ (Fintype.card m : ℝ) ^ Fintype.card m :=
    calc
      B.det ^ 2 = ∏ i, |⟪b i, v i⟫_ℝ| ^ 2 := by rw [← sq_abs, hdet, Finset.prod_pow]
      _ ≤ ∏ _i : m, (Fintype.card m : ℝ) := by gcongr with i; exact hrow i
      _ = (Fintype.card m : ℝ) ^ Fintype.card m := by simp
  simpa [B, m] using Real.abs_le_sqrt key

/-- Hadamard's maximal determinant inequality, squared form: `A.det ^ 2 ≤ n ^ n`. -/
theorem det_sq_le_card_pow_card_of_abs_apply_le_one
    [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : ∀ i j, |A i j| ≤ 1) :
    A.det ^ 2 ≤ (Fintype.card n : ℝ) ^ Fintype.card n := by
  simpa [sq_abs] using (Real.le_sqrt (abs_nonneg _) (by positivity)).1
    (abs_det_le_sqrt_card_pow_card_of_abs_apply_le_one hA)

/-- The absolute value of the determinant of a real Hadamard matrix is the Hadamard bound. -/
theorem IsHadamard.abs_det_eq_sqrt_card_pow_card
    [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.IsHadamard) :
    |A.det| = √((Fintype.card n : ℝ) ^ Fintype.card n) := by
  rw [← hA.det_mul_star_det]
  simp [Real.sqrt_mul_self_eq_abs]

/-- Equality in Hadamard's maximal determinant inequality characterizes real Hadamard matrices. -/
theorem isHadamard_of_abs_det_eq_sqrt_card_pow_card_of_abs_apply_le_one
    [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hbound : ∀ i j, |A i j| ≤ 1)
    (hdet : |A.det| = √((Fintype.card n : ℝ) ^ Fintype.card n)) :
    A.IsHadamard := by
  let m := Fin (Fintype.card n)
  let e : n ≃ m := Fintype.equivFin n
  let B : Matrix m m ℝ := reindex e e A
  have hBbound : ∀ i j, |B i j| ≤ 1 := fun i j => by
    simpa [B, reindex_apply] using hbound (e.symm i) (e.symm j)
  suffices B.IsHadamard by simpa [B] using this
  obtain _ | _ := isEmpty_or_nonempty m
  · refine ⟨isEmptyElim, ?_, ?_⟩ <;> ext i <;> exact isEmptyElim i
  let v : m → EuclideanSpace ℝ m := fun i => WithLp.toLp 2 (B i)
  let N : ℝ := Fintype.card m
  let b : OrthonormalBasis m ℝ (EuclideanSpace ℝ m) :=
    gramSchmidtOrthonormalBasis finrank_euclideanSpace v
  -- Equality forces every row of `B` to have squared norm exactly `N` and to be parallel to the
  -- corresponding Gram-Schmidt vector.
  have key : ∀ i, |⟪b i, v i⟫_ℝ| = ‖v i‖ ∧ ‖v i‖ ^ 2 = N := by
    have hinner_le : ∀ i, |⟪b i, v i⟫_ℝ| ≤ ‖v i‖ := fun i => by
      simpa [b.norm_eq_one] using abs_real_inner_le_norm (b i) (v i)
    have hnorm_sq_le : ∀ i, ‖v i‖ ^ 2 ≤ N := fun i => by
      simpa [v, N] using euclidean_row_norm_sq_le_card hBbound i
    have hinner_sq_le : ∀ i, |⟪b i, v i⟫_ℝ| ^ 2 ≤ N := fun i =>
      ((sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 (hinner_le i)).trans (hnorm_sq_le i)
    have hNpos : 0 < N := by simp [N, Fintype.card_pos]
    have hprod : ∏ i, |⟪b i, v i⟫_ℝ| ^ 2 = N ^ Fintype.card m := by
      have habs : |B.det| = ∏ i, |⟪b i, v i⟫_ℝ| := by
        simpa [b, v] using abs_det_eq_prod_abs_inner_gramSchmidt_rows B
      have hdetB : |B.det| = √(N ^ Fintype.card m) := by simpa [B, m, N] using hdet
      rw [Finset.prod_pow, ← habs, hdetB, Real.sq_sqrt (by positivity)]
    have hinner_sq_eq : ∀ i, |⟪b i, v i⟫_ℝ| ^ 2 = N := fun i =>
      (hinner_sq_le i).eq_of_not_lt fun hlt => by
        have := Finset.prod_lt_prod (fun j _ => (sq_nonneg _).lt_of_ne' <|
          Finset.prod_ne_zero_iff.mp (hprod ▸ pow_ne_zero _ hNpos.ne') j (Finset.mem_univ j))
          (fun j _ => hinner_sq_le j) ⟨i, Finset.mem_univ i, hlt⟩
        rw [hprod] at this
        simp at this
    intro i
    have h : ‖v i‖ ^ 2 = N := (hnorm_sq_le i).antisymm <| hinner_sq_eq i ▸
      (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 (hinner_le i)
    exact ⟨(sq_eq_sq₀ (abs_nonneg _) (norm_nonneg _)).1 (by rw [hinner_sq_eq i, h]), h⟩
  refine IsHadamard.of_entry_sq_of_pairwise_rows (fun i j => ?_) (fun i k hik => ?_)
  · exact (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
      (fun k _ => (sq_le_one_iff_abs_le_one (B i k)).2 (hBbound i k))).mp
        (by simpa [v, N, EuclideanSpace.real_norm_sq_eq] using (key i).2) j (Finset.mem_univ j)
  · simpa [v, PiLp.inner_apply, dotProduct, mul_comm] using
      gramSchmidtOrthonormalBasis_pairwise_inner_eq_zero_of_parallel finrank_euclideanSpace v
        (fun i => Or.resolve_left (((norm_inner_eq_norm_tfae ℝ (b i) (v i)).out 0 2).1
          (by rw [Real.norm_eq_abs, (key i).1, b.norm_eq_one, one_mul]))
          (norm_pos_iff.1 (by rw [b.norm_eq_one]; norm_num))) hik

/-- Under the entry bound `|A i j| ≤ 1`, equality in Hadamard's maximal determinant inequality
holds if and only if `A` is a real Hadamard matrix. -/
theorem abs_det_eq_sqrt_card_pow_card_iff_isHadamard_of_abs_apply_le_one
    [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hbound : ∀ i j, |A i j| ≤ 1) :
    |A.det| = √((Fintype.card n : ℝ) ^ Fintype.card n) ↔ A.IsHadamard :=
  ⟨isHadamard_of_abs_det_eq_sqrt_card_pow_card_of_abs_apply_le_one hbound,
    IsHadamard.abs_det_eq_sqrt_card_pow_card⟩

end Matrix
