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

namespace Matrix

variable {n : Type*}

private lemma abs_det_eq_prod_abs_inner_gramSchmidt_rows
    [Fintype n] [DecidableEq n] [LinearOrder n]
    [LocallyFiniteOrderBot n] [WellFoundedLT n] (A : Matrix n n ℝ) :
    |A.det| = ∏ i,
      |inner ℝ
        ((InnerProductSpace.gramSchmidtOrthonormalBasis finrank_euclideanSpace
          (fun i => WithLp.toLp 2 (A i) : n → EuclideanSpace ℝ n)) i)
        (WithLp.toLp 2 (A i) : EuclideanSpace ℝ n)| := by
  let v : n → EuclideanSpace ℝ n := fun i => WithLp.toLp 2 (A i)
  let b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n) :=
    InnerProductSpace.gramSchmidtOrthonormalBasis finrank_euclideanSpace v
  rw [show |A.det| = |b.toBasis.det v| by
    rw [show b.toBasis.det v = b.toBasis.det (EuclideanSpace.basisFun n ℝ) * A.det by
      nth_rewrite 1 [(b.toBasis.det).eq_smul_basis_det (EuclideanSpace.basisFun n ℝ).toBasis]
      simp [v, EuclideanSpace.basisFun_toBasis_det_toLp n ℝ A]]
    rcases OrthonormalBasis.det_to_matrix_orthonormalBasis_real b (EuclideanSpace.basisFun n ℝ)
      with h | h <;> simp [h],
    InnerProductSpace.gramSchmidtOrthonormalBasis_det, Finset.abs_prod]

private lemma euclidean_row_norm_sq_le_card
    [Fintype n] {A : Matrix n n ℝ}
    (hA : ∀ i j, |A i j| ≤ 1) (i : n) :
    ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℝ n)‖ ^ 2 ≤ (Fintype.card n : ℝ) := by
  simpa [EuclideanSpace.real_norm_sq_eq] using Finset.sum_le_card_nsmul Finset.univ
    (fun j => (A i j) ^ 2) 1 fun j _ => (sq_le_one_iff_abs_le_one (A i j)).2 (hA i j)

/-- Hadamard's maximal determinant inequality for real matrices with entries bounded by one:
`|A.det| ≤ √((Fintype.card n : ℝ) ^ Fintype.card n)`. -/
theorem abs_det_le_sqrt_card_pow_card_of_abs_apply_le_one
    [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : ∀ i j, |A i j| ≤ 1) :
    |A.det| ≤ √((Fintype.card n : ℝ) ^ Fintype.card n) := by
  classical
  let m := Fin (Fintype.card n)
  let e : n ≃ m := Fintype.equivFin n
  let B : Matrix m m ℝ := reindex e e A
  have hB : ∀ i j, |B i j| ≤ 1 := fun i j => by
    simpa [B, reindex_apply] using hA (e.symm i) (e.symm j)
  simpa [B, m] using Real.abs_le_sqrt (x := B.det)
    (y := (Fintype.card m : ℝ) ^ Fintype.card m) <| by
    let v : m → EuclideanSpace ℝ m := fun i => WithLp.toLp 2 (B i)
    calc
      B.det ^ 2 ≤ ∏ i, ‖v i‖ ^ 2 := by
        simpa [sq_abs, Finset.prod_pow] using
          (sq_le_sq₀ (abs_nonneg B.det) (by positivity)).2 <| by
          let b : OrthonormalBasis m ℝ (EuclideanSpace ℝ m) :=
            InnerProductSpace.gramSchmidtOrthonormalBasis finrank_euclideanSpace v
          rw [show |B.det| = ∏ i, |inner ℝ (b i) (v i)| by
            simpa [b, v] using abs_det_eq_prod_abs_inner_gramSchmidt_rows B]
          gcongr with i
          simpa [b.norm_eq_one] using abs_real_inner_le_norm (b i) (v i)
      _ ≤ ∏ _i : m, (Fintype.card m : ℝ) := by
        gcongr with i
        simpa [v] using euclidean_row_norm_sq_le_card hB i
      _ = (Fintype.card m : ℝ) ^ Fintype.card m := by simp

/-- Hadamard's maximal determinant inequality, squared form: `A.det ^ 2 ≤ n ^ n`. -/
theorem det_sq_le_card_pow_card_of_abs_apply_le_one
    [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : ∀ i j, |A i j| ≤ 1) :
    A.det ^ 2 ≤ (Fintype.card n : ℝ) ^ Fintype.card n := by
  simpa [sq_abs, Real.sq_sqrt (pow_nonneg (Nat.cast_nonneg _) _)] using
    (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).2
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
  classical
  let m := Fin (Fintype.card n)
  let e : n ≃ m := Fintype.equivFin n
  let B : Matrix m m ℝ := reindex e e A
  have hBbound : ∀ i j, |B i j| ≤ 1 := fun i j => by
    simpa [B, reindex_apply] using hbound (e.symm i) (e.symm j)
  suffices B.IsHadamard by simpa [B] using this
  by_cases hempty : IsEmpty m
  · letI := hempty
    refine ⟨isEmptyElim, ?_, ?_⟩ <;> ext i <;> exact isEmptyElim i
  haveI : Nonempty m := not_isEmpty_iff.mp hempty
  let v : m → EuclideanSpace ℝ m := fun i => WithLp.toLp 2 (B i)
  let N : ℝ := Fintype.card m
  let b : OrthonormalBasis m ℝ (EuclideanSpace ℝ m) :=
    InnerProductSpace.gramSchmidtOrthonormalBasis finrank_euclideanSpace v
  have habs_prod : |B.det| = ∏ i, |inner ℝ (b i) (v i)| := by
    simpa [b, v] using abs_det_eq_prod_abs_inner_gramSchmidt_rows B
  have hinner_le : ∀ i, |inner ℝ (b i) (v i)| ≤ ‖v i‖ := fun i => by
    simpa [b.norm_eq_one] using abs_real_inner_le_norm (b i) (v i)
  have hnorm_sq_le : ∀ i, ‖v i‖ ^ 2 ≤ N := fun i => by
    simpa [v, N] using euclidean_row_norm_sq_le_card hBbound i
  have hNpos : 0 < N := by
    simpa [N] using (by exact_mod_cast Fintype.card_pos (α := m) :
      0 < (Fintype.card m : ℝ))
  have hprod_inner_sq_eq : ∏ i, |inner ℝ (b i) (v i)| ^ 2 = N ^ Fintype.card m := by
    rw [Finset.prod_pow, ← habs_prod,
      show |B.det| = √((Fintype.card m : ℝ) ^ Fintype.card m) by simpa [B, m] using hdet,
      Real.sq_sqrt (pow_nonneg hNpos.le _)]
  have hinner_sq_le : ∀ i, |inner ℝ (b i) (v i)| ^ 2 ≤ N := fun i =>
    ((sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 (hinner_le i)).trans (hnorm_sq_le i)
  have hinner_sq_eq : ∀ i, |inner ℝ (b i) (v i)| ^ 2 = N := by
    intro i
    by_contra hne
    have hlt : ∏ i, |inner ℝ (b i) (v i)| ^ 2 < ∏ _i : m, N :=
      Finset.prod_lt_prod (s := Finset.univ) (fun i _ =>
        lt_of_le_of_ne (sq_nonneg _) <| (Finset.prod_ne_zero_iff.mp (by
          rw [hprod_inner_sq_eq]
          positivity) i (Finset.mem_univ i)).symm)
      (by simpa using hinner_sq_le)
      ⟨i, Finset.mem_univ i,
        lt_of_le_of_ne (hinner_sq_le i) hne⟩
    rw [hprod_inner_sq_eq] at hlt
    simp at hlt
  have hnorm_sq_eq : ∀ i, ‖v i‖ ^ 2 = N := fun i =>
    le_antisymm (hnorm_sq_le i) <| by
      rw [← hinner_sq_eq i]
      exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 (hinner_le i)
  refine IsHadamard.of_entry_sq_of_pairwise_rows ?_ ?_
  · intro i j
    exact (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
      (fun k _ => (sq_le_one_iff_abs_le_one (B i k)).2 (hBbound i k))).mp
        (by simpa [v, N, EuclideanSpace.real_norm_sq_eq] using hnorm_sq_eq i)
        j (Finset.mem_univ j)
  · intro i k hik
    simpa [v, PiLp.inner_apply, mul_comm] using
      (InnerProductSpace.gramSchmidtOrthonormalBasis_pairwise_inner_eq_zero_of_parallel
      finrank_euclideanSpace v (fun i => by
        refine Or.resolve_left (((norm_inner_eq_norm_tfae ℝ (b i) (v i)).out 0 2).1 ?_)
          (norm_pos_iff.1 (by rw [b.norm_eq_one]; norm_num))
        rw [Real.norm_eq_abs,
          (sq_eq_sq₀ (abs_nonneg _) (norm_nonneg _)).1 (by rw [hinner_sq_eq i, hnorm_sq_eq i]),
          b.norm_eq_one, one_mul])) hik

/-- Under the entry bound `|A i j| ≤ 1`, equality in Hadamard's maximal determinant inequality
holds if and only if `A` is a real Hadamard matrix. -/
theorem abs_det_eq_sqrt_card_pow_card_iff_isHadamard_of_abs_apply_le_one
    [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hbound : ∀ i j, |A i j| ≤ 1) :
    |A.det| = √((Fintype.card n : ℝ) ^ Fintype.card n) ↔ A.IsHadamard :=
  ⟨isHadamard_of_abs_det_eq_sqrt_card_pow_card_of_abs_apply_le_one hbound,
    IsHadamard.abs_det_eq_sqrt_card_pow_card⟩

end Matrix
