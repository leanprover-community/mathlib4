/-
Copyright (c) 2026 Gravitomagnetic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: gravitomagnetic
-/
module

public import Mathlib.LinearAlgebra.Matrix.Stochastic
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.Analysis.Convex.DoublyStochasticMatrix
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Unistochastic and orthostochastic matrices

A *unistochastic* matrix is a real stochastic matrix whose entries are the
modulus-squares of the entries of a unitary matrix. These were introduced by
Horn (1954) under the name *ortho-stochastic*; the modern terminology is due
to Thompson (1989). Every unistochastic matrix is doubly stochastic; for
`2 × 2` matrices the converse holds. Unistochastic matrices are the bridge
between unitary dynamics and classical probability: the transition matrices
in the stochastic-quantum correspondence (Barandes, 2023) are unistochastic.

## Main definitions

* `Matrix.IsUnistochastic`: `A` is entrywise the modulus-square of a unitary
  matrix.
* `Matrix.IsOrthostochastic`: the real-orthogonal special case.

## Main results

* `Matrix.IsOrthostochastic.isUnistochastic`: orthostochastic matrices are
  unistochastic.
* `Matrix.IsUnistochastic.doublyStochastic`: unistochastic matrices are
  doubly stochastic.
* `Matrix.isUnistochastic_of_doublyStochastic`: for `2 × 2` real matrices
  the converse of the previous result holds, constructively via a rotation.
* `Matrix.eq_permMatrix_of_rowStochastic_mul`: if two row-stochastic matrices
  multiply to the identity, the first is a permutation matrix.

## References

* A. Horn, *Doubly stochastic matrices and the normal field of values*,
  Duke Math. J. 21 (1954)
* G. Thompson, *Orthostochastic matrices and the normal field of values*,
  Linear Multilinear Algebra 26 (1989)
* J. A. Barandes, *The Stochastic-Quantum Theorem* (2023), arXiv:2302.13109

## Tags

unistochastic, orthostochastic, doubly stochastic, stochastic matrix,
permutation matrix, unitary, quantum
-/

@[expose] public section

namespace Matrix

open Finset Complex
open scoped ComplexConjugate

/-- A real square matrix is **unistochastic** if its entries are the
modulus-squares of the entries of some unitary complex matrix. -/
def IsUnistochastic {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) : Prop :=
  ∃ U : Matrix n n ℂ, U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1 ∧
    ∀ i j, A i j = ‖U i j‖ ^ 2

/-- A real square matrix is **orthostochastic** if its entries are the squares
of the entries of some real orthogonal matrix (the real case of
`IsUnistochastic`). -/
def IsOrthostochastic {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) : Prop :=
  ∃ O : Matrix n n ℝ, O.transpose * O = 1 ∧ O * O.transpose = 1 ∧
    ∀ i j, A i j = (O i j) ^ 2

/-- Orthostochastic matrices are unistochastic: a real orthogonal matrix is
in particular unitary. -/
theorem IsOrthostochastic.isUnistochastic {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : IsOrthostochastic A) : IsUnistochastic A := by
  obtain ⟨O, hO1, hO2, hA'⟩ := hA
  refine ⟨O.map Complex.ofReal, ?_, ?_, ?_⟩
  · ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply,
      RCLike.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
    have hsum : (∑ x : n, O x i * O x j) = (Oᵀ * O) i j := by
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl (fun x _ =>
        congrArg (fun t => t * O x j) (Matrix.transpose_apply O i x).symm)
    rw [hsum, hO1, Matrix.one_apply]
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  · ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply,
      RCLike.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
    have hsum : (∑ x : n, O i x * O j x) = (O * Oᵀ) i j := by
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl (fun x _ =>
        congrArg (fun t => O i x * t) (Matrix.transpose_apply O x j).symm)
    rw [hsum, hO2, Matrix.one_apply]
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  · intro i j
    rw [hA' i j, Matrix.map_apply]
    rw [show (‖(O i j : ℂ)‖) = |O i j| from RCLike.norm_ofReal (K := ℂ) (O i j), sq_abs]

/-- Unistochastic matrices are doubly stochastic. -/
theorem IsUnistochastic.doublyStochastic {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : IsUnistochastic A) : A ∈ doublyStochastic ℝ n := by
  obtain ⟨U, hU1, hU2, hA'⟩ := hA
  rw [mem_doublyStochastic]
  refine ⟨fun i j => by rw [hA' i j]; positivity, ?_, ?_⟩
  · ext i
    have hc : (∑ j : n, (U i j * conj (U i j) : ℂ)) = 1 := by
      calc (∑ j : n, (U i j * conj (U i j) : ℂ))
          = ∑ j : n, U i j * Uᴴ j i := by
              refine Finset.sum_congr rfl (fun j _ => ?_)
              exact congrArg (U i j * ·) (conjTranspose_apply U i j).symm
        _ = (U * Uᴴ) i i := by rw [← mul_apply]
        _ = 1 := by rw [hU2]; simp
    have hsum0 : (A *ᵥ 1) i = ∑ j : n, A i j := by
      simp only [mulVec_apply, dotProduct, Matrix.row_apply, Pi.one_apply, mul_one]
    rw [hsum0, Pi.one_apply]
    apply Complex.ofReal_injective
    have hconv : (∑ j : n, (A i j : ℂ)) = ∑ j : n, (U i j * conj (U i j) : ℂ) :=
      Finset.sum_congr rfl (fun j _ => by simp [hA' i j, RCLike.mul_conj])
    rw [Complex.ofReal_sum, hconv, hc]; rfl
  · ext j
    have hc : (∑ i : n, (conj (U i j) * U i j : ℂ)) = 1 := by
      calc (∑ i : n, (conj (U i j) * U i j : ℂ))
          = ∑ i : n, Uᴴ j i * U i j := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              exact congrArg (· * U i j) (conjTranspose_apply U i j).symm
        _ = (Uᴴ * U) j j := by rw [← mul_apply]
        _ = 1 := by rw [hU1]; simp
    have hsum0 : (1 ᵥ* A) j = ∑ i : n, A i j := by
      simp only [vecMul_apply, dotProduct, Matrix.col_apply, Pi.one_apply, one_mul]
    rw [hsum0, Pi.one_apply]
    apply Complex.ofReal_injective
    have hconv : (∑ i : n, (A i j : ℂ)) = ∑ i : n, (conj (U i j) * U i j : ℂ) :=
      Finset.sum_congr rfl (fun i _ => by simp [hA' i j, RCLike.conj_mul])
    rw [Complex.ofReal_sum, hconv, hc]; rfl

/-- Every `2 × 2` doubly stochastic matrix is unistochastic, constructively:
the rotation matrix with angle `arccos √(A 0 0)`. -/
theorem isUnistochastic_of_doublyStochastic
    (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A ∈ doublyStochastic ℝ (Fin 2)) :
    IsUnistochastic A := by
  obtain ⟨hnonneg, hrow, hcol⟩ := mem_doublyStochastic.mp hA
  have a1 : A 0 0 + A 0 1 = 1 := by
    have t := congrFun hrow 0
    simpa [mulVec_apply, dotProduct, Matrix.row_apply, Pi.one_apply, mul_one] using t
  have a2 : A 0 0 + A 1 0 = 1 := by
    have t := congrFun hcol 0
    simpa [vecMul_apply, dotProduct, Matrix.col_apply, Pi.one_apply, one_mul] using t
  have a3 : A 1 0 + A 1 1 = 1 := by
    have t := congrFun hrow 1
    simpa [mulVec_apply, dotProduct, Matrix.row_apply, Pi.one_apply, mul_one] using t
  have h00 : 0 ≤ A 0 0 := hnonneg 0 0
  have ha1 : A 0 0 ≤ 1 := by linarith [a1, hnonneg 0 1]
  have hb : A 1 0 = A 0 1 := by linarith
  have h11 : A 1 1 = A 0 0 := by linarith
  set θ := Real.arccos (Real.sqrt (A 0 0))
  have hcos : Real.cos θ = Real.sqrt (A 0 0) :=
    Real.cos_arccos (by linarith [Real.sqrt_nonneg (A 0 0)]) (Real.sqrt_le_one.mpr ha1)
  have hsin : Real.sin θ = Real.sqrt (1 - A 0 0) := by
    dsimp only [θ]
    rw [Real.sin_arccos, Real.sq_sqrt (by linarith)]
  have s1 : (Real.sqrt (A 0 0)) ^ 2 = A 0 0 := Real.sq_sqrt (by linarith)
  have s2 : (Real.sqrt (1 - A 0 0)) ^ 2 = 1 - A 0 0 := Real.sq_sqrt (by linarith)
  set O : Matrix (Fin 2) (Fin 2) ℝ :=
    !![Real.cos θ, Real.sin θ; Real.sin θ, -Real.cos θ]
  have hrot : Oᵀ * O = 1 := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp only [mul_apply, transpose_apply, Fin.sum_univ_two]
      dsimp only [O]
      simp only [Fin.isValue, Fin.zero_eta, of_apply, cons_val', cons_val_zero,
        cons_val_fin_one, cons_val_one, one_apply_eq]
      rw [← sq, ← sq, Real.cos_sq_add_sin_sq]
    · simp only [mul_apply, transpose_apply, Fin.sum_univ_two]
      dsimp only [O]
      simp only [Fin.isValue, Fin.zero_eta, of_apply, cons_val', cons_val_zero,
        cons_val_fin_one, Fin.mk_one, cons_val_one, mul_neg, ne_eq, zero_ne_one,
        not_false_eq_true, one_apply_ne]
      ring
    · simp only [mul_apply, transpose_apply, Fin.sum_univ_two]
      dsimp only [O]
      simp only [Fin.mk_one, Fin.isValue, of_apply, cons_val', cons_val_one,
        cons_val_fin_one, cons_val_zero, Fin.zero_eta, neg_mul, ne_eq, one_ne_zero,
        not_false_eq_true, one_apply_ne]
      ring
    · simp only [mul_apply, transpose_apply, Fin.sum_univ_two]
      dsimp only [O]
      simp only [Fin.mk_one, Fin.isValue, of_apply, cons_val', cons_val_one,
        cons_val_fin_one, cons_val_zero, mul_neg, neg_mul, neg_neg, one_apply_eq]
      rw [← sq, ← sq, add_comm, Real.cos_sq_add_sin_sq]
  have hrot2 : O * Oᵀ = 1 := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp only [mul_apply, transpose_apply, Fin.sum_univ_two]
      dsimp only [O]
      simp only [Fin.zero_eta, Fin.isValue, of_apply, cons_val', cons_val_zero,
        cons_val_fin_one, cons_val_one, one_apply_eq]
      rw [← sq, ← sq, Real.cos_sq_add_sin_sq]
    · simp only [mul_apply, transpose_apply, Fin.sum_univ_two]
      dsimp only [O]
      simp only [Fin.zero_eta, Fin.isValue, of_apply, cons_val', cons_val_zero,
        cons_val_fin_one, Fin.mk_one, cons_val_one, mul_neg, ne_eq, zero_ne_one,
        not_false_eq_true, one_apply_ne]
      ring
    · simp only [mul_apply, transpose_apply, Fin.sum_univ_two]
      dsimp only [O]
      simp only [Fin.mk_one, Fin.isValue, of_apply, cons_val', cons_val_zero,
        cons_val_fin_one, cons_val_one, Fin.zero_eta, neg_mul, ne_eq, one_ne_zero,
        not_false_eq_true, one_apply_ne]
      ring
    · simp only [mul_apply, transpose_apply, Fin.sum_univ_two]
      dsimp only [O]
      simp only [Fin.mk_one, Fin.isValue, of_apply, cons_val', cons_val_zero,
        cons_val_fin_one, cons_val_one, mul_neg, neg_mul, neg_neg, one_apply_eq]
      rw [← sq, ← sq, Real.sin_sq_add_cos_sq]
  have hent : ∀ i j : Fin 2, A i j = (O i j) ^ 2 := by
    intro i j
    fin_cases i <;> fin_cases j
    · dsimp only [O]
      simp only [Fin.zero_eta, Fin.isValue, of_apply, cons_val', cons_val_zero,
        cons_val_fin_one]
      rw [hcos, s1]
    · dsimp only [O]
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, of_apply, cons_val',
        cons_val_one, cons_val_fin_one, cons_val_zero]
      rw [hsin, s2]
      linarith
    · dsimp only [O]
      simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, of_apply, cons_val',
        cons_val_zero, cons_val_fin_one, cons_val_one]
      rw [hb, hsin, s2]
      linarith
    · dsimp only [O]
      simp only [Fin.mk_one, Fin.isValue, of_apply, cons_val', cons_val_one,
        cons_val_fin_one, even_two, Even.neg_pow]
      rw [hcos, s1]
      exact h11
  exact IsOrthostochastic.isUnistochastic A ⟨O, hrot, hrot2, hent⟩

/-- Stochastic matrices multiplying to the identity are permutation matrices:
if `A * B = 1` for row-stochastic `A, B`, then `A` is a permutation matrix.
In particular, nontrivial stochastic dynamics is never invertible within the
class of stochastic maps. -/
theorem eq_permMatrix_of_rowStochastic_mul {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (hA : A ∈ rowStochastic ℝ n) (hB : B ∈ rowStochastic ℝ n)
    (hAB : A * B = 1) : ∃ σ : Equiv.Perm n, A = σ.permMatrix ℝ := by
  obtain ⟨hAn, hArow⟩ := hA
  obtain ⟨hBn, hBrow⟩ := hB
  have rowA : ∀ i, ∑ k, A i k = 1 := fun i => by
    have t := congrFun hArow i
    simpa [mulVec_apply, dotProduct, Pi.one_apply, mul_one] using t
  have rowB : ∀ k, ∑ j, B k j = 1 := fun k => by
    have t := congrFun hBrow k
    simpa [mulVec_apply, dotProduct, Pi.one_apply, mul_one] using t
  have hdet : A.det * B.det = 1 := by rw [← Matrix.det_mul, hAB, Matrix.det_one]
  have hAu : IsUnit A := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact ⟨⟨A.det, B.det, hdet, by rw [mul_comm, hdet]⟩, rfl⟩
  obtain ⟨u, hu⟩ := hAu
  have hBA : B * A = 1 := by
    have h2 : (↑u⁻¹ : Matrix n n ℝ) * (↑u : Matrix n n ℝ) = 1 := by simp
    have hBu : B = ↑u⁻¹ := by
      calc B = 1 * B := (one_mul B).symm
        _ = (↑u⁻¹ * ↑u) * B := by rw [← h2]
        _ = ↑u⁻¹ * (↑u * B) := mul_assoc _ _ _
        _ = ↑u⁻¹ * (A * B) := by rw [← hu]
        _ = ↑u⁻¹ * 1 := by rw [hAB]
        _ = ↑u⁻¹ := mul_one _
    rw [hBu, ← hu]
    exact h2
  have bnd : ∀ k i, B k i ≤ 1 := fun k i => by
    have := Finset.single_le_sum (fun j _ => hBn k j) (Finset.mem_univ i)
    rw [rowB k] at this; exact this
  have diagAB : ∀ i, ∑ k, A i k * B k i = 1 := fun i => by
    have t := congrFun (congrFun hAB i) i
    simpa [Matrix.mul_apply, Matrix.one_apply] using t
  have key : ∀ i k, A i k * (1 - B k i) = 0 := fun i k => by
    have hnonneg : ∀ k ∈ (Finset.univ : Finset n), 0 ≤ A i k * (1 - B k i) :=
      fun k _ => mul_nonneg (hAn i k) (by linarith [bnd k i])
    have hsum : ∑ k : n, A i k * (1 - B k i) = 0 := calc
      ∑ k : n, A i k * (1 - B k i) = ∑ k : n, (A i k - A i k * B k i) :=
          Finset.sum_congr rfl (fun k _ => by rw [mul_sub, mul_one])
      _ = (∑ k : n, A i k) - ∑ k : n, A i k * B k i := by simp [Finset.sum_sub_distrib]
      _ = 1 - 1 := by rw [rowA i, diagAB i]
      _ = 0 := by ring
    have := Finset.sum_eq_zero_iff_of_nonneg hnonneg |>.mp hsum
    exact this k (Finset.mem_univ k)
  have supp : ∀ i, ∃ k, A i k ≠ 0 := fun i => by
    by_contra h; push Not at h
    have : ∑ k, A i k = 0 := Finset.sum_eq_zero (fun k _ => h k)
    rw [rowA i] at this; exact one_ne_zero this
  choose k_i hk_i using supp
  have Bki : ∀ i, B (k_i i) i = 1 := fun i => by
    have := key i (k_i i)
    have hpos : 0 < A i (k_i i) := lt_of_le_of_ne (hAn i (k_i i)) (Ne.symm (hk_i i))
    nlinarith
  have Bzero : ∀ i l, l ≠ i → B (k_i i) l = 0 := fun i l hl => by
    have hsum := Finset.sum_erase_add (s := (Finset.univ : Finset n)) (a := i)
      (Finset.mem_univ i) (f := fun j => B (k_i i) j)
    rw [rowB (k_i i), Bki i] at hsum
    have hzero : ∑ x ∈ univ.erase i, B (k_i i) x = 0 := by linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => hBn (k_i i) j)).mp hzero l (Finset.mem_erase.mpr ⟨hl, mem_univ _⟩)
  have Aik : ∀ i, A i (k_i i) = 1 := by
    intro i
    have t := congrFun (congrFun hBA (k_i i)) (k_i i)
    rw [Matrix.mul_apply, Matrix.one_apply, ite_eq_left rfl] at t
    have hsplit : ∑ l, B (k_i i) l * A l (k_i i)
        = (∑ l ∈ univ.erase i, B (k_i i) l * A l (k_i i)) + B (k_i i) i * A i (k_i i) :=
      (Finset.sum_erase_add (s := (Finset.univ : Finset n)) (a := i) (Finset.mem_univ i)
        (f := fun l => B (k_i i) l * A l (k_i i))).symm
    have hsum0 : ∑ l ∈ univ.erase i, B (k_i i) l * A l (k_i i) = 0 :=
      Finset.sum_eq_zero (fun l hl => by rw [Bzero i l (Finset.mem_erase.mp hl).1, zero_mul])
    rw [hsplit, hsum0, zero_add, Bki i, one_mul] at t
    exact t
  have inj : Function.Injective k_i := by
    intro i₁ i₂ h
    by_contra hne
    have h1 : B (k_i i₁) i₁ = 1 := Bki i₁
    have h2 : B (k_i i₂) i₂ = 1 := Bki i₂
    rw [← h] at h2
    have e1 := Finset.sum_erase_add (s := (Finset.univ : Finset n)) (a := i₂)
      (Finset.mem_univ i₂) (f := fun j => B (k_i i₁) j)
    have e2 := Finset.sum_erase_add (s := (Finset.univ : Finset n).erase i₂) (a := i₁)
      (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩) (f := fun j => B (k_i i₁) j)
    let S := (Finset.univ : Finset n).erase i₂ |>.erase i₁
    have hnonneg : 0 ≤ ∑ j ∈ S, B (k_i i₁) j := Finset.sum_nonneg (fun j _ => hBn _ j)
    rw [← e2, h1, h2, rowB (k_i i₁)] at e1
    linarith
  set σ : Equiv.Perm n := Equiv.ofBijective k_i inj.bijective_of_finite
  refine ⟨σ, Matrix.ext fun i j => ?_⟩
  have happly : σ.permMatrix ℝ i j = (if k_i i = j then 1 else 0) := by
    simp [σ, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      Equiv.ofBijective_apply]
  rw [happly]
  by_cases h : j = k_i i
  · rw [ite_eq_left h.symm, h]
    exact Aik i
  · rw [ite_eq_right (Ne.symm h), show A i j = 0 from by
      have hsum := Finset.sum_erase_add (s := (Finset.univ : Finset n)) (a := k_i i)
        (Finset.mem_univ _) (f := fun k => A i k)
      rw [rowA i, Aik i] at hsum
      have hsum0 : ∑ k ∈ univ.erase (k_i i), A i k = 0 := by linarith
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun k _ => hAn i k)).mp hsum0 j (Finset.mem_erase.mpr ⟨h, mem_univ _⟩)]

end Matrix
