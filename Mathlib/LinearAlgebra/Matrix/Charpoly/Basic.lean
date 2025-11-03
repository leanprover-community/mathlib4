/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.RingTheory.MatrixPolynomialAlgebra

/-!
# Characteristic polynomials and the Cayley-Hamilton theorem

We define characteristic polynomials of matrices and
prove the Cayley–Hamilton theorem over arbitrary commutative rings.

See the file `Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean` for corollaries of this theorem.

## Main definitions

* `Matrix.charpoly` is the characteristic polynomial of a matrix.

## Implementation details

We follow a nice proof from http://drorbn.net/AcademicPensieve/2015-12/CayleyHamilton.pdf
-/

noncomputable section

universe u v w

namespace Matrix

open Finset Matrix Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]
variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)
variable (i j : n)


/-- The "characteristic matrix" of `M : Matrix n n R` is the matrix of polynomials $t I - M$.
The determinant of this matrix is the characteristic polynomial.
-/
def charmatrix (M : Matrix n n R) : Matrix n n R[X] :=
  Matrix.scalar n (X : R[X]) - (C : R →+* R[X]).mapMatrix M

theorem charmatrix_apply :
    charmatrix M i j = (Matrix.diagonal fun _ : n => X) i j - C (M i j) :=
  rfl

@[simp]
theorem charmatrix_apply_eq : charmatrix M i i = (X : R[X]) - C (M i i) := by
  simp only [charmatrix, RingHom.mapMatrix_apply, sub_apply, scalar_apply, map_apply,
    diagonal_apply_eq]

@[simp]
theorem charmatrix_apply_ne (h : i ≠ j) : charmatrix M i j = -C (M i j) := by
  simp only [charmatrix, RingHom.mapMatrix_apply, sub_apply, scalar_apply, diagonal_apply_ne _ h,
    map_apply, sub_eq_neg_self]

@[simp]
theorem charmatrix_zero : charmatrix (0 : Matrix n n R) = Matrix.scalar n (X : R[X]) := by
  simp [charmatrix]

@[simp]
theorem charmatrix_diagonal (d : n → R) :
    charmatrix (diagonal d) = diagonal fun i => X - C (d i) := by
  rw [charmatrix, scalar_apply, RingHom.mapMatrix_apply, diagonal_map (map_zero _), diagonal_sub]

@[simp]
theorem charmatrix_one : charmatrix (1 : Matrix n n R) = diagonal fun _ => X - 1 :=
  charmatrix_diagonal _

@[simp]
theorem charmatrix_natCast (k : ℕ) :
    charmatrix (k : Matrix n n R) = diagonal fun _ => X - (k : R[X]) :=
  charmatrix_diagonal _

@[simp]
theorem charmatrix_ofNat (k : ℕ) [k.AtLeastTwo] :
    charmatrix (ofNat(k) : Matrix n n R) = diagonal fun _ => X - ofNat(k) :=
  charmatrix_natCast _

@[simp]
theorem charmatrix_transpose (M : Matrix n n R) : (Mᵀ).charmatrix = M.charmatrixᵀ := by
  simp [charmatrix, transpose_map]

theorem matPolyEquiv_charmatrix : matPolyEquiv (charmatrix M) = X - C M := by
  ext k i j
  simp only [matPolyEquiv_coeff_apply, coeff_sub]
  by_cases h : i = j
  · subst h
    rw [charmatrix_apply_eq, coeff_sub]
    simp only [coeff_X, coeff_C]
    split_ifs <;> simp
  · rw [charmatrix_apply_ne _ _ _ h, coeff_X, coeff_neg, coeff_C, coeff_C]
    split_ifs <;> simp [h]

theorem charmatrix_reindex (e : n ≃ m) :
    charmatrix (reindex e e M) = reindex e e (charmatrix M) := by
  ext i j x
  by_cases h : i = j
  all_goals simp [h]

lemma charmatrix_map (M : Matrix n n R) (f : R →+* S) :
    charmatrix (M.map f) = (charmatrix M).map (Polynomial.map f) := by
  ext i j
  by_cases h : i = j <;> simp [h, charmatrix, diagonal]

lemma charmatrix_fromBlocks :
    charmatrix (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      fromBlocks (charmatrix M₁₁) (- M₁₂.map C) (- M₂₁.map C) (charmatrix M₂₂) := by
  simp only [charmatrix]
  ext (i|i) (j|j) : 2 <;> simp [diagonal]

-- TODO: importing block triangular here is somewhat expensive, if more lemmas about it are added
-- to this file, it may be worth extracting things out to Charpoly/Block.lean
@[simp]
lemma charmatrix_blockTriangular_iff {α : Type*} [Preorder α] {M : Matrix n n R} {b : n → α} :
    M.charmatrix.BlockTriangular b ↔ M.BlockTriangular b := by
  rw [charmatrix, scalar_apply, RingHom.mapMatrix_apply, (blockTriangular_diagonal _).sub_iff_right]
  simp [BlockTriangular]

alias ⟨BlockTriangular.of_charmatrix, BlockTriangular.charmatrix⟩ := charmatrix_blockTriangular_iff

/-- The characteristic polynomial of a matrix `M` is given by $\det (t I - M)$. -/
def charpoly (M : Matrix n n R) : R[X] :=
  (charmatrix M).det

theorem eval_charpoly (M : Matrix m m R) (t : R) :
    M.charpoly.eval t = (Matrix.scalar _ t - M).det := by
  rw [Matrix.charpoly, ← Polynomial.coe_evalRingHom, RingHom.map_det, Matrix.charmatrix]
  congr
  ext i j
  obtain rfl | hij := eq_or_ne i j <;> simp [*]

@[simp]
theorem charpoly_isEmpty [IsEmpty n] {A : Matrix n n R} : charpoly A = 1 := by
  simp [charpoly]

@[simp]
theorem charpoly_zero : charpoly (0 : Matrix n n R) = X ^ Fintype.card n := by
  simp [charpoly]

theorem charpoly_diagonal (d : n → R) : charpoly (diagonal d) = ∏ i, (X - C (d i)) := by
  simp [charpoly]

theorem charpoly_one : charpoly (1 : Matrix n n R) = (X - 1) ^ Fintype.card n := by
  simp [charpoly]

theorem charpoly_natCast (k : ℕ) :
    charpoly (k : Matrix n n R) = (X - (k : R[X])) ^ Fintype.card n := by
  simp [charpoly]

theorem charpoly_ofNat (k : ℕ) [k.AtLeastTwo] :
    charpoly (ofNat(k) : Matrix n n R) = (X - ofNat(k)) ^ Fintype.card n:=
  charpoly_natCast _

@[simp]
theorem charpoly_transpose (M : Matrix n n R) : (Mᵀ).charpoly = M.charpoly := by
  simp [charpoly]

theorem charpoly_reindex (e : n ≃ m)
    (M : Matrix n n R) : (reindex e e M).charpoly = M.charpoly := by
  unfold Matrix.charpoly
  rw [charmatrix_reindex, Matrix.det_reindex_self]

lemma charpoly_map (M : Matrix n n R) (f : R →+* S) :
    (M.map f).charpoly = M.charpoly.map f := by
  rw [charpoly, charmatrix_map, ← Polynomial.coe_mapRingHom, charpoly, RingHom.map_det,
    RingHom.mapMatrix_apply]

@[simp]
lemma charpoly_fromBlocks_zero₁₂ :
    (fromBlocks M₁₁ 0 M₂₁ M₂₂).charpoly = (M₁₁.charpoly * M₂₂.charpoly) := by
  simp only [charpoly, charmatrix_fromBlocks, Matrix.map_zero _ (Polynomial.C_0), neg_zero,
    det_fromBlocks_zero₁₂]

@[simp]
lemma charpoly_fromBlocks_zero₂₁ :
    (fromBlocks M₁₁ M₁₂ 0 M₂₂).charpoly = (M₁₁.charpoly * M₂₂.charpoly) := by
  simp only [charpoly, charmatrix_fromBlocks, Matrix.map_zero _ (Polynomial.C_0), neg_zero,
    det_fromBlocks_zero₂₁]

lemma charmatrix_toSquareBlock {α : Type*} [DecidableEq α] {b : n → α} {a : α} :
    (M.toSquareBlock b a).charmatrix = M.charmatrix.toSquareBlock b a := by
  ext i j : 1
  simp [charmatrix_apply, toSquareBlock_def, diagonal_apply, Subtype.ext_iff]

lemma BlockTriangular.charpoly {α : Type*} {b : n → α} [LinearOrder α] (h : M.BlockTriangular b) :
    M.charpoly = ∏ a ∈ image b univ, (M.toSquareBlock b a).charpoly := by
  simp only [Matrix.charpoly, h.charmatrix.det, charmatrix_toSquareBlock]

lemma charpoly_of_upperTriangular [LinearOrder n] (M : Matrix n n R) (h : M.BlockTriangular id) :
    M.charpoly = ∏ i : n, (X - C (M i i)) := by
  simp [charpoly, det_of_upperTriangular h.charmatrix]

-- This proof follows http://drorbn.net/AcademicPensieve/2015-12/CayleyHamilton.pdf
/-- The **Cayley-Hamilton Theorem**, that the characteristic polynomial of a matrix,
applied to the matrix itself, is zero.

This holds over any commutative ring.

See `LinearMap.aeval_self_charpoly` for the equivalent statement about endomorphisms.
-/
theorem aeval_self_charpoly (M : Matrix n n R) : aeval M M.charpoly = 0 := by
  -- We begin with the fact $χ_M(t) I = adjugate (t I - M) * (t I - M)$,
  -- as an identity in `Matrix n n R[X]`.
  have h : M.charpoly • (1 : Matrix n n R[X]) = adjugate (charmatrix M) * charmatrix M :=
    (adjugate_mul _).symm
  -- Using the algebra isomorphism `Matrix n n R[X] ≃ₐ[R] Polynomial (Matrix n n R)`,
  -- we have the same identity in `Polynomial (Matrix n n R)`.
  apply_fun matPolyEquiv at h
  simp only [map_mul, matPolyEquiv_charmatrix] at h
  -- Because the coefficient ring `Matrix n n R` is non-commutative,
  -- evaluation at `M` is not multiplicative.
  -- However, any polynomial which is a product of the form $N * (t I - M)$
  -- is sent to zero, because the evaluation function puts the polynomial variable
  -- to the right of any coefficients, so everything telescopes.
  apply_fun fun p => p.eval M at h
  rw [eval_mul_X_sub_C] at h
  -- Now $χ_M (t) I$, when thought of as a polynomial of matrices
  -- and evaluated at some `N` is exactly $χ_M (N)$.
  rw [matPolyEquiv_smul_one, eval_map] at h
  -- Thus we have $χ_M(M) = 0$, which is the desired result.
  exact h

/--
A version of `Matrix.charpoly_mul_comm` for rectangular matrices.
See also `Matrix.charpoly_mul_comm_of_le` which has just `(A * B).charpoly` as the LHS.
-/
theorem charpoly_mul_comm' (A : Matrix m n R) (B : Matrix n m R) :
    X ^ Fintype.card n * (A * B).charpoly = X ^ Fintype.card m * (B * A).charpoly := by
  -- This proof follows https://math.stackexchange.com/a/311362/315369
  let M := fromBlocks (scalar m X) (A.map C) (B.map C) (1 : Matrix n n R[X])
  let N := fromBlocks (-1 : Matrix m m R[X]) 0 (B.map C) (-scalar n X)
  have hMN :
      M * N = fromBlocks (-scalar m X + (A * B).map C) (-(X : R[X]) • A.map C) 0 (-scalar n X) := by
    simp [M, N, fromBlocks_multiply, smul_eq_mul_diagonal, -diagonal_neg]
  have hNM : N * M = fromBlocks (-scalar m X) (-A.map C) 0 ((B * A).map C - scalar n X) := by
    simp [M, N, fromBlocks_multiply, sub_eq_add_neg, -scalar_apply, scalar_comm, Commute.all]
  have hdet_MN : (M * N).det = (-1 : R[X]) ^ (Fintype.card m + Fintype.card n) *
      (X ^ Fintype.card n * (scalar m X - (A * B).map C).det) := by
    rw [hMN, det_fromBlocks_zero₂₁, neg_add_eq_sub, ← neg_sub, det_neg]
    simp
    ring
  have hdet_NM : (N * M).det = (-1 : R[X]) ^ (Fintype.card m + Fintype.card n) *
      (X ^ Fintype.card m * (scalar n X - (B * A).map C).det) := by
    rw [hNM, det_fromBlocks_zero₂₁, ← neg_sub, det_neg (_ - _)]
    simp
    ring
  dsimp only [charpoly, charmatrix, RingHom.mapMatrix_apply]
  rw [← (isUnit_neg_one.pow _).isRegular.left.eq_iff, ← hdet_NM, ← hdet_MN, det_mul_comm]

theorem charpoly_mul_comm_of_le
    (A : Matrix m n R) (B : Matrix n m R) (hle : Fintype.card n ≤ Fintype.card m) :
    (A * B).charpoly = X ^ (Fintype.card m - Fintype.card n) * (B * A).charpoly := by
  rw [← (isRegular_X_pow _).left.eq_iff, ← mul_assoc, ← pow_add,
    Nat.add_sub_cancel' hle, charpoly_mul_comm']

/-- A version of `charpoly_mul_comm'` for square matrices. -/
theorem charpoly_mul_comm (A B : Matrix n n R) : (A * B).charpoly = (B * A).charpoly :=
  (isRegular_X_pow _).left.eq_iff.mp <| charpoly_mul_comm' A B

theorem charpoly_vecMulVec (u v : n → R) :
    (vecMulVec u v).charpoly = X ^ Fintype.card n - (u ⬝ᵥ v) • X ^ (Fintype.card n - 1) := by
  cases isEmpty_or_nonempty n
  · simp
  · have h : 1 ≤ Fintype.card n := NeZero.one_le
    rw [vecMulVec_eq (ι := Unit), charpoly_mul_comm_of_le (n := Unit) _ _ h, charpoly, charmatrix]
    simp [-Matrix.map_mul, mul_sub, ← pow_succ, h, dotProduct_comm, smul_eq_C_mul]

theorem charpoly_units_conj (M : (Matrix n n R)ˣ) (N : Matrix n n R) :
    (M.val * N * M⁻¹.val).charpoly = N.charpoly := by
  rw [Matrix.charpoly_mul_comm, ← mul_assoc]
  simp

theorem charpoly_units_conj' (M : (Matrix n n R)ˣ) (N : Matrix n n R) :
    (M⁻¹.val * N * M.val).charpoly = N.charpoly :=
  charpoly_units_conj M⁻¹ N

theorem charpoly_sub_scalar (M : Matrix n n R) (μ : R) :
    (M - scalar n μ).charpoly  = M.charpoly.comp (X + C μ) := by
  simp_rw [charpoly, det_apply, Polynomial.sum_comp, Polynomial.smul_comp, Polynomial.prod_comp]
  congr! with σ _ i _
  by_cases hi : σ i = i <;> simp [hi]
  ring

end Matrix
