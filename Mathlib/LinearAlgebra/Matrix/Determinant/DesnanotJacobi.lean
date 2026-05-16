/-
Copyright (c) 2026 Slava Naprienko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Slava Naprienko
-/
module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial

/-!
# The Desnanot-Jacobi identity

We prove the **Desnanot-Jacobi identity** (also known as the Lewis Carroll identity or
Dodgson condensation): for any `(n + 2) × (n + 2)` matrix `M` over a commutative ring,
`det M · det M_interior = det M_NW · det M_SE - det M_NE · det M_SW`,
where each "corner" submatrix is obtained from `M` by deleting one corner (first or
last row, first or last column), and `M_interior` is obtained by deleting the first
and last row and column.

The proof first establishes the identity premultiplied by `det M` over an arbitrary
commutative ring, by computing `det (M * P)` two ways for an auxiliary matrix `P`
built from columns of the adjugate. The premultiplication is then canceled by
passing to `Matrix.mvPolynomialX`, where the determinant is nonzero, and specializing
back via `MvPolynomial.aeval`.

## Main results

* `Matrix.desnanot_jacobi`: the Desnanot-Jacobi identity for any commutative ring.
-/

@[expose] public section

namespace Matrix

open Finset MvPolynomial

variable {n : ℕ} {R : Type*} [CommRing R]

/-- Auxiliary matrix used in the proof of `Matrix.desnanot_jacobi`: it agrees with
the identity matrix on the middle columns and with the corresponding columns of
`adjugate M` at column `0` and column `Fin.last (n + 1)`. -/
private def desnanotAux (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) R := fun i j ↦
  if j = 0 then adjugate M i 0
  else if j = Fin.last (n + 1) then adjugate M i (Fin.last (n + 1))
  else if i = j then 1
  else 0

/-- Pointwise formula for `M * desnanotAux M`: `det M` at the diagonal corners, zero
elsewhere in the corner columns, and the entries of `M` in the middle columns. -/
private lemma mul_desnanotAux_apply (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R)
    (i j : Fin (n + 2)) :
    (M * desnanotAux M) i j =
      if j = 0 then if i = 0 then M.det else 0
      else if j = Fin.last (n + 1) then if i = Fin.last (n + 1) then M.det else 0
      else M i j := by
  simp only [desnanotAux, mul_apply]
  rcases eq_or_ne j 0 with rfl | hj0
  · simpa only [smul_eq_mul, smul_apply, one_apply, mul_boole]
      using congr_fun (congr_fun (mul_adjugate M) i) 0
  rcases eq_or_ne j (Fin.last (n + 1)) with rfl | hjk
  · simpa only [smul_eq_mul, smul_apply, one_apply, mul_boole]
      using congr_fun (congr_fun (mul_adjugate M) i) (Fin.last (n + 1))
  simp only [hj0, hjk, mul_ite, mul_one, mul_zero, ite_false]
  rw [sum_eq_single j (fun b _ hbj ↦ if_neg hbj) (fun hj ↦ (hj (mem_univ j)).elim),
    if_pos rfl]

/-- Determinant of `M * desnanotAux M`: cofactor-expand along columns `0` and last to
peel off two factors of `det M`. -/
private lemma det_M_mul_desnanotAux (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :
    (M * desnanotAux M).det = M.det ^ 2 *
      (M.submatrix (Fin.succAbove 0 ∘ (Fin.last n).succAbove)
        (Fin.succAbove 0 ∘ (Fin.last n).succAbove)).det := by
  let Q := (M * desnanotAux M).submatrix Fin.succ Fin.succ
  have h_inner :
      (M * desnanotAux M).submatrix (Fin.succ ∘ Fin.castSucc) (Fin.succ ∘ Fin.castSucc) =
        M.submatrix (Fin.succAbove 0 ∘ (Fin.last n).succAbove)
          (Fin.succAbove 0 ∘ (Fin.last n).succAbove) := by
    ext i j
    simp [mul_desnanotAux_apply, Function.comp, Fin.succ_ne_zero]
  have h1 : (M * desnanotAux M).det = M.det * Q.det := by
    rw [det_succ_column _ 0, sum_eq_single 0]
    · simp [mul_desnanotAux_apply, Q]
    · intro i _ hi; simp [mul_desnanotAux_apply, hi]
    · simp
  have h2 : Q.det = M.det *
      (M.submatrix (Fin.succAbove 0 ∘ (Fin.last n).succAbove)
        (Fin.succAbove 0 ∘ (Fin.last n).succAbove)).det := by
    rw [det_succ_column Q (Fin.last n), sum_eq_single (Fin.last n)]
    · simp [Q, mul_desnanotAux_apply, h_inner]
    · intro b _ hb; simp [Q, mul_desnanotAux_apply, hb]
    · simp
  rw [h1, h2, sq, mul_assoc]

/-- Determinant of `desnanotAux M`: cofactor-expand along row `0`, where only the
entries in column `0` and column `last` are nonzero. The minors collapse to
determinants of corner submatrices of `M`. -/
private lemma det_desnanotAux (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :
    (desnanotAux M).det =
      (M.submatrix (Fin.succAbove 0) (Fin.succAbove 0)).det *
          (M.submatrix (Fin.last (n + 1)).succAbove (Fin.last (n + 1)).succAbove).det -
        (M.submatrix (Fin.succAbove 0) (Fin.last (n + 1)).succAbove).det *
          (M.submatrix (Fin.last (n + 1)).succAbove (Fin.succAbove 0)).det := by
  let f0 := (0 : Fin (n + 2)).succAbove
  let fn := (Fin.last (n + 1)).succAbove
  let M'11 := (desnanotAux M).submatrix f0 f0
  let M'1n := (desnanotAux M).submatrix f0 fn
  have h_M'_expand : (desnanotAux M).det =
      desnanotAux M 0 0 * M'11.det + (-1 : R) ^ (n + 1) *
        desnanotAux M 0 (Fin.last (n + 1)) * M'1n.det := by
    rw [Matrix.det_succ_row (desnanotAux M) 0, Fin.sum_univ_succ,
      Finset.sum_eq_single (Fin.last n)]
    · simp [M'11, M'1n, f0, fn]
    · intro b _ hb
      have h1 : (b.succ : Fin (n + 2)) ≠ 0 := Fin.succ_ne_zero b
      have h2 : (b.succ : Fin (n + 2)) ≠ Fin.last (n + 1) := by
        intro h; exact hb (Fin.succ_inj.mp (by rw [h, ← Fin.succ_last]))
      simp [desnanotAux, h1, h1.symm, h2]
    · simp
  have h_id_NW : ((desnanotAux M).submatrix (Fin.succAbove 0) (Fin.succAbove 0)).submatrix
      (Fin.last n).succAbove (Fin.last n).succAbove = 1 := by
    ext i j
    simp [desnanotAux, Fin.succ_inj, Matrix.one_apply]
  have h_id_NE : ((desnanotAux M).submatrix (Fin.succAbove 0)
      (Fin.last (n + 1)).succAbove).submatrix (Fin.last n).succAbove (Fin.succAbove 0) = 1 := by
    ext i j
    simp [desnanotAux, Fin.ext_iff, Matrix.one_apply]
    omega
  rw [h_M'_expand]
  have h_M'00 : desnanotAux M 0 0 = (M.submatrix (Fin.succAbove 0) (Fin.succAbove 0)).det := by
    change adjugate M 0 0 = _
    rw [adjugate_fin_succ_eq_det_submatrix]; simp
  have h_M'0n : desnanotAux M 0 (Fin.last (n + 1)) =
      (-1) ^ (n + 1) * (M.submatrix (Fin.last (n + 1)).succAbove (Fin.succAbove 0)).det := by
    simp [desnanotAux, adjugate_fin_succ_eq_det_submatrix]
  have h_M'11_det : M'11.det =
      (M.submatrix (Fin.last (n + 1)).succAbove (Fin.last (n + 1)).succAbove).det := by
    rw [det_succ_column M'11 (Fin.last n), sum_eq_single (Fin.last n)]
    · have h_entry : M'11 (Fin.last n) (Fin.last n) =
          (M.submatrix (Fin.last (n + 1)).succAbove (Fin.last (n + 1)).succAbove).det := by
        simp [M'11, desnanotAux, f0, submatrix_apply,
          Fin.succAbove_zero, Fin.succ_last, adjugate_fin_succ_eq_det_submatrix]
      rw [h_entry, h_id_NW, det_one, mul_one]
      simp only [Fin.val_last, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
    · intro b _ hb
      obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq (Ne.symm hb)
      suffices hdet :
          (M'11.submatrix b.succAbove (Fin.last n).succAbove).det = 0 by rw [hdet]; ring
      refine det_eq_zero_of_row_eq_zero r fun j ↦ ?_
      have ne_last : (j.castSucc.succ : Fin (n + 2)) ≠ Fin.last (n + 1) := by
        simp [Fin.ext_iff]; omega
      simp [submatrix_apply, M'11, desnanotAux, f0, Fin.succAbove_zero, hr,
        ne_last, ne_last.symm]
    · simp
  have h_M'1n : M'1n.det = -(M.submatrix (Fin.succAbove 0) (Fin.last (n + 1)).succAbove).det := by
    rw [det_succ_column M'1n 0, sum_eq_single (Fin.last n)]
    · have h_entry : M'1n (Fin.last n) 0 = adjugate M (Fin.last (n + 1)) 0 := by
        simp [M'1n, desnanotAux, f0, fn, submatrix_apply,
          Fin.succAbove_zero, Fin.succAbove_last, Fin.succ_last]
      rw [h_entry, adjugate_fin_succ_eq_det_submatrix]
      simp only [Fin.val_zero, zero_add, Fin.val_last]
      have hp : n + 0 + (n + 1) = 2 * n + 1 := by omega
      rw [h_id_NE, det_one, mul_one, ← mul_assoc,
        ← pow_add, hp, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, neg_one_mul]
    · intro b _ hb
      obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq (Ne.symm hb)
      suffices hdet : (M'1n.submatrix b.succAbove (Fin.succAbove 0)).det = 0 by rw [hdet]; ring
      refine det_eq_zero_of_row_eq_zero r fun j ↦ ?_
      have ne_last : (j.castSucc.succ : Fin (n + 2)) ≠ Fin.last (n + 1) := by
        simp [Fin.ext_iff]; omega
      simp [submatrix_apply, M'1n, desnanotAux,
        f0, fn, Fin.succAbove_zero, Fin.succAbove_last, Fin.succ_last, hr,
        ne_last, ne_last.symm]
    · simp
  rw [h_M'00, h_M'11_det, h_M'0n, h_M'1n,
    mul_neg, ← mul_assoc, ← mul_pow, neg_mul_neg, one_mul, one_pow]
  ring

/-- The Desnanot-Jacobi identity premultiplied by `det M`. The unprefixed form follows
by canceling `det M` over `Matrix.mvPolynomialX` in `Matrix.desnanot_jacobi`. -/
private lemma det_mul_desnanot_jacobi (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :
    M.det * (M.det * (M.submatrix (Fin.succAbove 0 ∘ (Fin.last n).succAbove)
        (Fin.succAbove 0 ∘ (Fin.last n).succAbove)).det) =
    M.det * ((M.submatrix (Fin.succAbove 0) (Fin.succAbove 0)).det *
        (M.submatrix (Fin.last (n + 1)).succAbove (Fin.last (n + 1)).succAbove).det -
      (M.submatrix (Fin.succAbove 0) (Fin.last (n + 1)).succAbove).det *
        (M.submatrix (Fin.last (n + 1)).succAbove (Fin.succAbove 0)).det) := by
  rw [← mul_assoc, ← sq, ← det_M_mul_desnanotAux, det_mul, det_desnanotAux]

/-- The **Desnanot-Jacobi identity** (Lewis Carroll identity, Dodgson condensation):
for any `(n + 2) × (n + 2)` matrix `M` over a commutative ring,
`det M · det M_interior = det M_NW · det M_SE - det M_NE · det M_SW`. -/
theorem desnanot_jacobi (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :
    M.det * (M.submatrix (Fin.succAbove 0 ∘ (Fin.last n).succAbove)
        (Fin.succAbove 0 ∘ (Fin.last n).succAbove)).det =
    (M.submatrix (Fin.succAbove 0) (Fin.succAbove 0)).det *
        (M.submatrix (Fin.last (n + 1)).succAbove (Fin.last (n + 1)).succAbove).det -
      (M.submatrix (Fin.succAbove 0) (Fin.last (n + 1)).succAbove).det *
        (M.submatrix (Fin.last (n + 1)).succAbove (Fin.succAbove 0)).det := by
  -- Pass to the universal matrix to cancel `det M`, then specialize via `aeval`.
  let X := mvPolynomialX (Fin (n + 2)) (Fin (n + 2)) ℤ
  let φ : MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℤ →ₐ[ℤ] R :=
    MvPolynomial.aeval fun p ↦ M p.1 p.2
  -- Push `φ` through `det` on any submatrix of `X`.
  have h_det_sub : ∀ {m : ℕ} (r c : Fin m → Fin (n + 2)),
      φ (X.submatrix r c).det = (M.submatrix r c).det := fun r c ↦ by
    rw [AlgHom.map_det]; congr 1; ext i j
    simp [φ, X, AlgHom.mapMatrix_apply, mvPolynomialX_apply]
  simpa [map_sub, map_mul, h_det_sub,
    show φ X.det = M.det from by rw [AlgHom.map_det, mvPolynomialX_mapMatrix_aeval]]
    using congr_arg φ
      (mul_left_cancel₀ (det_mvPolynomialX_ne_zero (Fin (n + 2)) ℤ)
        (det_mul_desnanot_jacobi X))

end Matrix
