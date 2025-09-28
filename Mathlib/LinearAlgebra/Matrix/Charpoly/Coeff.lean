/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark
-/
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.RingTheory.Polynomial.Nilpotent

/-!
# Characteristic polynomials

We give methods for computing coefficients of the characteristic polynomial.

## Main definitions

- `Matrix.charpoly_degree_eq_dim` proves that the degree of the characteristic polynomial
  over a nonzero ring is the dimension of the matrix
- `Matrix.det_eq_sign_charpoly_coeff` proves that the determinant is the constant term of the
  characteristic polynomial, up to sign.
- `Matrix.trace_eq_neg_charpoly_coeff` proves that the trace is the negative of the (d-1)th
  coefficient of the characteristic polynomial, where d is the dimension of the matrix.
  For a nonzero ring, this is the second-highest coefficient.
- `Matrix.charpolyRev` the reverse of the characteristic polynomial.
- `Matrix.reverse_charpoly` characterises the reverse of the characteristic polynomial.

-/


noncomputable section

universe u v w z

open Finset Matrix Polynomial

variable {R : Type u} [CommRing R]
variable {n G : Type v} [DecidableEq n] [Fintype n]
variable {α β : Type v} [DecidableEq α]
variable {M : Matrix n n R}

namespace Matrix

theorem charmatrix_apply_natDegree [Nontrivial R] (i j : n) :
    (charmatrix M i j).natDegree = ite (i = j) 1 0 := by
  by_cases h : i = j <;> simp [h]

theorem charmatrix_apply_natDegree_le (i j : n) :
    (charmatrix M i j).natDegree ≤ ite (i = j) 1 0 := by
  split_ifs with h <;> simp [h, natDegree_X_le]

variable (M)

theorem charpoly_sub_diagonal_degree_lt :
    (M.charpoly - ∏ i : n, (X - C (M i i))).degree < ↑(Fintype.card n - 1) := by
  rw [charpoly, det_apply', ← insert_erase (mem_univ (Equiv.refl n)),
    sum_insert (notMem_erase (Equiv.refl n) univ), add_comm]
  simp only [charmatrix_apply_eq, one_mul, Equiv.Perm.sign_refl, id, Int.cast_one,
    Units.val_one, add_sub_cancel_right, Equiv.coe_refl]
  rw [← mem_degreeLT]
  apply Submodule.sum_mem (degreeLT R (Fintype.card n - 1))
  intro c hc; rw [← C_eq_intCast, C_mul']
  apply Submodule.smul_mem (degreeLT R (Fintype.card n - 1)) ↑↑(Equiv.Perm.sign c)
  rw [mem_degreeLT]
  apply lt_of_le_of_lt degree_le_natDegree _
  rw [Nat.cast_lt]
  apply lt_of_le_of_lt _ (Equiv.Perm.fixed_point_card_lt_of_ne_one (ne_of_mem_erase hc))
  apply le_trans (Polynomial.natDegree_prod_le univ fun i : n => charmatrix M (c i) i) _
  rw [card_eq_sum_ones]; rw [sum_filter]; apply sum_le_sum
  intros
  apply charmatrix_apply_natDegree_le

theorem charpoly_coeff_eq_prod_coeff_of_le {k : ℕ} (h : Fintype.card n - 1 ≤ k) :
    M.charpoly.coeff k = (∏ i : n, (X - C (M i i))).coeff k := by
  apply eq_of_sub_eq_zero; rw [← coeff_sub]
  apply Polynomial.coeff_eq_zero_of_degree_lt
  apply lt_of_lt_of_le (charpoly_sub_diagonal_degree_lt M) ?_
  rw [Nat.cast_le]; apply h

@[deprecated (since := "2025-08-14")] alias det_of_card_zero := det_eq_one_of_card_eq_zero

@[simp]
theorem charpoly_degree_eq_dim [Nontrivial R] (M : Matrix n n R) :
    M.charpoly.degree = Fintype.card n := by
  by_cases h : Fintype.card n = 0
  · rw [h]
    unfold charpoly
    rw [det_eq_one_of_card_eq_zero]
    · simp
    · assumption
  rw [← sub_add_cancel M.charpoly (∏ i : n, (X - C (M i i)))]
  -- Porting note: added `↑` in front of `Fintype.card n`
  have h1 : (∏ i : n, (X - C (M i i))).degree = ↑(Fintype.card n) := by
    rw [degree_eq_iff_natDegree_eq_of_pos (Nat.pos_of_ne_zero h), natDegree_prod']
    · simp_rw [natDegree_X_sub_C]
      rw [← Finset.card_univ, sum_const, smul_eq_mul, mul_one]
    simp_rw [(monic_X_sub_C _).leadingCoeff]
    simp
  rw [degree_add_eq_right_of_degree_lt]
  · exact h1
  rw [h1]
  apply lt_trans (charpoly_sub_diagonal_degree_lt M)
  rw [Nat.cast_lt]
  cutsat

@[simp] theorem charpoly_natDegree_eq_dim [Nontrivial R] (M : Matrix n n R) :
    M.charpoly.natDegree = Fintype.card n :=
  natDegree_eq_of_degree_eq_some (charpoly_degree_eq_dim M)

theorem charpoly_monic (M : Matrix n n R) : M.charpoly.Monic := by
  nontriviality R
  by_cases h : Fintype.card n = 0
  · rw [charpoly, det_eq_one_of_card_eq_zero h]
    apply monic_one
  have mon : (∏ i : n, (X - C (M i i))).Monic := by
    apply monic_prod_of_monic univ fun i : n => X - C (M i i)
    simp [monic_X_sub_C]
  rw [← sub_add_cancel (∏ i : n, (X - C (M i i))) M.charpoly] at mon
  rw [Monic] at *
  rwa [leadingCoeff_add_of_degree_lt] at mon
  rw [charpoly_degree_eq_dim]
  rw [← neg_sub]
  rw [degree_neg]
  apply lt_trans (charpoly_sub_diagonal_degree_lt M)
  rw [Nat.cast_lt]
  cutsat

/-- See also `Matrix.coeff_charpolyRev_eq_neg_trace`. -/
theorem trace_eq_neg_charpoly_coeff [Nonempty n] (M : Matrix n n R) :
    trace M = -M.charpoly.coeff (Fintype.card n - 1) := by
  rw [charpoly_coeff_eq_prod_coeff_of_le _ le_rfl, Fintype.card,
    prod_X_sub_C_coeff_card_pred univ (fun i : n => M i i) Fintype.card_pos, neg_neg, trace]
  simp_rw [diag_apply]

theorem det_eq_sign_charpoly_coeff (M : Matrix n n R) :
    M.det = (-1) ^ Fintype.card n * M.charpoly.coeff 0 := by
  rw [coeff_zero_eq_eval_zero, charpoly, eval_det, matPolyEquiv_charmatrix, ← det_smul]
  simp

lemma derivative_det_one_add_X_smul_aux {n} (M : Matrix (Fin n) (Fin n) R) :
    (derivative <| det (1 + (X : R[X]) • M.map C)).eval 0 = trace M := by
  induction n with
  | zero => simp
  | succ n IH =>
    rw [det_succ_row_zero, map_sum, eval_finset_sum]
    simp only [add_apply, smul_apply, map_apply, smul_eq_mul, X_mul_C, submatrix_add,
      submatrix_smul, Pi.add_apply, Pi.smul_apply, submatrix_map, derivative_mul, map_add,
      derivative_C, zero_mul, derivative_X, mul_one, zero_add, eval_add, eval_mul, eval_C, eval_X,
      mul_zero, add_zero, eval_det_add_X_smul, eval_pow, eval_neg, eval_one]
    rw [Finset.sum_eq_single 0]
    · simp only [Fin.val_zero, pow_zero, derivative_one, eval_zero, one_apply_eq, eval_one,
        mul_one, zero_add, one_mul, Fin.succAbove_zero, submatrix_one _ (Fin.succ_injective _),
        det_one, IH, trace_submatrix_succ]
    · intro i _ hi
      cases n with
      | zero => exact (hi (Subsingleton.elim i 0)).elim
      | succ n =>
        simp only [one_apply_ne' hi, eval_zero, mul_zero, zero_add, zero_mul, add_zero]
        rw [det_eq_zero_of_column_eq_zero 0, eval_zero, mul_zero]
        intro j
        rw [submatrix_apply, Fin.succAbove_of_castSucc_lt, one_apply_ne]
        · exact (bne_iff_ne (a := Fin.succ j) (b := Fin.castSucc 0)).mp rfl
        · rw [Fin.castSucc_zero]; exact lt_of_le_of_ne (Fin.zero_le _) hi.symm
    · exact fun H ↦ (H <| Finset.mem_univ _).elim

/-- The derivative of `det (1 + M X)` at `0` is the trace of `M`. -/
lemma derivative_det_one_add_X_smul (M : Matrix n n R) :
    (derivative <| det (1 + (X : R[X]) • M.map C)).eval 0 = trace M := by
  let e := Matrix.reindexLinearEquiv R R (Fintype.equivFin n) (Fintype.equivFin n)
  rw [← Matrix.det_reindexLinearEquiv_self R[X] (Fintype.equivFin n)]
  convert derivative_det_one_add_X_smul_aux (e M)
  · ext; simp [map_add, e]
  · delta trace
    rw [← (Fintype.equivFin n).symm.sum_comp]
    simp_rw [e, reindexLinearEquiv_apply, reindex_apply, diag_apply, submatrix_apply]

lemma coeff_det_one_add_X_smul_one (M : Matrix n n R) :
    (det (1 + (X : R[X]) • M.map C)).coeff 1 = trace M := by
  simp only [← derivative_det_one_add_X_smul, ← coeff_zero_eq_eval_zero,
    coeff_derivative, zero_add, Nat.cast_zero, mul_one]

lemma det_one_add_X_smul (M : Matrix n n R) :
    det (1 + (X : R[X]) • M.map C) =
      (1 : R[X]) + trace M • X + (det (1 + (X : R[X]) • M.map C)).divX.divX * X ^ 2 := by
  rw [Algebra.smul_def (trace M), ← C_eq_algebraMap, pow_two, ← mul_assoc, add_assoc,
    ← add_mul, ← coeff_det_one_add_X_smul_one, ← coeff_divX, add_comm (C _), divX_mul_X_add,
    add_comm (1 : R[X]), ← C.map_one]
  convert (divX_mul_X_add _).symm
  rw [coeff_zero_eq_eval_zero, eval_det_add_X_smul, det_one, eval_one]

/-- The first two terms of the Taylor expansion of `det (1 + r • M)` at `r = 0`. -/
lemma det_one_add_smul (r : R) (M : Matrix n n R) :
    det (1 + r • M) =
      1 + trace M * r + (det (1 + (X : R[X]) • M.map C)).divX.divX.eval r * r ^ 2 := by
  simpa [eval_det, ← smul_eq_mul_diagonal] using congr_arg (eval r) (Matrix.det_one_add_X_smul M)

lemma charpoly_of_card_eq_two [Nontrivial R] (hn : Fintype.card n = 2) :
    M.charpoly = X ^ 2 - C M.trace * X + C M.det := by
  have : Nonempty n := by rw [← Fintype.card_pos_iff]; omega
  ext i
  by_cases hi : i ∈ Finset.range 3
  · fin_cases hi
    · simp [det_eq_sign_charpoly_coeff, hn]
    · simp [trace_eq_neg_charpoly_coeff, hn]
    · simpa [leadingCoeff, charpoly_natDegree_eq_dim, hn, coeff_X] using
        M.charpoly_monic.leadingCoeff
  · rw [Finset.mem_range, not_lt, Nat.succ_le] at hi
    suffices M.charpoly.coeff i = 0 by
      simpa [show i ≠ 2 by cutsat, show 1 ≠ i by cutsat, show i ≠ 0 by cutsat, coeff_X, coeff_C]
    apply coeff_eq_zero_of_natDegree_lt
    simpa [charpoly_natDegree_eq_dim, hn] using hi

lemma charpoly_fin_two [Nontrivial R] (M : Matrix (Fin 2) (Fin 2) R) :
    M.charpoly = X ^ 2 - C M.trace * X + C M.det :=
  M.charpoly_of_card_eq_two <| Fintype.card_fin _

end Matrix

theorem matPolyEquiv_eq_X_pow_sub_C {K : Type*} (k : ℕ) [CommRing K] (M : Matrix n n K) :
    matPolyEquiv ((expand K k : K[X] →+* K[X]).mapMatrix (charmatrix (M ^ k))) =
      X ^ k - C (M ^ k) := by
  ext m i j
  rw [coeff_sub, coeff_C, matPolyEquiv_coeff_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    AlgHom.coe_toRingHom, DMatrix.sub_apply, coeff_X_pow]
  by_cases hij : i = j
  · rw [hij, charmatrix_apply_eq, map_sub, expand_C, expand_X, coeff_sub, coeff_X_pow, coeff_C]
    split_ifs with mp m0 <;> simp
  · rw [charmatrix_apply_ne _ _ _ hij, map_neg, expand_C, coeff_neg, coeff_C]
    split_ifs with m0 mp <;> simp_all

namespace Matrix

/-- Any matrix polynomial `p` is equivalent under evaluation to `p %ₘ M.charpoly`; that is, `p`
is equivalent to a polynomial with degree less than the dimension of the matrix. -/
theorem aeval_eq_aeval_mod_charpoly (M : Matrix n n R) (p : R[X]) :
    aeval M p = aeval M (p %ₘ M.charpoly) :=
  (aeval_modByMonic_eq_self_of_root M.charpoly_monic M.aeval_self_charpoly).symm

/-- Any matrix power can be computed as the sum of matrix powers less than `Fintype.card n`.

TODO: add the statement for negative powers phrased with `zpow`. -/
theorem pow_eq_aeval_mod_charpoly (M : Matrix n n R) (k : ℕ) :
    M ^ k = aeval M (X ^ k %ₘ M.charpoly) := by rw [← aeval_eq_aeval_mod_charpoly, map_pow, aeval_X]

section Ideal

theorem coeff_charpoly_mem_ideal_pow {I : Ideal R} (h : ∀ i j, M i j ∈ I) (k : ℕ) :
    M.charpoly.coeff k ∈ I ^ (Fintype.card n - k) := by
  delta charpoly
  rw [Matrix.det_apply, finset_sum_coeff]
  apply sum_mem
  rintro c -
  rw [coeff_smul, Submodule.smul_mem_iff']
  have : ∑ x : n, 1 = Fintype.card n := by rw [Finset.sum_const, card_univ, smul_eq_mul, mul_one]
  rw [← this]
  apply coeff_prod_mem_ideal_pow_tsub
  rintro i - (_ | k)
  · rw [tsub_zero, pow_one, charmatrix_apply, coeff_sub, ← smul_one_eq_diagonal, smul_apply,
      smul_eq_mul, coeff_X_mul_zero, coeff_C_zero, zero_sub, neg_mem_iff]
    exact h (c i) i
  · rw [add_comm, tsub_self_add, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top

end Ideal

section reverse

open LaurentPolynomial hiding C

/-- The reverse of the characteristic polynomial of a matrix.

It has some advantages over the characteristic polynomial, including the fact that it can be
extended to infinite dimensions (for appropriate operators). In such settings it is known as the
"characteristic power series". -/
def charpolyRev (M : Matrix n n R) : R[X] := det (1 - (X : R[X]) • M.map C)

lemma reverse_charpoly (M : Matrix n n R) :
    M.charpoly.reverse = M.charpolyRev := by
  nontriviality R
  let t : R[T;T⁻¹] := T 1
  let t_inv : R[T;T⁻¹] := T (-1)
  let p : R[T;T⁻¹] := det (scalar n t - M.map LaurentPolynomial.C)
  let q : R[T;T⁻¹] := det (1 - scalar n t * M.map LaurentPolynomial.C)
  have ht : t_inv * t = 1 := by rw [← T_add, neg_add_cancel, T_zero]
  have hp : toLaurentAlg M.charpoly = p := by
    simp [p, t, charpoly, charmatrix, AlgHom.map_det, map_sub]
  have hq : toLaurentAlg M.charpolyRev = q := by
    simp [q, t, charpolyRev, AlgHom.map_det, map_sub, smul_eq_diagonal_mul]
  suffices t_inv ^ Fintype.card n * p = invert q by
    apply toLaurent_injective
    rwa [toLaurent_reverse, ← coe_toLaurentAlg, hp, hq, ← involutive_invert.injective.eq_iff,
      map_mul, involutive_invert p, charpoly_natDegree_eq_dim,
      ← mul_one (Fintype.card n : ℤ), ← T_pow, map_pow, invert_T, mul_comm]
  rw [← det_smul, smul_sub, scalar_apply, ← diagonal_smul, Pi.smul_def, smul_eq_mul, ht,
    diagonal_one, invert.map_det]
  simp [t_inv, map_sub, map_one, map_mul, t, smul_eq_diagonal_mul]


@[simp] lemma eval_charpolyRev :
    eval 0 M.charpolyRev = 1 := by
  rw [charpolyRev, ← coe_evalRingHom, RingHom.map_det, ← det_one (R := R) (n := n)]
  have : (1 - (X : R[X]) • M.map C).map (eval 0) = 1 := by
    ext i j; rcases eq_or_ne i j with hij | hij <;> simp [hij, one_apply]
  congr

@[simp] lemma coeff_charpolyRev_eq_neg_trace (M : Matrix n n R) :
    coeff M.charpolyRev 1 = - trace M := by
  nontriviality R
  cases isEmpty_or_nonempty n
  · simp [charpolyRev, coeff_one]
  · simp [trace_eq_neg_charpoly_coeff M, ← M.reverse_charpoly, nextCoeff]

lemma isUnit_charpolyRev_of_isNilpotent (hM : IsNilpotent M) :
    IsUnit M.charpolyRev := by
  obtain ⟨k, hk⟩ := hM
  replace hk : 1 - (X : R[X]) • M.map C ∣ 1 := by
    convert one_sub_dvd_one_sub_pow ((X : R[X]) • M.map C) k
    rw [← C.mapMatrix_apply, smul_pow, ← map_pow, hk, map_zero, smul_zero, sub_zero]
  apply isUnit_of_dvd_one
  rw [← det_one (R := R[X]) (n := n)]
  exact map_dvd detMonoidHom hk

lemma isNilpotent_trace_of_isNilpotent (hM : IsNilpotent M) :
    IsNilpotent (trace M) := by
  cases isEmpty_or_nonempty n
  · simp
  suffices IsNilpotent (coeff (charpolyRev M) 1) by simpa using this
  exact (isUnit_iff_coeff_isUnit_isNilpotent.mp (isUnit_charpolyRev_of_isNilpotent hM)).2
    _ one_ne_zero

lemma isNilpotent_charpoly_sub_pow_of_isNilpotent (hM : IsNilpotent M) :
    IsNilpotent (M.charpoly - X ^ (Fintype.card n)) := by
  nontriviality R
  let p : R[X] := M.charpolyRev
  have hp : p - 1 = X * (p /ₘ X) := by
    conv_lhs => rw [← modByMonic_add_div p monic_X]
    simp [p, modByMonic_X]
  have : IsNilpotent (p /ₘ X) :=
    (Polynomial.isUnit_iff'.mp (isUnit_charpolyRev_of_isNilpotent hM)).2
  have aux : (M.charpoly - X ^ (Fintype.card n)).natDegree ≤ M.charpoly.natDegree :=
    le_trans (natDegree_sub_le _ _) (by simp)
  rw [← isNilpotent_reflect_iff aux, reflect_sub, ← reverse, M.reverse_charpoly]
  simpa [p, hp]

end reverse

end Matrix
