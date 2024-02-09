/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark
-/
import Mathlib.Data.Polynomial.Expand
import Mathlib.Data.Polynomial.Laurent
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.RingTheory.Polynomial.Nilpotent

#align_import linear_algebra.matrix.charpoly.coeff from "leanprover-community/mathlib"@"9745b093210e9dac443af24da9dba0f9e2b6c912"

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
--  porting note: whenever there was `∏ i : n, X - C (M i i)`, I replaced it with
--  `∏ i : n, (X - C (M i i))`, since otherwise Lean would parse as `(∏ i : n, X) - C (M i i)`

universe u v w z

open Polynomial Matrix BigOperators

variable {R : Type u} [CommRing R]

variable {n G : Type v} [DecidableEq n] [Fintype n]

variable {α β : Type v} [DecidableEq α]

open Finset

variable {M : Matrix n n R}

theorem charmatrix_apply_natDegree [Nontrivial R] (i j : n) :
    (charmatrix M i j).natDegree = ite (i = j) 1 0 := by
  by_cases h : i = j <;> simp [h, ← degree_eq_iff_natDegree_eq_of_pos (Nat.succ_pos 0)]
#align charmatrix_apply_nat_degree charmatrix_apply_natDegree

theorem charmatrix_apply_natDegree_le (i j : n) :
    (charmatrix M i j).natDegree ≤ ite (i = j) 1 0 := by
  split_ifs with h <;> simp [h, natDegree_X_le]
#align charmatrix_apply_nat_degree_le charmatrix_apply_natDegree_le

namespace Matrix

variable (M)

theorem charpoly_sub_diagonal_degree_lt :
    (M.charpoly - ∏ i : n, (X - C (M i i))).degree < ↑(Fintype.card n - 1) := by
  rw [charpoly, det_apply', ← insert_erase (mem_univ (Equiv.refl n)),
    sum_insert (not_mem_erase (Equiv.refl n) univ), add_comm]
  simp only [charmatrix_apply_eq, one_mul, Equiv.Perm.sign_refl, id.def, Int.cast_one,
    Units.val_one, add_sub_cancel, Equiv.coe_refl]
  rw [← mem_degreeLT]
  apply Submodule.sum_mem (degreeLT R (Fintype.card n - 1))
  intro c hc; rw [← C_eq_int_cast, C_mul']
  apply Submodule.smul_mem (degreeLT R (Fintype.card n - 1)) ↑↑(Equiv.Perm.sign c)
  rw [mem_degreeLT]
  apply lt_of_le_of_lt degree_le_natDegree _
  rw [Nat.cast_lt]
  apply lt_of_le_of_lt _ (Equiv.Perm.fixed_point_card_lt_of_ne_one (ne_of_mem_erase hc))
  apply le_trans (Polynomial.natDegree_prod_le univ fun i : n => charmatrix M (c i) i) _
  rw [card_eq_sum_ones]; rw [sum_filter]; apply sum_le_sum
  intros
  apply charmatrix_apply_natDegree_le
#align matrix.charpoly_sub_diagonal_degree_lt Matrix.charpoly_sub_diagonal_degree_lt

theorem charpoly_coeff_eq_prod_coeff_of_le {k : ℕ} (h : Fintype.card n - 1 ≤ k) :
    M.charpoly.coeff k = (∏ i : n, (X - C (M i i))).coeff k := by
  apply eq_of_sub_eq_zero; rw [← coeff_sub]
  apply Polynomial.coeff_eq_zero_of_degree_lt
  apply lt_of_lt_of_le (charpoly_sub_diagonal_degree_lt M) ?_
  rw [Nat.cast_le]; apply h
#align matrix.charpoly_coeff_eq_prod_coeff_of_le Matrix.charpoly_coeff_eq_prod_coeff_of_le

theorem det_of_card_zero (h : Fintype.card n = 0) (M : Matrix n n R) : M.det = 1 := by
  rw [Fintype.card_eq_zero_iff] at h
  suffices M = 1 by simp [this]
  ext i
  exact h.elim i
#align matrix.det_of_card_zero Matrix.det_of_card_zero

theorem charpoly_degree_eq_dim [Nontrivial R] (M : Matrix n n R) :
    M.charpoly.degree = Fintype.card n := by
  by_cases h : Fintype.card n = 0
  · rw [h]
    unfold charpoly
    rw [det_of_card_zero]
    · simp
    · assumption
  rw [← sub_add_cancel M.charpoly (∏ i : n, (X - C (M i i)))]
  -- porting note: added `↑` in front of `Fintype.card n`
  have h1 : (∏ i : n, (X - C (M i i))).degree = ↑(Fintype.card n) := by
    rw [degree_eq_iff_natDegree_eq_of_pos (Nat.pos_of_ne_zero h), natDegree_prod']
    simp_rw [natDegree_X_sub_C]
    rw [← Finset.card_univ, sum_const, smul_eq_mul, mul_one]
    simp_rw [(monic_X_sub_C _).leadingCoeff]
    simp
  rw [degree_add_eq_right_of_degree_lt]
  exact h1
  rw [h1]
  apply lt_trans (charpoly_sub_diagonal_degree_lt M)
  rw [Nat.cast_lt]
  rw [← Nat.pred_eq_sub_one]
  apply Nat.pred_lt
  apply h
#align matrix.charpoly_degree_eq_dim Matrix.charpoly_degree_eq_dim

@[simp] theorem charpoly_natDegree_eq_dim [Nontrivial R] (M : Matrix n n R) :
    M.charpoly.natDegree = Fintype.card n :=
  natDegree_eq_of_degree_eq_some (charpoly_degree_eq_dim M)
#align matrix.charpoly_nat_degree_eq_dim Matrix.charpoly_natDegree_eq_dim

theorem charpoly_monic (M : Matrix n n R) : M.charpoly.Monic := by
  nontriviality R -- porting note: was simply `nontriviality`
  by_cases h : Fintype.card n = 0
  · rw [charpoly, det_of_card_zero h]
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
  rw [← Nat.pred_eq_sub_one]
  apply Nat.pred_lt
  apply h
#align matrix.charpoly_monic Matrix.charpoly_monic

/-- See also `Matrix.coeff_charpolyRev_eq_neg_trace`. -/
theorem trace_eq_neg_charpoly_coeff [Nonempty n] (M : Matrix n n R) :
    trace M = -M.charpoly.coeff (Fintype.card n - 1) := by
  rw [charpoly_coeff_eq_prod_coeff_of_le _ le_rfl, Fintype.card,
    prod_X_sub_C_coeff_card_pred univ (fun i : n => M i i) Fintype.card_pos, neg_neg, trace]
  simp_rw [diag_apply]
#align matrix.trace_eq_neg_charpoly_coeff Matrix.trace_eq_neg_charpoly_coeff

theorem matPolyEquiv_symm_map_eval (M : (Matrix n n R)[X]) (r : R) :
    (matPolyEquiv.symm M).map (eval r) = M.eval (scalar n r) := by
  suffices ((aeval r).mapMatrix.comp matPolyEquiv.symm.toAlgHom : (Matrix n n R)[X] →ₐ[R] _) =
      (eval₂AlgHom' (AlgHom.id R _) (scalar n r)
        fun x => (scalar_commute _ (Commute.all _) _).symm) from
    DFunLike.congr_fun this M
  ext : 1
  · ext M : 1
    simp [Function.comp]
  · simp [smul_eq_diagonal_mul]

theorem matPolyEquiv_eval_eq_map (M : Matrix n n R[X]) (r : R) :
    (matPolyEquiv M).eval (scalar n r) = M.map (eval r) := by
  simpa only [AlgEquiv.symm_apply_apply] using (matPolyEquiv_symm_map_eval (matPolyEquiv M) r).symm

-- I feel like this should use `Polynomial.algHom_eval₂_algebraMap`
theorem matPolyEquiv_eval (M : Matrix n n R[X]) (r : R) (i j : n) :
    (matPolyEquiv M).eval (scalar n r) i j = (M i j).eval r := by
  rw [matPolyEquiv_eval_eq_map, map_apply]
#align matrix.mat_poly_equiv_eval Matrix.matPolyEquiv_eval

theorem eval_det (M : Matrix n n R[X]) (r : R) :
    Polynomial.eval r M.det = (Polynomial.eval (scalar n r) (matPolyEquiv M)).det := by
  rw [Polynomial.eval, ← coe_eval₂RingHom, RingHom.map_det]
  apply congr_arg det
  ext
  symm
  -- porting note: `exact` was `convert`
  exact matPolyEquiv_eval _ _ _ _
#align matrix.eval_det Matrix.eval_det

theorem det_eq_sign_charpoly_coeff (M : Matrix n n R) :
    M.det = (-1) ^ Fintype.card n * M.charpoly.coeff 0 := by
  rw [coeff_zero_eq_eval_zero, charpoly, eval_det, matPolyEquiv_charmatrix, ← det_smul]
  simp
#align matrix.det_eq_sign_charpoly_coeff Matrix.det_eq_sign_charpoly_coeff

lemma eval_det_add_X_smul (A : Matrix n n R[X]) (M : Matrix n n R) :
    (det (A + (X : R[X]) • M.map C)).eval 0 = (det A).eval 0 := by
  simp only [eval_det, map_zero, map_add, eval_add, Algebra.smul_def, _root_.map_mul]
  simp only [Algebra.algebraMap_eq_smul_one, matPolyEquiv_smul_one, map_X, X_mul, eval_mul_X,
    mul_zero, add_zero]

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
        · exact (bne_iff_ne (Fin.succ j) (Fin.castSucc 0)).mp rfl
        · rw [Fin.castSucc_zero]; exact lt_of_le_of_ne (Fin.zero_le _) hi.symm
    · exact fun H ↦ (H <| Finset.mem_univ _).elim

/-- The derivative of `det (1 + M X)` at `0` is the trace of `M`. -/
lemma derivative_det_one_add_X_smul (M : Matrix n n R) :
    (derivative <| det (1 + (X : R[X]) • M.map C)).eval 0 = trace M := by
  let e := Matrix.reindexLinearEquiv R R (Fintype.equivFin n) (Fintype.equivFin n)
  rw [← Matrix.det_reindexLinearEquiv_self R[X] (Fintype.equivFin n)]
  convert derivative_det_one_add_X_smul_aux (e M)
  · ext; simp
  · delta trace
    rw [← (Fintype.equivFin n).symm.sum_comp]
    rfl

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

/-- The first two terms of the taylor expansion of `det (1 + r • M)` at `r = 0`. -/
lemma det_one_add_smul (r : R) (M : Matrix n n R) :
    det (1 + r • M) =
      1 + trace M * r + (det (1 + (X : R[X]) • M.map C)).divX.divX.eval r * r ^ 2 := by
  simpa [eval_det, ← smul_eq_mul_diagonal] using congr_arg (eval r) (Matrix.det_one_add_X_smul M)

end Matrix

variable {p : ℕ} [Fact p.Prime]

theorem matPolyEquiv_eq_x_pow_sub_c {K : Type*} (k : ℕ) [Field K] (M : Matrix n n K) :
    matPolyEquiv ((expand K k : K[X] →+* K[X]).mapMatrix (charmatrix (M ^ k))) =
      X ^ k - C (M ^ k) := by
  -- porting note: `i` and `j` are used later on, but were not mentioned in mathlib3
  ext m i j
  rw [coeff_sub, coeff_C, matPolyEquiv_coeff_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    AlgHom.coe_toRingHom, DMatrix.sub_apply, coeff_X_pow]
  by_cases hij : i = j
  · rw [hij, charmatrix_apply_eq, AlgHom.map_sub, expand_C, expand_X, coeff_sub, coeff_X_pow,
      coeff_C]
                             -- porting note: the second `Matrix.` was `DMatrix.`
    split_ifs with mp m0 <;> simp only [Matrix.one_apply_eq, Matrix.zero_apply]
  · rw [charmatrix_apply_ne _ _ _ hij, AlgHom.map_neg, expand_C, coeff_neg, coeff_C]
    split_ifs with m0 mp <;>
      -- porting note: again, the first `Matrix.` that was `DMatrix.`
      simp only [hij, zero_sub, Matrix.zero_apply, sub_zero, neg_zero, Matrix.one_apply_ne, Ne.def,
        not_false_iff]
set_option linter.uppercaseLean3 false in
#align mat_poly_equiv_eq_X_pow_sub_C matPolyEquiv_eq_x_pow_sub_c

namespace Matrix

/-- Any matrix polynomial `p` is equivalent under evaluation to `p %ₘ M.charpoly`; that is, `p`
is equivalent to a polynomial with degree less than the dimension of the matrix. -/
theorem aeval_eq_aeval_mod_charpoly (M : Matrix n n R) (p : R[X]) :
    aeval M p = aeval M (p %ₘ M.charpoly) :=
  (aeval_modByMonic_eq_self_of_root M.charpoly_monic M.aeval_self_charpoly).symm
#align matrix.aeval_eq_aeval_mod_charpoly Matrix.aeval_eq_aeval_mod_charpoly

/-- Any matrix power can be computed as the sum of matrix powers less than `Fintype.card n`.

TODO: add the statement for negative powers phrased with `zpow`. -/
theorem pow_eq_aeval_mod_charpoly (M : Matrix n n R) (k : ℕ) :
    M ^ k = aeval M (X ^ k %ₘ M.charpoly) := by rw [← aeval_eq_aeval_mod_charpoly, map_pow, aeval_X]
#align matrix.pow_eq_aeval_mod_charpoly Matrix.pow_eq_aeval_mod_charpoly

end Matrix

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
  · rw [Nat.zero_eq]  -- porting note: `rw [Nat.zero_eq]` was not present
    rw [tsub_zero, pow_one, charmatrix_apply, coeff_sub, ← smul_one_eq_diagonal, smul_apply,
      smul_eq_mul, coeff_X_mul_zero, coeff_C_zero, zero_sub]
    apply neg_mem  -- porting note: was `rw [neg_mem_iff]`, but Lean could not synth `NegMemClass`
    exact h (c i) i
  · rw [Nat.succ_eq_one_add, tsub_self_add, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
#align coeff_charpoly_mem_ideal_pow coeff_charpoly_mem_ideal_pow

end Ideal

namespace Matrix

section reverse

open Polynomial
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
  have ht : t_inv * t = 1 := by rw [← T_add, add_left_neg, T_zero]
  have hp : toLaurentAlg M.charpoly = p := by
    simp [charpoly, charmatrix, AlgHom.map_det, map_sub, map_smul']
  have hq : toLaurentAlg M.charpolyRev = q := by
    simp [charpolyRev, AlgHom.map_det, map_sub, map_smul', smul_eq_diagonal_mul]
  suffices : t_inv ^ Fintype.card n * p = invert q
  · apply toLaurent_injective
    rwa [toLaurent_reverse, ← coe_toLaurentAlg, hp, hq, ← involutive_invert.injective.eq_iff,
      invert.map_mul, involutive_invert p, charpoly_natDegree_eq_dim,
      ← mul_one (Fintype.card n : ℤ), ← T_pow, invert.map_pow, invert_T, mul_comm]
  rw [← det_smul, smul_sub, scalar_apply, ← diagonal_smul, Pi.smul_def, smul_eq_mul, ht,
    diagonal_one, invert.map_det]
  simp [map_smul', smul_eq_diagonal_mul]

@[simp] lemma eval_charpolyRev :
    eval 0 M.charpolyRev = 1 := by
  rw [charpolyRev, ← coe_evalRingHom, RingHom.map_det, ← det_one (R := R) (n := n)]
  have : (1 - (X : R[X]) • M.map C).map (eval 0) = 1 := by
    ext i j; rcases eq_or_ne i j with hij | hij <;> simp [hij]
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
    simp [modByMonic_X]
  have : IsNilpotent (p /ₘ X) :=
    (Polynomial.isUnit_iff'.mp (isUnit_charpolyRev_of_isNilpotent hM)).2
  have aux : (M.charpoly - X ^ (Fintype.card n)).natDegree ≤ M.charpoly.natDegree :=
    le_trans (natDegree_sub_le _ _) (by simp)
  rw [← isNilpotent_reflect_iff aux, reflect_sub, ← reverse, M.reverse_charpoly]
  simpa [hp]

end reverse

end Matrix
