/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark
-/
import Mathlib.Data.Polynomial.Expand
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Data.Polynomial.Laurent

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
  by_cases i = j <;> simp [h, ← degree_eq_iff_natDegree_eq_of_pos (Nat.succ_pos 0)]
  -- ⊢ natDegree (charmatrix M i j) = if i = j then 1 else 0
  -- ⊢ natDegree (charmatrix M i j) = if i = j then 1 else 0
                     -- 🎉 no goals
                     -- 🎉 no goals
#align charmatrix_apply_nat_degree charmatrix_apply_natDegree

theorem charmatrix_apply_natDegree_le (i j : n) :
    (charmatrix M i j).natDegree ≤ ite (i = j) 1 0 := by
  split_ifs with h <;> simp [h, natDegree_X_sub_C_le]
  -- ⊢ natDegree (charmatrix M i j) ≤ 1
                       -- 🎉 no goals
                       -- 🎉 no goals
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
  -- ⊢ ∑ x in Finset.erase univ (Equiv.refl n), ↑↑(↑Equiv.Perm.sign x) * ∏ x_1 : n, …
  apply Submodule.sum_mem (degreeLT R (Fintype.card n - 1))
  -- ⊢ ∀ (c : n ≃ n), c ∈ Finset.erase univ (Equiv.refl n) → ↑↑(↑Equiv.Perm.sign c) …
  intro c hc; rw [← C_eq_int_cast, C_mul']
  -- ⊢ ↑↑(↑Equiv.Perm.sign c) * ∏ x : n, charmatrix M (↑c x) x ∈ degreeLT R (Fintyp …
              -- ⊢ ↑↑(↑Equiv.Perm.sign c) • ∏ x : n, charmatrix M (↑c x) x ∈ degreeLT R (Fintyp …
  apply Submodule.smul_mem (degreeLT R (Fintype.card n - 1)) ↑↑(Equiv.Perm.sign c)
  -- ⊢ ∏ x : n, charmatrix M (↑c x) x ∈ degreeLT R (Fintype.card n - 1)
  rw [mem_degreeLT]
  -- ⊢ degree (∏ x : n, charmatrix M (↑c x) x) < ↑(Fintype.card n - 1)
  apply lt_of_le_of_lt degree_le_natDegree _
  -- ⊢ ↑(natDegree (∏ x : n, charmatrix M (↑c x) x)) < ↑(Fintype.card n - 1)
  rw [Nat.cast_withBot, Nat.cast_withBot] -- porting note: added
  -- ⊢ ↑(natDegree (∏ x : n, charmatrix M (↑c x) x)) < ↑(Fintype.card n - 1)
  rw [WithBot.coe_lt_coe]
  -- ⊢ natDegree (∏ x : n, charmatrix M (↑c x) x) < Fintype.card n - 1
  apply lt_of_le_of_lt _ (Equiv.Perm.fixed_point_card_lt_of_ne_one (ne_of_mem_erase hc))
  -- ⊢ natDegree (∏ x : n, charmatrix M (↑c x) x) ≤ card (filter (fun x => ↑c x = x …
  apply le_trans (Polynomial.natDegree_prod_le univ fun i : n => charmatrix M (c i) i) _
  -- ⊢ ∑ i : n, natDegree (charmatrix M (↑c i) i) ≤ card (filter (fun x => ↑c x = x …
  rw [card_eq_sum_ones]; rw [sum_filter]; apply sum_le_sum
  -- ⊢ ∑ i : n, natDegree (charmatrix M (↑c i) i) ≤ ∑ x in filter (fun x => ↑c x =  …
                         -- ⊢ ∑ i : n, natDegree (charmatrix M (↑c i) i) ≤ ∑ a : n, if ↑c a = a then 1 els …
                                          -- ⊢ ∀ (i : n), i ∈ univ → natDegree (charmatrix M (↑c i) i) ≤ if ↑c i = i then 1 …
  intros
  -- ⊢ natDegree (charmatrix M (↑c i✝) i✝) ≤ if ↑c i✝ = i✝ then 1 else 0
  apply charmatrix_apply_natDegree_le
  -- 🎉 no goals
#align matrix.charpoly_sub_diagonal_degree_lt Matrix.charpoly_sub_diagonal_degree_lt

theorem charpoly_coeff_eq_prod_coeff_of_le {k : ℕ} (h : Fintype.card n - 1 ≤ k) :
    M.charpoly.coeff k = (∏ i : n, (X - C (M i i))).coeff k := by
  apply eq_of_sub_eq_zero; rw [← coeff_sub]
  -- ⊢ coeff (charpoly M) k - coeff (∏ i : n, (X - ↑C (M i i))) k = 0
                           -- ⊢ coeff (charpoly M - ∏ i : n, (X - ↑C (M i i))) k = 0
  apply Polynomial.coeff_eq_zero_of_degree_lt
  -- ⊢ degree (charpoly M - ∏ i : n, (X - ↑C (M i i))) < ↑k
  apply lt_of_lt_of_le (charpoly_sub_diagonal_degree_lt M) ?_
  -- ⊢ ↑(Fintype.card n - 1) ≤ ↑k
  rw [Nat.cast_withBot, Nat.cast_withBot] -- porting note: added
  -- ⊢ ↑(Fintype.card n - 1) ≤ ↑k
  rw [WithBot.coe_le_coe]; apply h
  -- ⊢ Fintype.card n - 1 ≤ k
                           -- 🎉 no goals
#align matrix.charpoly_coeff_eq_prod_coeff_of_le Matrix.charpoly_coeff_eq_prod_coeff_of_le

theorem det_of_card_zero (h : Fintype.card n = 0) (M : Matrix n n R) : M.det = 1 := by
  rw [Fintype.card_eq_zero_iff] at h
  -- ⊢ det M = 1
  suffices M = 1 by simp [this]
  -- ⊢ M = 1
  ext i
  -- ⊢ M i x✝ = OfNat.ofNat 1 i x✝
  exact h.elim i
  -- 🎉 no goals
#align matrix.det_of_card_zero Matrix.det_of_card_zero

theorem charpoly_degree_eq_dim [Nontrivial R] (M : Matrix n n R) :
    M.charpoly.degree = Fintype.card n := by
  by_cases h : Fintype.card n = 0
  -- ⊢ degree (charpoly M) = ↑(Fintype.card n)
  · rw [h]
    -- ⊢ degree (charpoly M) = ↑0
    unfold charpoly
    -- ⊢ degree (det (charmatrix M)) = ↑0
    rw [det_of_card_zero]
    -- ⊢ degree 1 = ↑0
    · simp
      -- 🎉 no goals
    · assumption
      -- 🎉 no goals
  rw [← sub_add_cancel M.charpoly (∏ i : n, (X - C (M i i)))]
  -- ⊢ degree (charpoly M - ∏ i : n, (X - ↑C (M i i)) + ∏ i : n, (X - ↑C (M i i)))  …
  -- porting note: added `↑` in front of `Fintype.card n`
  have h1 : (∏ i : n, (X - C (M i i))).degree = ↑(Fintype.card n) := by
    rw [degree_eq_iff_natDegree_eq_of_pos (Nat.pos_of_ne_zero h), natDegree_prod']
    simp_rw [natDegree_X_sub_C]
    rw [← Finset.card_univ, sum_const, smul_eq_mul, mul_one]
    simp_rw [(monic_X_sub_C _).leadingCoeff]
    simp
  rw [degree_add_eq_right_of_degree_lt]
  -- ⊢ degree (∏ i : n, (X - ↑C (M i i))) = ↑(Fintype.card n)
  exact h1
  -- ⊢ degree (charpoly M - ∏ i : n, (X - ↑C (M i i))) < degree (∏ i : n, (X - ↑C ( …
  rw [h1]
  -- ⊢ degree (charpoly M - ∏ i : n, (X - ↑C (M i i))) < ↑(Fintype.card n)
  apply lt_trans (charpoly_sub_diagonal_degree_lt M)
  -- ⊢ ↑(Fintype.card n - 1) < ↑(Fintype.card n)
  rw [Nat.cast_withBot, Nat.cast_withBot] -- porting note: added
  -- ⊢ ↑(Fintype.card n - 1) < ↑(Fintype.card n)
  rw [WithBot.coe_lt_coe]
  -- ⊢ Fintype.card n - 1 < Fintype.card n
  rw [← Nat.pred_eq_sub_one]
  -- ⊢ Nat.pred (Fintype.card n) < Fintype.card n
  apply Nat.pred_lt
  -- ⊢ Fintype.card n ≠ 0
  apply h
  -- 🎉 no goals
#align matrix.charpoly_degree_eq_dim Matrix.charpoly_degree_eq_dim

theorem charpoly_natDegree_eq_dim [Nontrivial R] (M : Matrix n n R) :
    M.charpoly.natDegree = Fintype.card n :=
  natDegree_eq_of_degree_eq_some (charpoly_degree_eq_dim M)
#align matrix.charpoly_nat_degree_eq_dim Matrix.charpoly_natDegree_eq_dim

theorem charpoly_monic (M : Matrix n n R) : M.charpoly.Monic := by
  nontriviality R -- porting note: was simply `nontriviality`
  -- ⊢ Monic (charpoly M)
  by_cases h : Fintype.card n = 0
  -- ⊢ Monic (charpoly M)
  · rw [charpoly, det_of_card_zero h]
    -- ⊢ Monic 1
    apply monic_one
    -- 🎉 no goals
  have mon : (∏ i : n, (X - C (M i i))).Monic := by
    apply monic_prod_of_monic univ fun i : n => X - C (M i i)
    simp [monic_X_sub_C]
  rw [← sub_add_cancel (∏ i : n, (X - C (M i i))) M.charpoly] at mon
  -- ⊢ Monic (charpoly M)
  rw [Monic] at *
  -- ⊢ leadingCoeff (charpoly M) = 1
  rwa [leadingCoeff_add_of_degree_lt] at mon
  -- ⊢ degree (∏ i : n, (X - ↑C (M i i)) - charpoly M) < degree (charpoly M)
  rw [charpoly_degree_eq_dim]
  -- ⊢ degree (∏ i : n, (X - ↑C (M i i)) - charpoly M) < ↑(Fintype.card n)
  rw [← neg_sub]
  -- ⊢ degree (-(charpoly M - ∏ i : n, (X - ↑C (M i i)))) < ↑(Fintype.card n)
  rw [degree_neg]
  -- ⊢ degree (charpoly M - ∏ i : n, (X - ↑C (M i i))) < ↑(Fintype.card n)
  apply lt_trans (charpoly_sub_diagonal_degree_lt M)
  -- ⊢ ↑(Fintype.card n - 1) < ↑(Fintype.card n)
  rw [Nat.cast_withBot, Nat.cast_withBot] -- porting note: added
  -- ⊢ ↑(Fintype.card n - 1) < ↑(Fintype.card n)
  rw [WithBot.coe_lt_coe]
  -- ⊢ Fintype.card n - 1 < Fintype.card n
  rw [← Nat.pred_eq_sub_one]
  -- ⊢ Nat.pred (Fintype.card n) < Fintype.card n
  apply Nat.pred_lt
  -- ⊢ Fintype.card n ≠ 0
  apply h
  -- 🎉 no goals
#align matrix.charpoly_monic Matrix.charpoly_monic

theorem trace_eq_neg_charpoly_coeff [Nonempty n] (M : Matrix n n R) :
    trace M = -M.charpoly.coeff (Fintype.card n - 1) := by
  rw [charpoly_coeff_eq_prod_coeff_of_le _ le_rfl, Fintype.card,
    prod_X_sub_C_coeff_card_pred univ (fun i : n => M i i) Fintype.card_pos, neg_neg, trace]
  simp_rw [diag_apply]
  -- 🎉 no goals
#align matrix.trace_eq_neg_charpoly_coeff Matrix.trace_eq_neg_charpoly_coeff

-- I feel like this should use `Polynomial.algHom_eval₂_algebraMap`
theorem matPolyEquiv_eval (M : Matrix n n R[X]) (r : R) (i j : n) :
    (matPolyEquiv M).eval ((scalar n) r) i j = (M i j).eval r := by
  unfold Polynomial.eval
  -- ⊢ eval₂ (RingHom.id ((fun x => Matrix n n R) r)) (↑(scalar n) r) (↑matPolyEqui …
  rw [Polynomial.eval₂_def, Polynomial.eval₂_def]  -- porting note: was `unfold eval₂`
  -- ⊢ sum (↑matPolyEquiv M) (fun e a => ↑(RingHom.id ((fun x => Matrix n n R) r))  …
  trans Polynomial.sum (matPolyEquiv M) fun (e : ℕ) (a : Matrix n n R) => (a * (scalar n) r ^ e) i j
  -- ⊢ sum (↑matPolyEquiv M) (fun e a => ↑(RingHom.id ((fun x => Matrix n n R) r))  …
  · unfold Polynomial.sum
    -- ⊢ Finset.sum (support (↑matPolyEquiv M)) (fun n_1 => (fun e a => ↑(RingHom.id  …
    simp only [sum_apply]
    -- ⊢ ∑ c in support (↑matPolyEquiv M), (↑(RingHom.id (Matrix n n R)) (coeff (↑mat …
    dsimp
    -- 🎉 no goals
  · simp_rw [← RingHom.map_pow, ← (scalar.commute _ _).eq]
    -- ⊢ (sum (↑matPolyEquiv M) fun e a => (↑(scalar n) (r ^ e) * a) i j) = sum (M i  …
    simp only [coe_scalar, Matrix.one_mul, RingHom.id_apply, Pi.smul_apply, smul_eq_mul,
      Algebra.smul_mul_assoc]
    -- porting note: the `have` was present and unused also in the original
    --have h : ∀ x : ℕ, (fun (e : ℕ) (a : R) => r ^ e * a) x 0 = 0 := by simp
    simp only [Polynomial.sum, matPolyEquiv_coeff_apply, mul_comm]
    -- ⊢ ∑ x in support (↑matPolyEquiv M), (r ^ x • coeff (↑matPolyEquiv M) x) i j =  …
    simp only [smul_apply, matPolyEquiv_coeff_apply, smul_eq_mul]  -- porting note: added
    -- ⊢ ∑ x in support (↑matPolyEquiv M), r ^ x * coeff (M i j) x = ∑ x in support ( …
    apply (Finset.sum_subset (support_subset_support_matPolyEquiv _ _ _) _).symm
    -- ⊢ ∀ (x : ℕ), x ∈ support (↑matPolyEquiv M) → ¬x ∈ support (M i j) → r ^ x * co …
    intro n _hn h'n
    -- ⊢ r ^ n * coeff (M i j) n = 0
    rw [not_mem_support_iff] at h'n
    -- ⊢ r ^ n * coeff (M i j) n = 0
    simp only [h'n, zero_mul]
    -- ⊢ r ^ n * 0 = 0
    simp only [mul_zero]  -- porting note: added
    -- 🎉 no goals
#align matrix.mat_poly_equiv_eval Matrix.matPolyEquiv_eval

theorem eval_det (M : Matrix n n R[X]) (r : R) :
    Polynomial.eval r M.det = (Polynomial.eval (scalar n r) (matPolyEquiv M)).det := by
  rw [Polynomial.eval, ← coe_eval₂RingHom, RingHom.map_det]
  -- ⊢ det (↑(RingHom.mapMatrix (eval₂RingHom (RingHom.id R) r)) M) = det (eval (↑( …
  apply congr_arg det
  -- ⊢ ↑(RingHom.mapMatrix (eval₂RingHom (RingHom.id R) r)) M = eval (↑(scalar n) r …
  ext
  -- ⊢ ↑(RingHom.mapMatrix (eval₂RingHom (RingHom.id R) r)) M i✝ x✝ = eval (↑(scala …
  symm
  -- ⊢ eval (↑(scalar n) r) (↑matPolyEquiv M) i✝ x✝ = ↑(RingHom.mapMatrix (eval₂Rin …
  -- porting note: `exact` was `convert`
  exact matPolyEquiv_eval _ _ _ _
  -- 🎉 no goals
#align matrix.eval_det Matrix.eval_det

theorem det_eq_sign_charpoly_coeff (M : Matrix n n R) :
    M.det = (-1) ^ Fintype.card n * M.charpoly.coeff 0 := by
  rw [coeff_zero_eq_eval_zero, charpoly, eval_det, matPolyEquiv_charmatrix, ← det_smul]
  -- ⊢ det M = det (-1 • eval (↑(scalar n) 0) (X - ↑C M))
  simp
  -- 🎉 no goals
#align matrix.det_eq_sign_charpoly_coeff Matrix.det_eq_sign_charpoly_coeff

end Matrix

variable {p : ℕ} [Fact p.Prime]

theorem matPolyEquiv_eq_x_pow_sub_c {K : Type*} (k : ℕ) [Field K] (M : Matrix n n K) :
    matPolyEquiv ((expand K k : K[X] →+* K[X]).mapMatrix (charmatrix (M ^ k))) =
      X ^ k - C (M ^ k) := by
  -- porting note: `i` and `j` are used later on, but were not mentioned in mathlib3
  ext m i j
  -- ⊢ coeff (↑matPolyEquiv (↑(RingHom.mapMatrix ↑(expand K k)) (charmatrix (M ^ k) …
  rw [coeff_sub, coeff_C, matPolyEquiv_coeff_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    AlgHom.coe_toRingHom, DMatrix.sub_apply, coeff_X_pow]
  by_cases hij : i = j
  -- ⊢ coeff (↑(expand K k) (charmatrix (M ^ k) i j)) m = ite (m = k) 1 0 i j - ite …
  · rw [hij, charmatrix_apply_eq, AlgHom.map_sub, expand_C, expand_X, coeff_sub, coeff_X_pow,
      coeff_C]
                             -- porting note: the second `Matrix.` was `DMatrix.`
    split_ifs with mp m0 <;> simp only [Matrix.one_apply_eq, Matrix.zero_apply]
                             -- 🎉 no goals
                             -- 🎉 no goals
                             -- 🎉 no goals
                             -- 🎉 no goals
  · rw [charmatrix_apply_ne _ _ _ hij, AlgHom.map_neg, expand_C, coeff_neg, coeff_C]
    -- ⊢ (-if m = 0 then (M ^ k) i j else 0) = ite (m = k) 1 0 i j - ite (m = 0) (M ^ …
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
                                                -- 🎉 no goals
#align matrix.pow_eq_aeval_mod_charpoly Matrix.pow_eq_aeval_mod_charpoly

end Matrix

section Ideal

theorem coeff_charpoly_mem_ideal_pow {I : Ideal R} (h : ∀ i j, M i j ∈ I) (k : ℕ) :
    M.charpoly.coeff k ∈ I ^ (Fintype.card n - k) := by
  delta charpoly
  -- ⊢ coeff (det (charmatrix M)) k ∈ I ^ (Fintype.card n - k)
  rw [Matrix.det_apply, finset_sum_coeff]
  -- ⊢ ∑ b : Equiv.Perm n, coeff (↑Equiv.Perm.sign b • ∏ i : n, charmatrix M (↑b i) …
  apply sum_mem
  -- ⊢ ∀ (c : Equiv.Perm n), c ∈ univ → coeff (↑Equiv.Perm.sign c • ∏ i : n, charma …
  rintro c -
  -- ⊢ coeff (↑Equiv.Perm.sign c • ∏ i : n, charmatrix M (↑c i) i) k ∈ I ^ (Fintype …
  rw [coeff_smul, Submodule.smul_mem_iff']
  -- ⊢ coeff (∏ i : n, charmatrix M (↑c i) i) k ∈ I ^ (Fintype.card n - k)
  have : ∑ x : n, 1 = Fintype.card n := by rw [Finset.sum_const, card_univ, smul_eq_mul, mul_one]
  -- ⊢ coeff (∏ i : n, charmatrix M (↑c i) i) k ∈ I ^ (Fintype.card n - k)
  rw [← this]
  -- ⊢ coeff (∏ i : n, charmatrix M (↑c i) i) k ∈ I ^ (∑ x : n, 1 - k)
  apply coeff_prod_mem_ideal_pow_tsub
  -- ⊢ ∀ (i : n), i ∈ univ → ∀ (k : ℕ), coeff (charmatrix M (↑c i) i) k ∈ I ^ (1 - k)
  rintro i - (_ | k)
  -- ⊢ coeff (charmatrix M (↑c i) i) Nat.zero ∈ I ^ (1 - Nat.zero)
  · rw [Nat.zero_eq]  -- porting note: `rw [Nat.zero_eq]` was not present
    -- ⊢ coeff (charmatrix M (↑c i) i) 0 ∈ I ^ (1 - 0)
    rw [tsub_zero, pow_one, charmatrix_apply, coeff_sub, coeff_X_mul_zero, coeff_C_zero, zero_sub]
    -- ⊢ -M (↑c i) i ∈ I
    apply neg_mem  -- porting note: was `rw [neg_mem_iff]`, but Lean could not synth `NegMemClass`
    -- ⊢ M (↑c i) i ∈ I
    exact h (c i) i
    -- 🎉 no goals
  · rw [Nat.succ_eq_one_add, tsub_self_add, pow_zero, Ideal.one_eq_top]
    -- ⊢ coeff (charmatrix M (↑c i) i) (1 + k) ∈ ⊤
    exact Submodule.mem_top
    -- 🎉 no goals
#align coeff_charpoly_mem_ideal_pow coeff_charpoly_mem_ideal_pow

end Ideal

section reverse

open Polynomial
open LaurentPolynomial hiding C

/-- The right hand side of the equality in this lemma statement is sometimes called the
"characteristic power series" of a matrix.

It has some advantages over the characteristic polynomial, including the fact that it can be
extended to infinite dimensions (for appropriate operators). -/
lemma Matrix.reverse_charpoly (M : Matrix n n R) :
    M.charpoly.reverse = det (1 - (X : R[X]) • C.mapMatrix M) := by
  nontriviality R
  -- ⊢ reverse (charpoly M) = det (1 - X • ↑(RingHom.mapMatrix C) M)
  let t : R[T;T⁻¹] := T 1
  -- ⊢ reverse (charpoly M) = det (1 - X • ↑(RingHom.mapMatrix C) M)
  let t_inv : R[T;T⁻¹] := T (-1)
  -- ⊢ reverse (charpoly M) = det (1 - X • ↑(RingHom.mapMatrix C) M)
  let p : R[T;T⁻¹] := det (scalar n t - LaurentPolynomial.C.mapMatrix M)
  -- ⊢ reverse (charpoly M) = det (1 - X • ↑(RingHom.mapMatrix C) M)
  let q : R[T;T⁻¹] := det (1 - scalar n t * LaurentPolynomial.C.mapMatrix M)
  -- ⊢ reverse (charpoly M) = det (1 - X • ↑(RingHom.mapMatrix C) M)
  have ht : t_inv * t = 1 := by rw [← T_add, add_left_neg, T_zero]
  -- ⊢ reverse (charpoly M) = det (1 - X • ↑(RingHom.mapMatrix C) M)
  have hp : toLaurentAlg M.charpoly = p := by
    simp [charpoly, charmatrix, AlgHom.map_det, map_sub, map_smul']
  have hq : toLaurentAlg (det (1 - (X : R[X]) • C.mapMatrix M)) = q := by
    simp [AlgHom.map_det, map_sub, map_smul']
  suffices : t_inv ^ Fintype.card n * p = invert q
  -- ⊢ reverse (charpoly M) = det (1 - X • ↑(RingHom.mapMatrix C) M)
  · apply toLaurent_injective
    -- ⊢ ↑toLaurent (reverse (charpoly M)) = ↑toLaurent (det (1 - X • ↑(RingHom.mapMa …
    rwa [toLaurent_reverse, ← coe_toLaurentAlg, hp, hq, ← involutive_invert.injective.eq_iff,
      invert.map_mul, involutive_invert p, charpoly_natDegree_eq_dim,
      ← mul_one (Fintype.card n : ℤ), ← T_pow, invert.map_pow, invert_T, mul_comm]
  rw [← det_smul, smul_sub, coe_scalar, ← smul_assoc, smul_eq_mul, ht, one_smul, invert.map_det]
  -- ⊢ det (1 - t_inv • ↑(RingHom.mapMatrix LaurentPolynomial.C) M) = det (↑(AlgEqu …
  simp [map_smul']
  -- 🎉 no goals

end reverse
