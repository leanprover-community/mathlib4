/-
Copyright (c) 2026 Essam Abadir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Essam Abadir
-/
module
public import Mathlib.InformationTheory.Entropy.Axioms
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.Ring.Nat



/-!
# Rota's Entropy Theorem — Axiomatic Uniqueness Proof

This file is a faithful Lean 4 rendition of the uniqueness-of-entropy proof
from Gian-Carlo Rota and Kenneth Baclawski, *Introduction to Probability and
Random Processes* (1979, Chapter 7; revised 1992, Chapter 8).

## Approach

The proof works entirely with **abstract** entropy functions: it assumes an
`H_func` satisfying the 7 axioms in `HasRotaEntropyAxioms` (defined in
`Axioms.lean`) and derives that H must be a constant multiple of the
logarithm. No concrete Shannon entropy formula is assumed or constructed
here.

## Main definitions

* `rationalDist` -- a rational probability distribution on `Fin n` with natural-number weights.
* `rotaConstant` -- the constant `C` relating `entropyUniform₀` to `Real.log`.
* `EntropyFunction` -- a bundled entropy function with all 7 Rota axioms verified.

## Main results

* `entropyUniform₀_mul` -- `entropyUniform₀` satisfies the Cauchy functional equation.
* `logarithmic_trapping` -- the monotone Cauchy solution is trapped
  between consecutive integer logarithms.
* `rota_uniqueness` / `rota_uniqueness_formula` -- for uniform
  distributions, `H(uniform_n) = C * log n`.
* `H_canonical_uniform_eq_C_shannon` -- the canonical uniform entropy equals `C * Shannon entropy`.

These results establish that any function satisfying Rota's axioms agrees
with Shannon entropy up to a positive scalar — the classical
Rota–Khinchin uniqueness theorem.

## Tags

entropy, rota, uniqueness, information theory
-/

@[expose] public section

open Finset Real NNReal Fin Set Filter Function BigOperators Topology

namespace InformationTheory

/-! ### Rational distribution -/

/-- A rational probability distribution on `Fin n` with weights
`a : Fin n → ℕ` summing to `N_den`. The `i`-th probability is
`a i / N_den`. -/
@[nolint unusedArguments]
noncomputable def rationalDist (n : ℕ) (a : Fin n → ℕ) (N_den : ℕ)
    (_h_sum_a_eq_N : ∑ i, a i = N_den)
    (_hN_den_pos : N_den > 0) : Fin n → NNReal :=
  fun i => (a i : NNReal) / (N_den : NNReal)

/-- The distribution created by `rationalDist` sums to `1`. -/
lemma sum_rationalDist (n : ℕ) (a : Fin n → ℕ) (N_den : ℕ)
    (h_sum_a_eq_N : ∑ i, a i = N_den)
    (hN_den_pos : N_den > 0) :
    ∑ i, (rationalDist n a N_den h_sum_a_eq_N hN_den_pos) i = 1 := by
  simp_rw [rationalDist]
  have hN_den_nnreal_ne_zero : (N_den : NNReal) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hN_den_pos
  rw [show (∑ i : Fin n, (a i : NNReal) / (N_den : NNReal)) =
    (∑ i : Fin n, (a i : NNReal)) / (N_den : NNReal) from by
      simp_rw [div_eq_mul_inv]; rw [Finset.sum_mul]]
  rw [show (∑ i : Fin n, (a i : NNReal)) =
    ((∑ i, a i : ℕ) : NNReal) from by push_cast; rfl]
  rw [h_sum_a_eq_N]
  exact div_self hN_den_nnreal_ne_zero

/-! ### Rota constant -/

/-- The constant `C` relating `entropyUniform₀ H n` to `Real.log n`.
Defined as `(entropyUniform₀ H 2 : ℝ) / Real.log 2` if H is
non-trivial, else `0`. -/
noncomputable def rotaConstant
    {H : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyAxioms H) : ℝ :=
  (entropyUniform₀ hH_axioms 2 : ℝ) / Real.log 2

/-- `rotaConstant` is non-negative. -/
lemma rotaConstant_nonneg
    {H : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyAxioms H) :
    rotaConstant hH_axioms ≥ 0 := by
  rw [rotaConstant]
  have hf02_real_nonneg :
      (entropyUniform₀ hH_axioms 2 : ℝ) ≥ 0 :=
    NNReal.coe_nonneg _
  have hlog2_pos : Real.log 2 > 0 :=
    Real.log_pos (by norm_num : (2 : ℝ) > 1)
  exact div_nonneg hf02_real_nonneg (le_of_lt hlog2_pos)

/-! ### Helper lemmas -/

/-- `(n : NNReal) ≠ 0 ↔ n ≠ 0` for natural numbers. -/
private lemma nnreal_natCast_ne_zero_iff {n : ℕ} :
    (n : NNReal) ≠ 0 ↔ n ≠ 0 := by
  constructor
  · intro h hc; exact h (by simp [hc])
  · intro h hc; exact h (by exact_mod_cast hc)

/-- Inverse of a product equals the product of inverses in `NNReal`. -/
private lemma nnreal_inv_mul_inv_eq_inv_mul
    {a b : NNReal} (ha : a ≠ 0) (hb : b ≠ 0) :
    a⁻¹ * b⁻¹ = (a * b)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  calc a⁻¹ * b⁻¹ * (a * b)
      = (a⁻¹ * a) * (b⁻¹ * b) := by ring
    _ = 1 * 1 := by
        rw [inv_mul_cancel₀ ha, inv_mul_cancel₀ hb]
    _ = 1 := one_mul 1

/-- For any `x ≥ 1` and integer `b ≥ 2`, there exists `k` such that
`b^k ≤ x < b^(k+1)`. -/
private lemma exists_nat_pow_bounds {b : ℕ} {x : ℝ}
    (hb : b ≥ 2) (hx : x ≥ 1) :
    ∃ k : ℕ, (b : ℝ) ^ k ≤ x ∧ x < (b : ℝ) ^ (k + 1) := by
  let k := Nat.floor (Real.logb b x)
  use k
  have hb_real_gt_1 : (b : ℝ) > 1 :=
    Nat.one_lt_cast.mpr (by linarith : b > 1)
  have hb_real_pos : (b : ℝ) > 0 := lt_trans zero_lt_one hb_real_gt_1
  have hx_pos : x > 0 := lt_of_lt_of_le zero_lt_one hx
  have hlogb_nonneg : 0 ≤ Real.logb b x :=
    Real.logb_nonneg hb_real_gt_1 hx
  constructor
  · rw [← Real.rpow_natCast b k]
    rw [← Real.le_logb_iff_rpow_le hb_real_gt_1 hx_pos]
    exact Nat.floor_le hlogb_nonneg
  · rw [← Real.rpow_natCast b (k + 1)]
    rw [← Real.logb_lt_iff_lt_rpow hb_real_gt_1 hx_pos]
    push_cast
    exact Nat.lt_floor_add_one (Real.logb b x)

/-- `1 ≤ (n : ℝ) ^ m` when `n ≥ 1`. -/
private lemma one_le_pow_cast {n m : ℕ} (hn : n ≥ 1) :
    1 ≤ (n : ℝ) ^ m := by
  have hn_real_ge_1 : 1 ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
  exact one_le_pow₀ hn_real_ge_1

/-- `0 < n` from `1 ≤ n`. -/
private lemma pos_of_one_le {n : ℕ} (h : 1 ≤ n) : 0 < n :=
  Nat.lt_of_lt_of_le Nat.zero_lt_one h

/-- Extract `ℕ` bounds from `ℝ` power bounds. -/
private lemma nat_bounds_from_cast_pow_bounds {b k n m : ℕ}
    (h_le_cast : (b : ℝ) ^ k ≤ (n : ℝ) ^ m)
    (h_lt_cast : (n : ℝ) ^ m < (b : ℝ) ^ (k + 1)) :
    b ^ k ≤ n ^ m ∧ n ^ m < b ^ (k + 1) := by
  rw [← Nat.cast_pow, ← Nat.cast_pow] at h_le_cast
  rw [← Nat.cast_pow, ← Nat.cast_pow] at h_lt_cast
  exact ⟨Nat.cast_le.mp h_le_cast, Nat.cast_lt.mp h_lt_cast⟩

/-- If `|x - y| ≤ 1/m` for every `m ≥ 1`, then `x = y`. -/
private lemma eq_of_abs_sub_le_inv_ge_one_nat {x y : ℝ}
    (h_bound : ∀ m : ℕ, m ≥ 1 → |x - y| ≤ 1 / (m : ℝ)) :
    x = y := by
  apply eq_of_forall_dist_le
  intro ε hε_pos
  rw [Real.dist_eq]
  obtain ⟨m, hm_lt⟩ := exists_nat_gt (ε⁻¹)
  have hm_pos : (m : ℝ) > 0 := lt_trans (inv_pos.mpr hε_pos) hm_lt
  have hm_ge1 : m ≥ 1 := by
    rcases m with _ | m
    · simp at hm_pos
    · exact Nat.succ_le_succ (Nat.zero_le _)
  have h1 : |x - y| ≤ 1 / (m : ℝ) := h_bound m hm_ge1
  have h2 : 1 / (m : ℝ) < ε := by
    rw [one_div]
    rw [inv_lt_comm₀ hm_pos hε_pos]
    linarith
  linarith

/-- `∃ k, n ≤ a ^ k` for `a > 1`. -/
private lemma exists_pow_ge {a n : ℕ} (ha : 1 < a) :
    ∃ k : ℕ, n ≤ a ^ k := by
  cases n with
  | zero => use 0; exact Nat.zero_le (a ^ 0)
  | succ n =>
      exact ⟨n + 1, Nat.le_of_lt ((n + 1).lt_pow_self ha)⟩

/-! ### Uniform entropy properties -/

/-- `entropyUniform₀ H 1 = 0`. -/
theorem entropyUniform₀_one
    {H : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyAxioms H) :
    entropyUniform₀ hH_axioms 1 = 0 := by
  have h1_pos : 1 > 0 := Nat.one_pos
  simp only [entropyUniform₀, dif_pos h1_pos]
  simp only [entropyUniform]
  rw [uniformDist_fin_one]
  exact hH_axioms.normalized (fun (_ : Fin 1) => 1) sum_fin_one_eq_one

/-- `entropyUniform₀ H n` is monotone non-decreasing.
Uses `zero_invariance` and `max_uniform` axioms. -/
theorem entropyUniform₀_mono
    {H : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyAxioms H) :
    Monotone (entropyUniform₀ hH_axioms) := by
  apply monotone_nat_of_le_succ
  intro n
  if hn_is_zero : n = 0 then
    rw [hn_is_zero]
    simp [Nat.add_zero]
    have h0_1_eq_0 : entropyUniform₀ hH_axioms 1 = 0 :=
      entropyUniform₀_one hH_axioms
    rw [h0_1_eq_0]
    simp [entropyUniform₀, Nat.not_lt_zero]
  else
    have hn_pos : n > 0 := Nat.pos_of_ne_zero hn_is_zero
    have hn1_pos : n + 1 > 0 := Nat.succ_pos n
    rw [entropyUniform₀, dif_pos hn_pos,
        entropyUniform₀, dif_pos hn1_pos]
    let α_n := Fin n
    have h_card_n_pos : 0 < Fintype.card α_n := by
      unfold α_n
      simp only [Fintype.card_fin, hn_pos]
    let unif_n_dist := uniformDist h_card_n_pos
    let p_ext : Fin (n + 1) → NNReal :=
      fun (i : Fin (n + 1)) =>
        if h_lt : i.val < n then
          unif_n_dist (Fin.castLT i h_lt)
        else 0
    have h_sum_unif_n_dist : (∑ i, unif_n_dist i) = 1 :=
      sum_uniformDist h_card_n_pos
    have h_sum_p_ext_eq_1 : (∑ i, p_ext i) = 1 :=
      sum_ext_zero_eq_one unif_n_dist h_sum_unif_n_dist
    have h_H_p_ext_eq_H_unif_n : H p_ext = H unif_n_dist := by
      exact hH_axioms.zero_invariance unif_n_dist
        h_sum_unif_n_dist
    let α_n1 := Fin (n + 1)
    have h_card_n1_pos : 0 < Fintype.card α_n1 := by
      unfold α_n1
      simp only [Fintype.card_fin, hn1_pos]
    let unif_n1_dist := uniformDist h_card_n1_pos
    have h_H_p_ext_le_H_unif_n1 :
        H p_ext ≤ H unif_n1_dist := by
      exact hH_axioms.max_uniform h_card_n1_pos p_ext
        h_sum_p_ext_eq_1
    change H unif_n_dist ≤ H unif_n1_dist
    rw [← h_H_p_ext_eq_H_unif_n]
    exact h_H_p_ext_le_H_unif_n1

/-! ### Independent-distribution helpers -/

/-- `P(i,j) = prior(i) * q_const(j)` using `dependentPairDistSigma`. -/
@[nolint unusedArguments]
noncomputable def dependentPairDistSigma_of_independent
    {N M : ℕ} [NeZero N] [NeZero M]
    (prior : Fin N → NNReal) (q_const : Fin M → NNReal) :
    (Σ _ : Fin N, Fin M) → NNReal :=
  dependentPairDistSigma prior (fun _ => M) (fun _ => q_const)

/-- If weights `w` sum to `1`, then `∑ w i * C = C`. -/
lemma sum_weighted_constant {β : Type*} [Fintype β]
    {C_val : NNReal} {w : β → NNReal}
    (h_w_sum_1 : ∑ i, w i = 1) :
    (∑ i, w i * C_val) = C_val := by
  rw [← Finset.sum_mul, h_w_sum_1, one_mul]

/-- If `P(j|i) = q_const(j)` (conditional independent of prior index),
then `H(joint) = H(prior) + H(q_const)`. -/
lemma cond_add_for_independent_distributions
    {H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyAxioms H_func)
    {N M : ℕ} [NeZero N] [NeZero M]
    (prior : Fin N → NNReal) (q_const : Fin M → NNReal)
    (hprior_sum_1 : ∑ i, prior i = 1)
    (hq_const_sum_1 : ∑ j, q_const j = 1) :
    H_func (dependentPairDistSigma prior (fun _ => M)
      (fun _ => q_const)) =
      H_func prior + H_func q_const := by
  have hP_cond_props_for_sigma :
      ∀ i : Fin N, prior i > 0 →
        ((fun (_ : Fin N) => M) i > 0 ∧
          ∑ j, (fun (_ : Fin N) => q_const) i j = 1) := by
    intro i_idx _h_prior_i_pos
    constructor
    · simp only [gt_iff_lt]
      exact NeZero.pos M
    · exact hq_const_sum_1
  have hH_P_cond_M_map_zero_is_zero_for_sigma :
      ∀ i : Fin N, (fun (_ : Fin N) => M) i = 0 →
        H_func ((fun (_ : Fin N) => q_const) i) = 0 := by
    intro i_idx h_M_eq_0
    have h_M_ne_zero : M ≠ 0 := NeZero.ne M
    exfalso
    exact h_M_ne_zero h_M_eq_0
  rw [hH_axioms.cond_add_sigma prior (fun _ => M)
    (fun _ => q_const) hprior_sum_1
    hP_cond_props_for_sigma
    hH_P_cond_M_map_zero_is_zero_for_sigma]
  rw [add_left_cancel_iff]
  exact sum_weighted_constant hprior_sum_1

/-- The joint of two independent uniforms is the sigma-type uniform. -/
lemma joint_uniform_is_sigma_uniform
    {N M : ℕ} (hN_pos : N > 0) (hM_pos : M > 0) :
    haveI : NeZero N := NeZero.of_pos hN_pos
    haveI : NeZero M := NeZero.of_pos hM_pos
    let unif_N_dist := uniformDist
      (by simp only [Fintype.card_fin]; exact hN_pos :
        0 < Fintype.card (Fin N))
    let unif_M_dist := uniformDist
      (by simp only [Fintype.card_fin]; exact hM_pos :
        0 < Fintype.card (Fin M))
    let joint_dist :=
      dependentPairDistSigma_of_independent unif_N_dist unif_M_dist
    let sigma_uniform_dist := uniformDist
      (by simp only [Fintype.card_sigma, Fintype.card_fin,
            Finset.sum_const, Finset.card_univ];
          exact Nat.mul_pos hN_pos hM_pos :
        0 < Fintype.card (Σ _ : Fin N, Fin M))
    joint_dist = sigma_uniform_dist := by
  funext sigma_pair
  rcases sigma_pair with ⟨i, j⟩
  simp only [dependentPairDistSigma_of_independent,
    dependentPairDistSigma, uniformDist]
  simp only [Fintype.card_fin, Fintype.card_sigma,
    Finset.sum_const, Finset.card_univ]
  simp [Nat.cast_mul, mul_comm]

/-! ### Multiplicativity of uniform entropy -/

/-- `entropyUniform₀ H (n * m) = entropyUniform₀ H n +
entropyUniform₀ H m` for `n, m > 0`. -/
theorem entropyUniform₀_mul
    {H : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyAxioms H) {n m : ℕ}
    (hn_pos : n > 0) (hm_pos : m > 0) :
    entropyUniform₀ hH_axioms (n * m) =
      entropyUniform₀ hH_axioms n +
        entropyUniform₀ hH_axioms m := by
  have hnm_pos : n * m > 0 := Nat.mul_pos hn_pos hm_pos
  haveI hN_ne_zero : NeZero n := NeZero.of_pos hn_pos
  haveI hM_ne_zero : NeZero m := NeZero.of_pos hm_pos
  haveI hNM_ne_zero : NeZero (n * m) := NeZero.of_pos hnm_pos
  let P_n := uniformDist (Fintype.card_fin_pos hn_pos)
  let P_m := uniformDist (Fintype.card_fin_pos hm_pos)
  let P_nm := uniformDist (Fintype.card_fin_pos hnm_pos)
  let M_map_const_m (_ : Fin n) : ℕ := m
  let P_cond_const_P_m (_ : Fin n) : Fin m → NNReal := P_m
  have h_sum_P_n : ∑ i, P_n i = 1 :=
    sum_uniformDist (Fintype.card_fin_pos hn_pos)
  have h_sum_P_m : ∑ j, P_m j = 1 :=
    sum_uniformDist (Fintype.card_fin_pos hm_pos)
  simp [entropyUniform₀, hn_pos, hm_pos, hnm_pos] at *
  have h_indep :
      H (dependentPairDistSigma P_n M_map_const_m
        P_cond_const_P_m) =
        H P_n + H P_m := by
    simpa using
      (cond_add_for_independent_distributions hH_axioms P_n P_m
        h_sum_P_n h_sum_P_m)
  let U_sigma := uniformDist
    (α := (Σ i : Fin n, Fin m))
    (by
      simp only [Fintype.card_sigma, Fintype.card_fin,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact hnm_pos)
  have h_dep_pair_dist_eq_U_sigma :
      dependentPairDistSigma P_n M_map_const_m
        P_cond_const_P_m = U_sigma := by {
    funext x_sig; rcases x_sig with ⟨i_idx, j_idx⟩;
    conv_lhs =>
      simp only [dependentPairDistSigma, P_n, P_m,
        M_map_const_m, P_cond_const_P_m,
        uniformDist, Fintype.card_fin]
    conv_rhs =>
      simp only [U_sigma, uniformDist, Fintype.card_sigma,
        Fintype.card_fin, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
    have hn_ne : (n : NNReal) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn_pos)
    have hm_ne : (m : NNReal) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hm_pos)
    simpa [Nat.cast_mul] using
      (nnreal_inv_mul_inv_eq_inv_mul
        (a := (n : NNReal)) (b := (m : NNReal)) hn_ne hm_ne)
  }
  let e_final_for_symmetry :
      (Σ i : Fin n, Fin m) ≃ Fin (n * m) :=
    (Equiv.sigmaEquivProd (Fin n) (Fin m)).trans
      finProdFinEquiv
  have sum_U_sigma_is_1 : ∑ x, U_sigma x = 1 := by {
    simp [U_sigma];
    apply sum_uniformDist;
  }
  have h_comp_eq_P_nm :
      (U_sigma ∘ e_final_for_symmetry.symm) = P_nm := by {
    funext y_fin_nm;
    simp only [comp_apply, U_sigma, P_nm, uniformDist]
    simp [inv_eq_iff_eq_inv]
  }
  have h_sym :
      H U_sigma =
        H (U_sigma ∘ e_final_for_symmetry.symm) := by
    simpa using
      (hH_axioms.symmetry U_sigma sum_U_sigma_is_1
        e_final_for_symmetry.symm).symm
  have : H P_nm = H P_n + H P_m := by
    calc
      H P_nm
          = H (U_sigma ∘ e_final_for_symmetry.symm) := by
            simpa [h_comp_eq_P_nm]
      _ = H U_sigma := by
            simpa [h_sym] using (Eq.symm h_sym)
      _ = H (dependentPairDistSigma P_n M_map_const_m
              P_cond_const_P_m) := by
            simpa [h_dep_pair_dist_eq_U_sigma]
      _ = H P_n + H P_m := h_indep
  simpa using this

/-! ### Power law -/

/-- `entropyUniform₀ H (n^(m+1)) =
entropyUniform₀ H (n^m) + entropyUniform₀ H n`. -/
private lemma entropyUniform₀_pow_succ_step
    {H : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyAxioms H) {n m : ℕ}
    (hn_pos : n > 0) (_hm_pos : m > 0) :
    entropyUniform₀ hH_axioms (n ^ (m + 1)) =
      entropyUniform₀ hH_axioms (n ^ m) +
        entropyUniform₀ hH_axioms n := by
  rw [pow_succ' n m]
  have h_pow_nm_pos : n ^ m > 0 := by
    exact Nat.pow_pos hn_pos
  rw [entropyUniform₀_mul hH_axioms hn_pos h_pow_nm_pos]
  rw [add_comm (entropyUniform₀ hH_axioms n)
    (entropyUniform₀ hH_axioms (n ^ m))]

/-- `entropyUniform₀ H (n ^ k) = k * entropyUniform₀ H n`
for `n > 0, k > 0`. -/
theorem entropyUniform₀_pow
    {H : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyAxioms H)
    {n k : ℕ} (hn_pos : n > 0) (hk_pos : k > 0) :
    entropyUniform₀ hH_axioms (n ^ k) =
      (k : NNReal) * entropyUniform₀ hH_axioms n := by
  let P : ℕ → Prop :=
    fun k' ↦ entropyUniform₀ hH_axioms (n ^ k') =
      (k' : NNReal) * entropyUniform₀ hH_axioms n
  have base : P 1 := by
    simp [P, pow_one, Nat.cast_one, one_mul]
  have step : ∀ m, m ≥ 1 → P m → P (m + 1) := by
    intro m hm_ge1 hPm
    have hm_pos : m > 0 := hm_ge1
    have h_rec :=
      entropyUniform₀_pow_succ_step hH_axioms hn_pos hm_pos
    have h_rw :
        entropyUniform₀ hH_axioms (n ^ (m + 1)) =
          (m : NNReal) * entropyUniform₀ hH_axioms n +
            entropyUniform₀ hH_axioms n := by
      rw [h_rec]
      rw [hPm]
    have h_factor :
        (m : NNReal) * entropyUniform₀ hH_axioms n +
          entropyUniform₀ hH_axioms n =
        ((m + 1 : ℕ) : NNReal) *
          entropyUniform₀ hH_axioms n := by
      simpa [one_mul, add_mul, Nat.cast_add,
        Nat.cast_one] using
        congrArg (fun x => x) (rfl :
          (m : NNReal) * entropyUniform₀ hH_axioms n +
            1 * entropyUniform₀ hH_axioms n =
          ((m : NNReal) + 1) *
            entropyUniform₀ hH_axioms n)
    simpa [P] using h_rw.trans h_factor
  have hk_ge1 : k ≥ 1 := Nat.one_le_of_lt hk_pos
  have : P k := Nat.le_induction base step k hk_ge1
  simpa [P] using this

/-! ### Non-triviality lemmas -/

/-- `entropyUniform₀ H n ≥ 0` as `ℝ`. -/
private lemma entropyUniform₀_nonneg
    {H_func : ∀ {α : Type} [Fintype α],
      (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyAxioms H_func) {n : ℕ}
    (_hn_ge1 : n ≥ 1) :
    ((entropyUniform₀ hH_axioms n) : ℝ) ≥ 0 :=
  NNReal.coe_nonneg _

/-- If `entropyUniform₀ H b = 0` for `b ≥ 2`, then
`entropyUniform₀ H 2 = 0`. -/
private lemma entropyUniform₀_two_eq_zero_of_base
    {H_func : ∀ {α : Type} [Fintype α],
      (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyAxioms H_func) {b : ℕ}
    (hb_ge2 : b ≥ 2)
    (hf0b_eq_0 : entropyUniform₀ hH_axioms b = 0) :
    entropyUniform₀ hH_axioms 2 = 0 := by
  have h_mono := entropyUniform₀_mono hH_axioms
  have h_f0_2_ge_0 : entropyUniform₀ hH_axioms 2 ≥ 0 := bot_le
  have h2_le_b : 2 ≤ b := by linarith
  have h_f0_2_le_b :
      entropyUniform₀ hH_axioms 2 ≤
        entropyUniform₀ hH_axioms b :=
    h_mono h2_le_b
  rw [hf0b_eq_0] at h_f0_2_le_b
  exact le_antisymm h_f0_2_le_b h_f0_2_ge_0

/-- If `entropyUniform₀ H 2 = 0`, then
`entropyUniform₀ H (2^k) = 0` for `k ≥ 1`. -/
private lemma entropyUniform₀_pow2_eq_zero
    {H : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyAxioms H) {k : ℕ}
    (hf0_2_eq_0 : entropyUniform₀ hH_axioms 2 = 0)
    (hk_ge1 : k ≥ 1) :
    entropyUniform₀ hH_axioms (2 ^ k) = 0 := by
  have h2_pos : 2 > 0 := by norm_num
  have hk_pos : k > 0 := pos_of_one_le hk_ge1
  have h_pow_law :=
    entropyUniform₀_pow hH_axioms h2_pos hk_pos
  rw [hf0_2_eq_0, mul_zero] at h_pow_law
  exact h_pow_law

/-- If `entropyUniform₀ H (2^k) = 0` for all `k ≥ 1`, then
`entropyUniform₀ H n = 0` for all `n ≥ 1`. -/
private lemma entropyUniform₀_eq_zero_of_pow2_zero
    {H : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyAxioms H)
    (h_all : ∀ k ≥ 1,
      entropyUniform₀ hH_axioms (2 ^ k) = 0)
    {n : ℕ} (hn_ge1 : n ≥ 1) :
    entropyUniform₀ hH_axioms n = 0 := by
  have hn_pos : n > 0 := pos_of_one_le hn_ge1
  rcases @exists_pow_ge 2 n (by norm_num : 1 < 2) with
    ⟨k, h_n_le_2k⟩
  if hn_eq_1 : n = 1 then
    rw [hn_eq_1]
    exact entropyUniform₀_one hH_axioms
  else
    have k_ge_1 : k ≥ 1 := by
      contrapose! hn_eq_1
      have k_eq_zero : k = 0 := (Nat.lt_one_iff.mp hn_eq_1)
      rw [k_eq_zero, pow_zero] at h_n_le_2k
      exact Nat.le_antisymm h_n_le_2k hn_ge1
    have h_f0_n_le_f0_2k :
        entropyUniform₀ hH_axioms n ≤
          entropyUniform₀ hH_axioms (2 ^ k) :=
      (entropyUniform₀_mono hH_axioms) h_n_le_2k
    rw [h_all k k_ge_1] at h_f0_n_le_f0_2k
    exact le_antisymm h_f0_n_le_f0_2k
      (by apply @_root_.zero_le :
        entropyUniform₀ hH_axioms n ≥ 0)

/-- `entropyUniform₀ H b ≠ 0` if `H` is non-trivial and
`b ≥ 2`. -/
lemma entropyUniform₀_pos_of_nontrivial
    {H : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyAxioms H)
    (hH_nontrivial :
      ∃ n' ≥ 1, entropyUniform₀ hH_axioms n' ≠ 0)
    {b : ℕ} (hb_ge2 : b ≥ 2) :
    entropyUniform₀ hH_axioms b ≠ 0 := by
  intro hf0b_eq_0
  have hf0_2_eq_0 : entropyUniform₀ hH_axioms 2 = 0 :=
    entropyUniform₀_two_eq_zero_of_base hH_axioms hb_ge2
      hf0b_eq_0
  have h_all_f0_pow2_zero :
      ∀ k ≥ 1, entropyUniform₀ hH_axioms (2 ^ k) = 0 :=
    fun k hk_ge1 =>
      entropyUniform₀_pow2_eq_zero hH_axioms hf0_2_eq_0
        hk_ge1
  rcases hH_nontrivial with ⟨n', hn'_ge1, h_f0_n'_neq_0⟩
  have h_f0_n'_eq_0 : entropyUniform₀ hH_axioms n' = 0 :=
    entropyUniform₀_eq_zero_of_pow2_zero hH_axioms
      h_all_f0_pow2_zero hn'_ge1
  exact h_f0_n'_neq_0 h_f0_n'_eq_0

/-- If `entropyUniform₀ H n ≠ 0` for `n > 0`, then `H` is
non-trivial. -/
private lemma nontrivial_of_entropyUniform₀_ne_zero
    {H_func : ∀ {α : Type} [Fintype α],
      (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyAxioms H_func)
    {n : ℕ}
    (hf0n_ne_0 : entropyUniform₀ hH_axioms n ≠ 0)
    (hn_pos : n > 0) :
    ∃ n' ≥ 1, entropyUniform₀ hH_axioms n' ≠ 0 := by
  use n; exact ⟨Nat.one_le_of_lt hn_pos, hf0n_ne_0⟩

/-- `0 < entropyUniform₀ H b` as `NNReal` if `H` is non-trivial
and `b ≥ 2`. -/
private lemma entropyUniform₀_pos_nnreal
    {H : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyAxioms H)
    (hH_nontrivial :
      ∃ n' ≥ 1, entropyUniform₀ hH_axioms n' ≠ 0)
    {b : ℕ} (hb_ge2 : b ≥ 2) :
    0 < entropyUniform₀ hH_axioms b := by
  have h_ne_zero : entropyUniform₀ hH_axioms b ≠ 0 :=
    entropyUniform₀_pos_of_nontrivial hH_axioms
      hH_nontrivial hb_ge2
  exact (@_root_.pos_iff_ne_zero _).mpr h_ne_zero

/-! ### Logarithmic trapping -/

/-- Power-and-ratio bounds for the trapping argument. -/
private lemma k_from_trap_bounds_real
    {H : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyAxioms H)
    (hH_nontrivial :
      ∃ n' ≥ 1, entropyUniform₀ hH_axioms n' ≠ 0)
    {n m b : ℕ} (hn_pos : n > 0) (hm_pos : m > 0)
    (hb_ge2 : b ≥ 2) :
    ∃ k : ℕ,
      ((b : ℝ) ^ k ≤ (n : ℝ) ^ m ∧
        (n : ℝ) ^ m < (b : ℝ) ^ (k + 1)) ∧
      (((k : ℝ) / (m : ℝ) ≤
          (entropyUniform₀ hH_axioms n : ℝ) /
            (entropyUniform₀ hH_axioms b : ℝ)) ∧
        ((entropyUniform₀ hH_axioms n : ℝ) /
            (entropyUniform₀ hH_axioms b : ℝ) ≤
          ((k : ℝ) + 1) / (m : ℝ))) := by
  let x_real : ℝ := (n : ℝ) ^ m
  have hx_real_ge_1 : x_real ≥ 1 := by
    exact one_le_pow_cast (Nat.one_le_of_lt hn_pos)
  have hb_real_gt_1 : (b : ℝ) > 1 :=
    Nat.one_lt_cast.mpr (by linarith : b > 1)
  rcases exists_nat_pow_bounds hb_ge2 hx_real_ge_1 with
    ⟨k, h_bk_le_x, h_x_lt_bkp1⟩
  use k
  constructor
  · exact ⟨h_bk_le_x, h_x_lt_bkp1⟩
  · let f0n_nnreal := entropyUniform₀ hH_axioms n
    let f0b_nnreal := entropyUniform₀ hH_axioms b
    let f0_nm_pow_nnreal := entropyUniform₀ hH_axioms (n ^ m)
    let f0_bk_pow_nnreal := entropyUniform₀ hH_axioms (b ^ k)
    let f0_bkp1_pow_nnreal :=
      entropyUniform₀ hH_axioms (b ^ (k + 1))
    have h_nm_pow_pos : n ^ m > 0 := Nat.pow_pos hn_pos
    have h_bk_pow_pos : b ^ k > 0 :=
      Nat.pow_pos (by linarith : b > 0)
    have h_bkp1_pow_pos : b ^ (k + 1) > 0 :=
      Nat.pow_pos (by linarith : b > 0)
    have m_pos_real : (m : ℝ) > 0 :=
      Nat.cast_pos.mpr hm_pos
    have h_nat_bounds : b ^ k ≤ n ^ m ∧ n ^ m < b ^ (k + 1) :=
      nat_bounds_from_cast_pow_bounds h_bk_le_x h_x_lt_bkp1
    have h_nat_le := h_nat_bounds.left
    have h_nat_lt := h_nat_bounds.right
    have h_f0_mono1 :
        f0_bk_pow_nnreal ≤ f0_nm_pow_nnreal :=
      (entropyUniform₀_mono hH_axioms) h_nat_le
    have h_f0_mono2 :
        f0_nm_pow_nnreal ≤ f0_bkp1_pow_nnreal :=
      (entropyUniform₀_mono hH_axioms)
        (Nat.le_of_lt h_nat_lt)
    have pl_nm :
        f0_nm_pow_nnreal = (m : NNReal) * f0n_nnreal :=
      entropyUniform₀_pow hH_axioms hn_pos hm_pos
    have pl_bk :
        f0_bk_pow_nnreal =
          (if k_is_0 : k = 0 then 0
            else (k : NNReal) * f0b_nnreal) := by
      split_ifs with hk_cond
      · change entropyUniform₀ hH_axioms (b ^ k) = 0
        rw [hk_cond, pow_zero]
        exact entropyUniform₀_one hH_axioms
      · change entropyUniform₀ hH_axioms (b ^ k) =
            (k : NNReal) * f0b_nnreal
        exact entropyUniform₀_pow hH_axioms
          (by linarith) (Nat.pos_of_ne_zero hk_cond)
    have pl_bkp1 :
        f0_bkp1_pow_nnreal =
          ((k + 1 : ℕ) : NNReal) * f0b_nnreal :=
      entropyUniform₀_pow hH_axioms
        (by linarith) (Nat.succ_pos k)
    rw [pl_bk, pl_nm] at h_f0_mono1
    rw [pl_nm, pl_bkp1] at h_f0_mono2
    have h_f0b_real_pos : (f0b_nnreal : ℝ) > 0 := by
      simp only [NNReal.coe_pos]
      exact entropyUniform₀_pos_nnreal hH_axioms
        hH_nontrivial hb_ge2
    constructor
    · by_cases hk0_case : k = 0
      · rw [hk0_case] at h_f0_mono1
        simp only [if_pos] at h_f0_mono1
        simp only [hk0_case, Nat.cast_zero, zero_div]
        apply div_nonneg
        · exact NNReal.coe_nonneg f0n_nnreal
        · exact le_of_lt h_f0b_real_pos
      · simp [hk0_case] at h_f0_mono1
        rw [div_le_div_iff₀ m_pos_real h_f0b_real_pos]
        rw [← NNReal.coe_natCast k, ← NNReal.coe_natCast m]
        rw [← NNReal.coe_mul, ← NNReal.coe_mul]
        rw [NNReal.coe_le_coe]
        conv_rhs => rw [mul_comm]
        exact h_f0_mono1
    · rw [div_le_div_iff₀ h_f0b_real_pos m_pos_real]
      rw [mul_comm (f0n_nnreal : ℝ) _]
      rw [← NNReal.coe_natCast m]
      rw [← Nat.cast_add_one k]
      rw [← NNReal.coe_natCast (k + 1)]
      rw [← NNReal.coe_mul, ← NNReal.coe_mul]
      rw [NNReal.coe_le_coe]
      exact h_f0_mono2

/-- `k ≤ logb b X` given `b > 1, X > 0, b^k ≤ X`. -/
private lemma le_logb_rpow_self_of_le {b k X : ℝ}
    (hb_gt_1 : b > 1) (hX_pos : 0 < X)
    (hkX : b ^ k ≤ X) :
    k ≤ Real.logb b X := by
  have b_pos : 0 < b := lt_trans zero_lt_one hb_gt_1
  have b_ne_one : b ≠ 1 := ne_of_gt hb_gt_1
  rw [← Real.logb_rpow b_pos b_ne_one (x := k)]
  apply (Real.logb_le_logb hb_gt_1
    (Real.rpow_pos_of_pos b_pos k) hX_pos).mpr
  exact hkX

/-- `logb b X < k_plus_1` given `b > 1, X > 0,
X < b^(k_plus_1)`. -/
private lemma logb_rpow_self_lt_of_lt {b X k_plus_1 : ℝ}
    (hb_gt_1 : b > 1) (hX_pos : 0 < X)
    (hXlt : X < b ^ k_plus_1) :
    Real.logb b X < k_plus_1 := by
  have b_pos : 0 < b := lt_trans zero_lt_one hb_gt_1
  have b_ne_one : b ≠ 1 := ne_of_gt hb_gt_1
  rw [← Real.logb_rpow b_pos b_ne_one (x := k_plus_1)]
  apply Real.logb_lt_logb hb_gt_1 hX_pos hXlt

/-- Helper for `abs_sub_le_iff`. -/
private structure AbsPair (a b r : ℝ) : Prop where
  left  : a - b ≤ r
  right : b - a ≤ r

private instance {a b r : ℝ} :
    Coe (AbsPair a b r) (a - b ≤ r ∧ b - a ≤ r) where
  coe := fun h => ⟨h.left, h.right⟩

/-- Logarithmic trapping:
`| (entropyUniform₀ H n : ℝ) / (entropyUniform₀ H b : ℝ) -
  logb b n | ≤ 1 / m`. -/
theorem logarithmic_trapping
    {H : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyAxioms H)
    (hH_nontrivial :
      ∃ n' ≥ 1, entropyUniform₀ hH_axioms n' ≠ 0)
    {n m b : ℕ} (hn_pos : n > 0) (hm_pos : m > 0)
    (hb_ge2 : b ≥ 2) :
    |(entropyUniform₀ hH_axioms n : ℝ) /
        (entropyUniform₀ hH_axioms b : ℝ) -
      Real.logb b n| ≤ 1 / (m : ℝ) := by
  rcases k_from_trap_bounds_real
    hH_axioms hH_nontrivial hn_pos hm_pos hb_ge2
    with ⟨k, ⟨h_pow_le_nm, h_nm_lt_pow_kp1⟩,
      ⟨h_f0_ratio_lower_bound, h_f0_ratio_upper_bound⟩⟩
  let f0_ratio :=
    (entropyUniform₀ hH_axioms n : ℝ) /
      (entropyUniform₀ hH_axioms b : ℝ)
  let logb_n_val := Real.logb b n
  let k_real := (k : ℝ)
  let m_real := (m : ℝ)
  have hb_real_gt_1 : (b : ℝ) > 1 :=
    Nat.one_lt_cast.mpr (by linarith : b > 1)
  have hn_real_pos : (n : ℝ) > 0 :=
    Nat.cast_pos.mpr hn_pos
  have hm_real_pos : m_real > 0 :=
    Nat.cast_pos.mpr hm_pos
  have h_k_le_m_logbn :
      k_real ≤ m_real * logb_n_val := by
    rw [← Real.logb_rpow_eq_mul_logb_of_pos hn_real_pos
      (y := m_real)]
    have : (b : ℝ) ^ k_real ≤ (n : ℝ) ^ m_real := by
      simp_rw [k_real, m_real]
      rw [Real.rpow_natCast, Real.rpow_natCast]
      exact h_pow_le_nm
    apply le_logb_rpow_self_of_le hb_real_gt_1
      (Real.rpow_pos_of_pos hn_real_pos m_real) this
  have h_m_logbn_lt_kp1 :
      m_real * logb_n_val < k_real + 1 := by
    rw [← Real.logb_rpow_eq_mul_logb_of_pos hn_real_pos
      (y := m_real)]
    have : (n : ℝ) ^ m_real < (b : ℝ) ^ (k_real + 1) := by
      simp_rw [m_real, k_real]
      rw [Real.rpow_natCast, ← Nat.cast_add_one,
        Real.rpow_natCast]
      exact h_nm_lt_pow_kp1
    apply logb_rpow_self_lt_of_lt hb_real_gt_1
      (Real.rpow_pos_of_pos hn_real_pos m_real) this
  have h_logb_lt_kp1_m :
      logb_n_val < (k_real + 1) / m_real := by
    rw [lt_div_iff₀ hm_real_pos, mul_comm]
    exact h_m_logbn_lt_kp1
  have h_km_le_logb :
      k_real / m_real ≤ logb_n_val := by
    rw [div_le_iff₀ hm_real_pos, mul_comm]
    exact h_k_le_m_logbn
  have h_logb_minus_1m_lt_km :
      logb_n_val - 1 / m_real < k_real / m_real := by
    rw [sub_lt_iff_lt_add]
    rw [show k_real / m_real + 1 / m_real =
      (k_real + 1) / m_real from by ring]
    exact h_logb_lt_kp1_m
  have h_right :
      logb_n_val - f0_ratio ≤ 1 / m_real := by
    have : logb_n_val - f0_ratio < 1 / m_real := by
      linarith [h_logb_minus_1m_lt_km,
        h_f0_ratio_lower_bound]
    exact le_of_lt this
  have h_left :
      f0_ratio - logb_n_val ≤ 1 / m_real := by
    have h_aux :
        f0_ratio ≤ logb_n_val + 1 / m_real := by
      have h2 :
          f0_ratio ≤ (k_real + 1) / m_real :=
        h_f0_ratio_upper_bound
      have h3 :
          (k_real + 1) / m_real ≤
            logb_n_val + 1 / m_real := by
        have h_base :
            k_real + 1 ≤
              m_real * logb_n_val + 1 := by
          linarith
        rw [show logb_n_val + 1 / m_real =
            (m_real * logb_n_val + 1) / m_real by
              field_simp [mul_comm, ne_of_gt hm_real_pos]]
        exact (div_le_div_iff_of_pos_right hm_real_pos).mpr
          h_base
      exact h2.trans h3
    simpa [sub_le_iff_le_add, add_comm] using h_aux
  rw [abs_sub_comm f0_ratio logb_n_val]
  have h_bounds :
      AbsPair logb_n_val f0_ratio (1 / m_real) :=
    ⟨h_right, h_left⟩
  exact abs_sub_le_iff.mpr h_bounds

/-- The ratio `(entropyUniform₀ H n : ℝ) /
(entropyUniform₀ H b : ℝ)` is exactly `logb b n`. -/
theorem entropyUniform₀_ratio_eq_logb
    {H : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyAxioms H)
    (hH_nontrivial :
      ∃ n' ≥ 1, entropyUniform₀ hH_axioms n' ≠ 0)
    {n b : ℕ} (hn_pos : n > 0) (hb_ge2 : b ≥ 2) :
    (entropyUniform₀ hH_axioms n : ℝ) /
      (entropyUniform₀ hH_axioms b : ℝ) =
        Real.logb b n := by
  apply eq_of_abs_sub_le_inv_ge_one_nat
  intro m hm_ge1
  exact logarithmic_trapping hH_axioms hH_nontrivial
    hn_pos (pos_of_one_le hm_ge1) hb_ge2

/-! ### Rota's Uniform Theorem -/

/-- `entropyUniform₀ H n` (coerced to `ℝ`) is
`rotaConstant * Real.log n`. -/
theorem rota_uniqueness_formula
    {H : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyAxioms H) :
    let C_val := rotaConstant hH_axioms
    (C_val ≥ 0 ∧
      ∀ (n : ℕ) (_hn_pos : n > 0),
        (entropyUniform₀ hH_axioms n : ℝ) =
          C_val * Real.log n) := by
  let C_val := rotaConstant hH_axioms
  constructor
  · exact rotaConstant_nonneg hH_axioms
  · intro n hn_pos
    simp_rw [rotaConstant]
    by_cases h_trivial : entropyUniform₀ hH_axioms 2 = 0
    · have hf0n_eq_0_nnreal :
          entropyUniform₀ hH_axioms n = 0 := by
        have h_all_f0_pow2_zero :
            ∀ k ≥ 1, entropyUniform₀ hH_axioms (2 ^ k) = 0 :=
          fun k hk_ge1 =>
            entropyUniform₀_pow2_eq_zero hH_axioms h_trivial hk_ge1
        exact entropyUniform₀_eq_zero_of_pow2_zero hH_axioms
          h_all_f0_pow2_zero (Nat.one_le_of_lt hn_pos)
      have hf02_eq_0_real : (entropyUniform₀ hH_axioms 2 : ℝ) = 0 := by
        simp [h_trivial]
      simp only [hf0n_eq_0_nnreal, NNReal.coe_zero, hf02_eq_0_real, zero_div, zero_mul]
    · have h_nontrivial : ∃ n' ≥ 1, entropyUniform₀ hH_axioms n' ≠ 0 :=
        ⟨2, by norm_num, h_trivial⟩
      let F0N := (entropyUniform₀ hH_axioms n : ℝ)
      let F02 := (entropyUniform₀ hH_axioms 2 : ℝ)
      let LOGN := Real.log n
      let LOG2 := Real.log 2
      change F0N = (F02 / LOG2) * LOGN
      have h_ratio_eq_logb : F0N / F02 = Real.logb 2 n :=
        entropyUniform₀_ratio_eq_logb hH_axioms
          h_nontrivial hn_pos (by norm_num : 2 ≥ 2)
      have hf02_ne_zero : F02 ≠ 0 := by
        exact NNReal.coe_ne_zero.mpr h_trivial
      have hlog2_ne_zero : LOG2 ≠ 0 :=
        ne_of_gt (Real.log_pos (by norm_num : (2 : ℝ) > 1))
      have hn_real_pos : (n : ℝ) > 0 :=
        Nat.cast_pos.mpr hn_pos
      have h2_real_pos : (2 : ℝ) > 0 := by norm_num
      rw [Real.logb] at h_ratio_eq_logb
      rw [div_eq_iff hf02_ne_zero] at h_ratio_eq_logb
      rw [h_ratio_eq_logb]
      ring

/-- **Rota's Uniqueness Theorem**: There exists `C ≥ 0` such that
`entropyUniform₀ H n = C * log n` for all `n > 0`. -/
theorem rota_uniqueness
    {H : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyAxioms H) :
    ∃ C ≥ 0,
      ∀ (n : ℕ) (_hn_pos : n > 0),
        (entropyUniform₀ hH_axioms n : ℝ) =
          C * Real.log n := by
  use rotaConstant hH_axioms
  exact rota_uniqueness_formula hH_axioms

/-! ### Bundled entropy function -/

/-- An `EntropyFunction` bundles `H_func` together with a proof
that it satisfies `HasRotaEntropyAxioms`. -/
structure EntropyFunction where
  /-- The underlying entropy function valued in `NNReal` and parameterised
  by the outcome type. -/
  (H_func : ∀ {α : Type} [Fintype α],
    (α → NNReal) → NNReal)
  /-- Proof that `H_func` satisfies all seven Rota entropy axioms. -/
  (props : HasRotaEntropyAxioms H_func)

/-- Evaluate an `EntropyFunction` and get a `ℝ` value. -/
noncomputable def evalEntropyFunction {ef : EntropyFunction}
    {α : Type} [Fintype α] (p : α → NNReal) : ℝ :=
  (ef.H_func p : ℝ)

/-- The Rota constant associated with an `EntropyFunction`. -/
noncomputable def rotaConstant_of_EntropyFunction
    (ef : EntropyFunction) : ℝ :=
  rotaConstant ef.props

/-! ### Helpers for the rational-distribution case -/

/-- Helper: `M ≠ 0` contradicts `M = 0`. -/
private lemma H_func_of_cond_dist_on_empty_from_false
    {H_func : ∀ {α : Type} [Fintype α],
      (α → NNReal) → NNReal}
    {N M : ℕ} [hM_is_nonzero : NeZero M]
    (q_const : Fin M → NNReal)
    (_i_idx : Fin N)
    (h_M_eq_0 :
      (fun (_ : Fin N) => M) _i_idx = 0) :
    H_func ((fun (_ : Fin N) => q_const) _i_idx) = 0 := by
  simp only at h_M_eq_0
  have h_M_ne_zero : M ≠ 0 := NeZero.ne M
  exfalso
  exact h_M_ne_zero h_M_eq_0

/-- Core conditional distribution definition. If `val = 0`, the
distribution is on `Fin 0`; if `val = k + 1`, it is uniform
on `Fin (k + 1)`. -/
noncomputable def P_cond_sigma_def_core (val : ℕ) :
    Fin val → NNReal :=
  match h : val with
  | 0 => h ▸ (Fin.elim0 : Fin 0 → NNReal)
  | k + 1 => uniformDist (Fintype.card_fin_pos (Nat.succ_pos k))

/-- Conditional distribution for the `i`-th component in Rota's
rational setup. -/
noncomputable def P_cond_sigma_def {n : ℕ}
    (a_map : Fin n → ℕ) (i : Fin n) :
    Fin (a_map i) → NNReal :=
  P_cond_sigma_def_core (a_map i)

/-- `H_func` evaluated on `P_cond_sigma_def` is
`entropyUniform₀ hH` at the same cardinality. -/
private lemma H_func_P_cond_sigma_def_eq_entropyUniform₀
    {n : ℕ}
    (H_func : ∀ {α : Type} [Fintype α],
      (α → NNReal) → NNReal)
    (hH : HasRotaEntropyAxioms H_func)
    (a_map : Fin n → ℕ) (i : Fin n)
    {h0 : IsEntropyZeroOnEmpty H_func} :
    H_func (P_cond_sigma_def a_map i) =
      entropyUniform₀ hH (a_map i) := by
  dsimp [P_cond_sigma_def]
  cases h_ai : a_map i with
  | zero =>
      rw [P_cond_sigma_def_core]
      rw [entropyUniform₀, dif_neg (Nat.not_lt_zero 0)]
      rw [h0.apply_to_empty_domain]
  | succ k =>
      rw [P_cond_sigma_def_core]
      have hk_pos : (k.succ) > 0 := Nat.succ_pos k
      rw [entropyUniform₀, dif_pos hk_pos]
      rw [entropyUniform]

private lemma sum_P_cond_sigma_def_eq_one_of_pos {n : ℕ}
    (a_map : Fin n → ℕ) (i : Fin n)
    (ha_i_pos : a_map i > 0) :
    ∑ j, (P_cond_sigma_def a_map i) j = 1 := by
  simp_rw [P_cond_sigma_def, P_cond_sigma_def_core]
  cases h_ai_cases : a_map i with
  | zero =>
      exact (Nat.not_succ_le_zero 0
        (h_ai_cases ▸ ha_i_pos)).elim
  | succ k =>
      simp only [h_ai_cases]
      exact sum_uniformDist (Fintype.card_fin_pos (Nat.succ_pos k))

@[simp] private lemma P_cond_sigma_def_core_eval
    {val : ℕ} :
    (P_cond_sigma_def_core val) =
      (match val with
        | 0 => Fin.elim0
        | m + 1 => fun _j => ((m + 1 : NNReal)⁻¹)) := by
  cases val with
  | zero => simp [P_cond_sigma_def_core]
  | succ m =>
      funext j
      simp [P_cond_sigma_def_core, uniformDist,
        Fintype.card_fin]

@[simp] private lemma uniform_sigma_eval
    {n : ℕ} {a : Fin n → ℕ} {N : ℕ}
    (h_sum : ∑ k, a k = N) (hN : 0 < N)
    (i : Fin n) (j : Fin (a i)) :
    (uniformDist
      (α := Σ k, Fin (a k))
      (by simpa [Fintype.card_sigma, Fintype.card_fin,
        h_sum] using hN)) ⟨i, j⟩ =
      (N : NNReal)⁻¹ := by
  simp [uniformDist, h_sum]

@[simp] private lemma rational_factor_cancel
    {m N : ℕ} (hm : 0 < m) (hN : 0 < N) :
    ((m : NNReal) / N) * (m : NNReal)⁻¹ =
      (N : NNReal)⁻¹ := by
  have m_ne_zero : (m : NNReal) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hm
  have N_ne_zero : (N : NNReal) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hN
  field_simp [m_ne_zero, N_ne_zero]

@[simp] private lemma P_cond_sigma_def_core_apply_succ
    {k : ℕ} {j : Fin (k.succ)} :
    P_cond_sigma_def_core (k.succ) j =
      ((k.succ : NNReal)⁻¹) := by
  simp [P_cond_sigma_def_core, uniformDist,
    Fintype.card_fin]

private lemma LHS_eval_when_ai_is_succ
    (N_den k : ℕ) (j_val : Fin (k.succ))
    (h_N_den_pos_lemma : N_den > 0) :
    (↑(k.succ) / ↑N_den : NNReal) *
        P_cond_sigma_def_core (k.succ) j_val =
      (N_den : NNReal)⁻¹ := by
  rw [P_cond_sigma_def_core_apply_succ
    (k := k) (j := j_val)]
  have hk_succ_pos_lemma : 0 < k.succ := Nat.succ_pos k
  exact rational_factor_cancel hk_succ_pos_lemma
    h_N_den_pos_lemma

/-- The joint distribution from `rationalDist` and
`P_cond_sigma_def` yields the uniform on `Σ i, Fin (a i)`. -/
private lemma P_joint_sigma_is_uniform_for_rota
    {n : ℕ}
    (a : Fin n → ℕ) (N_den : ℕ)
    (h_sum_a_eq_N : ∑ k, a k = N_den)
    (hN_den_pos : N_den > 0)
    (P_rat : Fin n → NNReal)
    (hP_rat_def :
      P_rat = rationalDist n a N_den h_sum_a_eq_N
        hN_den_pos) :
    dependentPairDistSigma P_rat a (P_cond_sigma_def a) =
      uniformDist
        (α := Σ i : Fin n, Fin (a i))
        (by
          simpa [Fintype.card_sigma, Fintype.card_fin,
            h_sum_a_eq_N]
            using hN_den_pos) := by
  funext x
  rcases x with ⟨i, j⟩
  dsimp [dependentPairDistSigma, P_cond_sigma_def]
  simp_rw [hP_rat_def, rationalDist]
  conv_rhs =>
    rw [uniform_sigma_eval h_sum_a_eq_N hN_den_pos i j]
  have hai_pos : 0 < a i := Fin.pos j
  rcases Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hai_pos) with ⟨k, hk_eq_succ_ai⟩
  revert j
  rw [hk_eq_succ_ai]
  intro j
  exact LHS_eval_when_ai_is_succ N_den k j hN_den_pos

/-- `H_func` applied to the joint distribution is
`entropyUniform₀ hH_axioms N_den`. -/
private lemma H_P_joint_sigma_for_rota_eq_entropyUniform₀
    {n : ℕ} [NeZero n]
    (H_func : ∀ {α_aux : Type} [Fintype α_aux],
      (α_aux → NNReal) → NNReal)
    (hH_axioms : HasRotaEntropyAxioms H_func)
    (a : Fin n → ℕ) (N_den : ℕ)
    (h_sum_a_eq_N : ∑ k, a k = N_den)
    (hN_den_pos : N_den > 0)
    (P_rat : Fin n → NNReal)
    (hP_rat_def :
      P_rat = rationalDist n a N_den h_sum_a_eq_N
        hN_den_pos) :
    H_func (dependentPairDistSigma P_rat a
      (P_cond_sigma_def a)) =
      entropyUniform₀ hH_axioms N_den := by
  rw [P_joint_sigma_is_uniform_for_rota a N_den
    h_sum_a_eq_N hN_den_pos P_rat hP_rat_def]
  rw [entropyUniform₀, dif_pos hN_den_pos, entropyUniform]
  let SigmaType := (Σ i : Fin n, Fin (a i))
  let U_sigma_domain_card_pos :
      0 < Fintype.card SigmaType := by
    rw [Fintype.card_sigma]
    simp_rw [Fintype.card_fin]
    rw [h_sum_a_eq_N]
    exact hN_den_pos
  let U_fin_Nden_domain_card_pos :
      0 < Fintype.card (Fin N_den) := by
    simp only [Fintype.card_fin]
    exact hN_den_pos
  let e_sigma_to_card_sigma :
      SigmaType ≃ Fin (Fintype.card SigmaType) :=
    Fintype.equivFin SigmaType
  have h_card_sigma_eq_N_den :
      Fintype.card SigmaType = N_den := by
    rw [Fintype.card_sigma]
    simp_rw [Fintype.card_fin]
    rw [h_sum_a_eq_N]
  let e_sigma_to_fin_Nden : SigmaType ≃ Fin N_den :=
    e_sigma_to_card_sigma.trans
      (Equiv.cast (congrArg Fin h_card_sigma_eq_N_den))
  have h_dist_equality_with_comp :
      (uniformDist U_sigma_domain_card_pos) =
        (uniformDist U_fin_Nden_domain_card_pos) ∘
          e_sigma_to_fin_Nden := by
    funext x_s
    simp_rw [uniformDist, comp_apply]
    apply inv_inj.mpr
    apply Nat.cast_inj.mpr
    rw [h_card_sigma_eq_N_den]
    rw [Fintype.card_fin]
  rw [h_dist_equality_with_comp]
  let P_target_dist :=
    uniformDist U_fin_Nden_domain_card_pos
  have h_sum_P_target_dist_eq_1 :
      ∑ y, P_target_dist y = 1 :=
    sum_uniformDist U_fin_Nden_domain_card_pos
  exact hH_axioms.symmetry P_target_dist
    h_sum_P_target_dist_eq_1 e_sigma_to_fin_Nden

/-- Rota's intermediate formula for rational probabilities:
`H(P_rat) = entropyUniform₀(N_den) -
∑ (P_rat i) * entropyUniform₀(a i)`. -/
private lemma rota_rational_intermediate_formula
    {n : ℕ} [h_n_ne_zero : NeZero n]
    (H_func : ∀ {α_aux : Type} [Fintype α_aux],
      (α_aux → NNReal) → NNReal)
    (hH_axioms : HasRotaEntropyAxioms H_func)
    (a : Fin n → ℕ) (N_den : ℕ)
    (h_sum_a_eq_N : ∑ k, a k = N_den)
    (hN_den_pos : N_den > 0)
    (P_rat_param : Fin n → NNReal)
    (hP_rat_def :
      P_rat_param = rationalDist n a N_den
        h_sum_a_eq_N hN_den_pos) :
    (H_func P_rat_param : ℝ) =
      (entropyUniform₀ hH_axioms N_den : ℝ) -
        ∑ i : Fin n,
          (P_rat_param i : ℝ) *
            (entropyUniform₀ hH_axioms (a i) : ℝ) := by
  let P_prior_fn := P_rat_param
  let M_map_fn := a
  let P_cond_fn (i_idx : Fin n) :=
    P_cond_sigma_def a i_idx
  have hprior_sum_1 : ∑ i, P_prior_fn i = 1 := by
    dsimp [P_prior_fn]
    rw [hP_rat_def]
    exact sum_rationalDist n a N_den h_sum_a_eq_N hN_den_pos
  have hP_cond_props :
      ∀ i_idx : Fin n, P_prior_fn i_idx > 0 →
        (M_map_fn i_idx > 0 ∧
          ∑ j, P_cond_fn i_idx j = 1) := by
    intro i_idx hP_prior_i_pos
    dsimp [P_prior_fn] at hP_prior_i_pos
    have hai_pos : a i_idx > 0 := by
      rw [hP_rat_def] at hP_prior_i_pos
      simp only [rationalDist] at hP_prior_i_pos
      have hnum_ne_zero : (a i_idx : NNReal) ≠ 0 := by
        have : (a i_idx : NNReal) / (N_den : NNReal) ≠ 0 :=
          ne_of_gt hP_prior_i_pos
        have hN_ne : (N_den : NNReal) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt hN_den_pos)
        simpa [hN_ne] using (div_ne_zero_iff.mp this).1
      have hnum_pos : 0 < (a i_idx : NNReal) := by
        have : (a i_idx : NNReal) ≥ 0 := bot_le
        exact lt_of_le_of_ne this hnum_ne_zero.symm
      exact (by exact_mod_cast hnum_pos)
    constructor
    · exact hai_pos
    · exact sum_P_cond_sigma_def_eq_one_of_pos a i_idx
        hai_pos
  have hH_P_cond_M_map_zero :
      ∀ i_idx : Fin n,
        M_map_fn i_idx = 0 →
          H_func (P_cond_fn i_idx) = 0 := by
    intro i_idx h_M_map_fn_i_idx_eq_zero
    dsimp only [P_cond_fn]
    rw [H_func_P_cond_sigma_def_eq_entropyUniform₀ H_func
      hH_axioms a i_idx
      (h0 := hH_axioms.toIsEntropyZeroOnEmpty)]
    have h_ai_eq_zero : a i_idx = 0 := by
      simpa [M_map_fn] using h_M_map_fn_i_idx_eq_zero
    rw [h_ai_eq_zero]
    simp [entropyUniform₀]
  have h_cond_add_nnreal_stmt :=
    hH_axioms.cond_add_sigma
      P_prior_fn M_map_fn P_cond_fn
      hprior_sum_1 hP_cond_props hH_P_cond_M_map_zero
  rw [H_P_joint_sigma_for_rota_eq_entropyUniform₀ H_func
    hH_axioms a N_den h_sum_a_eq_N hN_den_pos P_rat_param
    hP_rat_def] at h_cond_add_nnreal_stmt
  simp_rw [P_cond_fn,
    fun i => H_func_P_cond_sigma_def_eq_entropyUniform₀
      H_func hH_axioms a i
      (h0 := hH_axioms.toIsEntropyZeroOnEmpty)]
    at h_cond_add_nnreal_stmt
  rw [eq_sub_iff_add_eq']
  calc
    (∑ i, (↑(P_rat_param i) : ℝ) *
        (↑(entropyUniform₀ hH_axioms (a i)) : ℝ)) +
      (↑(H_func P_rat_param) : ℝ)
    _ = (↑(H_func P_rat_param) : ℝ) +
          (∑ i, (↑(P_rat_param i) : ℝ) *
            (↑(entropyUniform₀ hH_axioms (a i)) : ℝ)) := by
        rw [add_comm]
    _ = (↑(H_func P_rat_param) : ℝ) +
          (∑ i, (↑(P_rat_param i *
            entropyUniform₀ hH_axioms (a i)) : ℝ)) := by
        simp_rw [NNReal.coe_mul]
    _ = (↑(H_func P_rat_param) : ℝ) +
          (↑(∑ i, P_rat_param i *
            entropyUniform₀ hH_axioms (a i)) : ℝ) := by
        rw [NNReal.coe_sum]
    _ = (↑((H_func P_rat_param) +
          (∑ i, P_rat_param i *
            entropyUniform₀ hH_axioms (a i))) : ℝ) := by
        rw [NNReal.coe_add]
    _ = (↑(entropyUniform₀ hH_axioms N_den) : ℝ) := by
        rw [← h_cond_add_nnreal_stmt]

/-! ### Shannon-entropy micro-helpers -/

private lemma Real.log_inv_eq_neg_log {x : ℝ}
    (_hx : 0 < x) :
    Real.log (x⁻¹) = -Real.log x := by
  simp [Real.log_inv]

@[simp] private lemma negMulLog_to_mul_log_one_div
    {x_nnreal : NNReal} :
    (negMulLog (x_nnreal : ℝ)) =
      (if (x_nnreal : ℝ) = 0 then 0
        else (x_nnreal : ℝ) *
          Real.log (1 / (x_nnreal : ℝ))) := by
  rw [negMulLog_def]
  split_ifs with h_coe_is_zero
  · simp [h_coe_is_zero]
  · have h_coe_pos : (x_nnreal : ℝ) > 0 := by
      apply lt_of_le_of_ne (NNReal.coe_nonneg x_nnreal)
      exact Ne.symm h_coe_is_zero
    rw [one_div]
    rw [Real.log_inv_eq_neg_log h_coe_pos]
    simp [mul_neg]

private lemma log_one_div_P_rat_to_log_N_sub_log_a
    {n : ℕ} (a : Fin n → ℕ) (N_den : ℕ) (i : Fin n)
    (P_rat_i : NNReal)
    (h_P_rat_i_def_val :
      P_rat_i = (a i : NNReal) / (N_den : NNReal))
    (h_P_rat_i_ne_zero : (P_rat_i : ℝ) ≠ 0)
    (h_N_den_pos : N_den > 0) :
    Real.log (1 / (P_rat_i : ℝ)) =
      Real.log N_den - Real.log (a i : ℝ) := by
  have h_P_rat_i_pos_real : (P_rat_i : ℝ) > 0 :=
    lt_of_le_of_ne (NNReal.coe_nonneg P_rat_i)
      h_P_rat_i_ne_zero.symm
  have h_a_i_pos_nat : a i > 0 := by
    have h_P_rat_i_ne_zero_nnreal : P_rat_i ≠ 0 :=
      NNReal.coe_ne_zero.mp h_P_rat_i_ne_zero
    rw [h_P_rat_i_def_val] at h_P_rat_i_ne_zero_nnreal
    have h_N_den_nnreal_ne_zero : (N_den : NNReal) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt h_N_den_pos)
    rw [div_ne_zero_iff] at h_P_rat_i_ne_zero_nnreal
    exact Nat.pos_of_ne_zero
      (nnreal_natCast_ne_zero_iff.mp
        h_P_rat_i_ne_zero_nnreal.left)
  have h_a_i_pos_real : (a i : ℝ) > 0 :=
    Nat.cast_pos.mpr h_a_i_pos_nat
  have h_N_den_pos_real : (N_den : ℝ) > 0 :=
    Nat.cast_pos.mpr h_N_den_pos
  simp only [h_P_rat_i_def_val, NNReal.coe_div,
    NNReal.coe_natCast]
  have h_num_ne_zero : (↑(a i) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr
      (Nat.pos_iff_ne_zero.mp h_a_i_pos_nat)
  have h_den_ne_zero : (↑N_den : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr
      (Nat.pos_iff_ne_zero.mp h_N_den_pos)
  have key_rewrite :
      1 / ((↑(a i) : ℝ) / (↑N_den : ℝ)) =
        (↑N_den : ℝ) / (↑(a i) : ℝ) :=
    one_div_div (↑(a i) : ℝ) (↑N_den : ℝ)
  rw [key_rewrite]
  apply Real.log_div
  · exact ne_of_gt h_N_den_pos_real
  · exact ne_of_gt h_a_i_pos_real

private lemma P_rat_i_coe_zero_iff_a_i_zero {n : ℕ}
    (a : Fin n → ℕ) (N_den : ℕ) (i : Fin n)
    (P_rat_i : NNReal)
    (h_P_rat_i_def_val :
      P_rat_i = (a i : NNReal) / (N_den : NNReal))
    (h_N_den_pos : N_den > 0) :
    (P_rat_i : ℝ) = 0 ↔ a i = 0 := by
  constructor
  · intro h
    have hNN : P_rat_i = 0 := NNReal.coe_eq_zero.mp h
    rw [h_P_rat_i_def_val] at hNN
    have hN : (N_den : NNReal) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt h_N_den_pos)
    simpa [hN] using div_eq_zero_iff.1 hNN
  · intro ha
    simp [h_P_rat_i_def_val, ha]

private lemma sum_ite_mul_const_right {α : Type*}
    [Fintype α] {β : Type*} [CommSemiring β]
    (P_fn : α → β) (C : β) (cond_fn : α → Prop)
    [DecidablePred cond_fn] :
    (∑ i, (if cond_fn i then 0 else P_fn i * C)) =
      (∑ i, (if cond_fn i then 0 else P_fn i)) * C := by
  calc
    (∑ i, (if cond_fn i then 0 else P_fn i * C))
    _ = ∑ i,
          (if cond_fn i then 0 * C else P_fn i * C) := by
        apply Finset.sum_congr rfl; intro i _
        by_cases h_cond : cond_fn i <;> simp [h_cond]
    _ = ∑ i,
          (if cond_fn i then 0 else P_fn i) * C := by
        simp [ite_mul]
    _ = (∑ i,
          (if cond_fn i then 0 else P_fn i)) * C := by
        rw [Finset.sum_mul]

/-- Main identity: rational-distribution Shannon entropy. -/
private lemma shannonEntropy_rational_identity
    {n : ℕ} [NeZero n]
    (a : Fin n → ℕ) (N_den : ℕ)
    (h_sum : ∑ i, a i = N_den) (hN : 0 < N_den)
    (P : Fin n → NNReal)
    (hP_def :
      P = rationalDist n a N_den h_sum hN) :
    shannonEntropy P =
      Real.log N_den -
        ∑ i, if a i = 0 then 0
          else (P i : ℝ) * Real.log (a i : ℝ) := by
  simp_rw [shannonEntropy, negMulLog_to_mul_log_one_div]
  have step2_sum_eq :
      ∑ i, (if (P i : ℝ) = 0 then 0
        else (P i : ℝ) * Real.log (1 / (P i : ℝ))) =
      ∑ i, (if (P i : ℝ) = 0 then 0
        else (P i : ℝ) *
          (Real.log N_den - Real.log (a i : ℝ))) := by
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with h_Pi_zero
    · rfl
    · apply congr_arg ((P i : ℝ) * ·)
      exact log_one_div_P_rat_to_log_N_sub_log_a a N_den i
        (P i) (by rw [hP_def]; rfl) h_Pi_zero hN
  rw [step2_sum_eq]
  have h_term_sub_distrib (i : Fin n) :
      (if (P i : ℝ) = 0 then 0
        else (P i : ℝ) *
          (Real.log N_den - Real.log (a i : ℝ))) =
      ((if (P i : ℝ) = 0 then 0
          else (P i : ℝ) * Real.log N_den) -
        (if (P i : ℝ) = 0 then 0
          else (P i : ℝ) * Real.log (a i : ℝ))) := by
    split_ifs with h_Pi_zero
    · simp
    · simp [mul_sub]
  simp_rw [h_term_sub_distrib]
  rw [Finset.sum_sub_distrib]
  have h_first_sum_eq_log_Nden :
      (∑ i, (if (P i : ℝ) = 0 then 0
        else (P i : ℝ) * Real.log N_den)) =
          Real.log N_den := by
    rw [sum_ite_mul_const_right (fun i => (P i : ℝ))
      (Real.log N_den) (fun i => (P i : ℝ) = 0)]
    have h_sum_if_P_rat_eq_sum_P_rat :
        (∑ (i : Fin n), if (P i : ℝ) = 0 then 0
          else (P i : ℝ)) =
          (∑ (i : Fin n), (P i : ℝ)) := by
      apply Finset.sum_congr rfl; intro i _;
      by_cases h_prat_i_zero : (P i : ℝ) = 0 <;>
        simp [h_prat_i_zero]
    rw [h_sum_if_P_rat_eq_sum_P_rat]
    have sumP_eq_1 : ∑ i, (P i : ℝ) = 1 := by
      rw [← NNReal.coe_sum, hP_def,
        sum_rationalDist n a N_den h_sum hN,
        NNReal.coe_one]
    rw [sumP_eq_1, one_mul]
  rw [h_first_sum_eq_log_Nden]
  apply congr_arg (Real.log N_den - ·)
  apply Finset.sum_congr rfl; intro i _;
  have h_cond_equiv : ((P i : ℝ) = 0) ↔ (a i = 0) := by
    apply P_rat_i_coe_zero_iff_a_i_zero a N_den i (P i)
    · rw [hP_def]; rfl
    · exact hN
  simp [h_cond_equiv]

/-! ### Micro-helpers for the rational entropy theorem -/

private lemma entropyUniform₀_to_rotaConstant_log
    {n : ℕ}
    {H_func : ∀ {α_aux : Type} [Fintype α_aux],
      (α_aux → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyAxioms H_func)
    (C_const : ℝ) (a_i_val : ℕ) (_i : Fin n)
    (hC_def : C_const = rotaConstant hH_axioms) :
    (entropyUniform₀ hH_axioms a_i_val : ℝ) =
      if a_i_val = 0 then 0
        else C_const * Real.log (a_i_val : ℝ) := by
  rw [hC_def]
  by_cases h_ai_zero : a_i_val = 0
  · rw [if_pos h_ai_zero]
    simp [entropyUniform₀, h_ai_zero, NNReal.coe_zero]
  · rw [if_neg h_ai_zero]
    have h_ai_pos : a_i_val > 0 :=
      Nat.pos_of_ne_zero h_ai_zero
    rw [(rota_uniqueness_formula hH_axioms).right
      a_i_val h_ai_pos]

private lemma sum_Prat_entropyUniform₀_to_sum_Prat_C_log
    {n : ℕ}
    {H_func : ∀ {α_aux : Type} [Fintype α_aux],
      (α_aux → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyAxioms H_func)
    (C_const : ℝ)
    (a : Fin n → ℕ) (P_rat : Fin n → NNReal)
    (hC_def : C_const = rotaConstant hH_axioms) :
    (∑ i, (P_rat i : ℝ) *
      (entropyUniform₀ hH_axioms (a i) : ℝ)) =
    (∑ i, (if a i = 0 then 0
      else (P_rat i : ℝ) *
        (C_const * Real.log (a i : ℝ)))) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [entropyUniform₀_to_rotaConstant_log hH_axioms
    C_const (a i) i hC_def]
  by_cases h_ai_zero : a i = 0
  · simp [h_ai_zero]
  · simp [h_ai_zero]

private lemma sum_Prat_C_log_factor_C {n : ℕ}
    (C_const : ℝ)
    (a : Fin n → ℕ) (P_rat : Fin n → NNReal) :
    (∑ i, (if a i = 0 then 0
      else (P_rat i : ℝ) *
        (C_const * Real.log (a i : ℝ)))) =
    C_const * (∑ i, (if a i = 0 then 0
      else (P_rat i : ℝ) * Real.log (a i : ℝ))) := by
  calc
    (∑ i, (if a i = 0 then 0
      else (P_rat i : ℝ) *
        (C_const * Real.log (a i : ℝ))))
    _ = ∑ i, (if a i = 0 then 0
          else C_const *
            ((P_rat i : ℝ) * Real.log (a i : ℝ))) := by
        apply Finset.sum_congr rfl; intro i _;
        by_cases h_ai_zero : a i = 0
        · simp [h_ai_zero]
        · simp [h_ai_zero]
          ac_rfl
    _ = C_const * (∑ i,
          ite (a i = 0) 0
            ((P_rat i : ℝ) * Real.log (a i : ℝ))) := by
        simp [Finset.mul_sum, mul_ite]
    _ = C_const * (∑ i,
          (if a i = 0 then 0
            else (P_rat i : ℝ) *
              Real.log (a i : ℝ))) := by
        rw [mul_comm]

/-! ### Rational case of Rota's uniqueness -/

/-- Rota's uniqueness for rational distributions:
`(H_func P_rat : ℝ) = C * shannonEntropy P_rat`. -/
theorem RUE_rational_case {n : ℕ} [h_n_ne_zero : NeZero n]
    (H_func : ∀ {α_aux : Type} [Fintype α_aux],
      (α_aux → NNReal) → NNReal)
    (hH_axioms : HasRotaEntropyAxioms H_func)
    (a : Fin n → ℕ) (N_den : ℕ)
    (h_sum_a_eq_N : ∑ i, a i = N_den)
    (hN_den_pos : N_den > 0) :
    let P_rat := rationalDist n a N_den h_sum_a_eq_N
      hN_den_pos
    (H_func P_rat : ℝ) =
      (rotaConstant hH_axioms) *
        shannonEntropy P_rat := by
  let P_rat_val := rationalDist n a N_den h_sum_a_eq_N
    hN_den_pos
  let C_const_val := rotaConstant hH_axioms
  calc
    (H_func P_rat_val : ℝ)
    _ = (entropyUniform₀ hH_axioms N_den : ℝ) -
          ∑ i, (P_rat_val i : ℝ) *
            (entropyUniform₀ hH_axioms (a i) : ℝ) := by
        rw [rota_rational_intermediate_formula H_func
          hH_axioms a N_den h_sum_a_eq_N hN_den_pos
          P_rat_val rfl]
    _ = (C_const_val * Real.log N_den) -
          ∑ i, (P_rat_val i : ℝ) *
            (entropyUniform₀ hH_axioms (a i) : ℝ) := by
        rw [(rota_uniqueness_formula hH_axioms).right
          N_den hN_den_pos]
    _ = (C_const_val * Real.log N_den) -
          (∑ i, (if a i = 0 then 0
            else (P_rat_val i : ℝ) *
              (C_const_val *
                Real.log (a i : ℝ)))) := by
        rw [congr_arg (C_const_val * Real.log N_den - ·)]
        exact sum_Prat_entropyUniform₀_to_sum_Prat_C_log
          hH_axioms C_const_val a P_rat_val rfl
    _ = (C_const_val * Real.log N_den) -
          C_const_val * (∑ i, (if a i = 0 then 0
            else (P_rat_val i : ℝ) *
              Real.log (a i : ℝ))) := by
        rw [congr_arg (C_const_val * Real.log N_den - ·)]
        exact sum_Prat_C_log_factor_C C_const_val a
          P_rat_val
    _ = C_const_val *
          (Real.log N_den - (∑ i, (if a i = 0 then 0
            else (P_rat_val i : ℝ) *
              Real.log (a i : ℝ)))) := by
        rw [← mul_sub]
    _ = C_const_val * shannonEntropy P_rat_val := by
        rw [congr_arg (C_const_val * ·)]
        exact (shannonEntropy_rational_identity a N_den
          h_sum_a_eq_N hN_den_pos P_rat_val rfl).symm

/-- `H_func` on the canonical uniform distribution equals
`C * shannonEntropy`. -/
theorem H_canonical_uniform_eq_C_shannon
    (H_func : ∀ {α_aux : Type} [Fintype α_aux],
      (α_aux → NNReal) → NNReal)
    (hH_axioms : HasRotaEntropyAxioms H_func)
    (k : ℕ) (hk_pos : k > 0) :
    (H_func (canonicalUniformDist k hk_pos) : ℝ) =
      (rotaConstant hH_axioms) *
        shannonEntropy (canonicalUniformDist k hk_pos) := by
  let p_unif_k := canonicalUniformDist k hk_pos
  have h_lhs_eq_entropyUniform₀ :
      (H_func p_unif_k : ℝ) =
        (entropyUniform₀ hH_axioms k : ℝ) := by
    simp only [p_unif_k, canonicalUniformDist, uniformDist,
      Fintype.card_fin_pos, entropyUniform₀, entropyUniform,
      dif_pos hk_pos]
  rw [h_lhs_eq_entropyUniform₀]
  rw [(rota_uniqueness_formula hH_axioms).right k hk_pos]
  rw [shannonEntropy_canonicalUniform k hk_pos]

end InformationTheory
