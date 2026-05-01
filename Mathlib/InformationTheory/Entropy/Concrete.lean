/-
Copyright (c) 2026 Essam Abadir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Essam Abadir
-/
module

public import Mathlib.InformationTheory.Entropy.Uniqueness
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Algebra.Order.Ring.Basic

@[expose] public section


/-!
# Concrete Shannon Entropy — All 7 Rota Axioms Proven

This file defines the concrete Shannon entropy function
(`shannonEntropyNNReal`, base-e; `shannonEntropyLog2`, base-2) and
proves that it satisfies all 7 axioms from `HasRotaEntropyAxioms`
(defined in `Axioms.lean`).

## Main definitions

* `shannonEntropyNNReal` — Shannon entropy (base e) as `NNReal`.
* `shannonEntropyBits` — Shannon entropy in bits (base 2) as `NNReal`.
* `shannonEntropyLog2` — alias for `shannonEntropyBits`.
* `shannonEntropyFunction` — an `EntropyFunction` bundling the
  concrete function with its verified axioms.

## Main results

Each `shannonEntropyNNReal_*` theorem converts what was an *axiom*
(assumption) in the uniqueness proof into a *proven property* of the
concrete Shannon entropy:

| Rota axiom (abstract)         | Proven theorem (concrete)                |
|-------------------------------|------------------------------------------|
| `IsEntropyNormalized`         | `shannonEntropyNNReal_normalized`        |
| `IsEntropySymmetric`          | `shannonEntropyNNReal_symmetric`         |
| `IsEntropyZeroInvariant`      | `shannonEntropyNNReal_zeroInvariant`     |
| `IsEntropyContinuous`         | `shannonEntropyNNReal_continuous`        |
| `IsEntropyCondAddSigma`       | `shannonEntropyNNReal_condAddSigma`      |
| `IsEntropyMaxUniform`         | `shannonEntropyNNReal_maxUniform`        |
| `IsEntropyZeroOnEmpty`        | `shannonEntropyNNReal_empty`             |

* `shannonEntropy_chain_rule` — chain rule for Shannon entropy
  over sigma types.
* `shannonEntropy_le_log_card` — Shannon entropy is at most
  `log(card α)`.
* `entropy_fair_coin` — entropy of a fair coin flip is 1 bit.

## Tags

entropy, shannon, information theory, rota
-/

open Finset Real

namespace InformationTheory

-- ==============================================================
-- SECTION: The Canonical Entropy Function
-- ==============================================================

/-- The canonical entropy function is the standard Shannon entropy
in **bits** (base 2). -/
noncomputable def shannonEntropyBits
    {α : Type} [Fintype α] (p : α → NNReal) : NNReal :=
  ((shannonEntropy p) / Real.log 2).toNNReal

/-- The canonical entropy function (base e), as `NNReal`. -/
noncomputable def shannonEntropyNNReal
    {α : Type} [Fintype α] (p : α → NNReal) : NNReal :=
  Real.toNNReal (shannonEntropy p)

-- ==============================================================
-- SECTION: Helper — Shannon entropy is non-negative
-- ==============================================================

/-- `shannonEntropy p ≥ 0` when `p` sums to `1`. -/
lemma shannonEntropy_nonneg_of_sum
    {α : Type*} [Fintype α] (p : α → NNReal)
    (hp_sum_1 : ∑ i, p i = 1) :
    0 ≤ shannonEntropy p := by
  apply Finset.sum_nonneg
  intro i _
  apply Real.negMulLog_nonneg
  · exact NNReal.coe_nonneg (p i)
  · rw [← NNReal.coe_one, NNReal.coe_le_coe]
    calc p i ≤ ∑ j, p j :=
          Finset.single_le_sum (fun _ _ => bot_le)
            (Finset.mem_univ i)
      _ = 1 := hp_sum_1

-- ==============================================================
-- SECTION: Proving shannonEntropyNNReal satisfies Rota's Axioms
-- ==============================================================

/-- Shannon entropy (NNReal) is symmetric. -/
theorem shannonEntropyNNReal_symmetric :
    IsEntropySymmetric shannonEntropyNNReal :=
  ⟨by
    intro α β _ _ p_target _ e
    unfold shannonEntropyNNReal
    congr 1
    show shannonEntropy (p_target ∘ e) = shannonEntropy p_target
    exact shannonEntropy_comp_equiv p_target e⟩

/-- Shannon entropy (NNReal) on the empty type is `0`. -/
theorem shannonEntropyNNReal_empty :
    IsEntropyZeroOnEmpty shannonEntropyNNReal :=
  ⟨by
    simp [shannonEntropyNNReal, shannonEntropy, Finset.sum_empty]⟩

/-- Shannon entropy (NNReal) of a single certain outcome is `0`. -/
theorem shannonEntropyNNReal_normalized :
    IsEntropyNormalized shannonEntropyNNReal :=
  ⟨by
    intro p hp_sum_1
    unfold shannonEntropyNNReal
    have h_p_zero_eq_one : p 0 = 1 := by
      have : ∑ i : Fin 1, p i = p 0 := by
        simp [Finset.sum_const, Finset.card_fin]
      rw [← this]
      exact hp_sum_1
    have h_p_eq_one : p = λ _ => 1 := by
      funext i
      rw [Fin.eq_zero i, h_p_zero_eq_one]
    rw [h_p_eq_one]
    simp [shannonEntropy, Real.negMulLog_one,
      Finset.sum_const, Finset.card_fin]⟩

/-- Shannon entropy (NNReal) is invariant under appending a
zero-probability outcome. -/
theorem shannonEntropyNNReal_zeroInvariant :
    IsEntropyZeroInvariant shannonEntropyNNReal :=
  ⟨by
    intro n p_orig hp_sum_1
    simp only [shannonEntropyNNReal]
    congr 1
    dsimp only
    simp only [shannonEntropy]
    rw [Fin.sum_univ_castSucc]
    have h_last_term_zero :
        Real.negMulLog ↑(if h_lt :
          (Fin.last n).val < n then
            p_orig (Fin.castLT (Fin.last n) h_lt)
          else 0) = 0 := by
      simp only [Fin.val_last, lt_irrefl, dif_neg,
        not_false_iff, NNReal.coe_zero,
        Real.negMulLog_zero]
    rw [h_last_term_zero, add_zero]
    apply Finset.sum_congr rfl
    intro i _
    have h_cond_true : i.castSucc.val < n := i.is_lt
    rw [dif_pos h_cond_true]
    rw [Fin.castLT_castSucc]⟩

/-- Shannon entropy (NNReal) is continuous. -/
theorem shannonEntropyNNReal_continuous :
    IsEntropyContinuous shannonEntropyNNReal :=
  ⟨by
    intro α _inst_fintype p_center hp_sum_1 ε hε_pos
    have h_cont :
        Continuous (fun (p : α → NNReal) =>
          shannonEntropy p) := by
      apply continuous_finset_sum (Finset.univ : Finset α)
      intro i _
      exact Real.continuous_negMulLog.comp
        (continuous_subtype_val.comp (continuous_apply i))
    rw [Metric.continuous_iff] at h_cont
    specialize h_cont p_center ε hε_pos
    rcases h_cont with ⟨δ, hδ_pos, h_ball⟩
    use δ
    constructor
    · exact hδ_pos
    · intro q hq_sum_1 hq_dist
      have H_eq_std (p : α → NNReal)
          (hp_sum : ∑ i, p i = 1) :
          (shannonEntropyNNReal p : ℝ) =
            shannonEntropy p := by
        simp [shannonEntropyNNReal]
        exact shannonEntropy_nonneg_of_sum p hp_sum
      rw [H_eq_std q hq_sum_1,
        H_eq_std p_center hp_sum_1]
      apply h_ball
      rw [dist_pi_lt_iff hδ_pos]
      intro i
      rw [NNReal.dist_eq]
      exact hq_dist i⟩

-- ==============================================================
-- SECTION: Helpers for Chain Rule and Max Uniform
-- ==============================================================

/-- Product rule for `negMulLog`:
`negMulLog(x*y) = y*negMulLog(x) + x*negMulLog(y)`. -/
lemma negMulLog_mul {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.negMulLog (x * y) =
      y * Real.negMulLog x +
        x * Real.negMulLog y := by
  have hxy : 0 < x * y := mul_pos hx hy
  simp only [Real.negMulLog_def, hx.ne', hy.ne', hxy.ne']
  rw [Real.log_mul hx.ne' hy.ne']
  ring

/-- Sum over a sigma type is a double sum. -/
lemma sum_sigma_eq_double_sum {N : ℕ}
    {M_map : Fin N → ℕ}
    (f : (Σ _i : Fin N, Fin (M_map _i)) → ℝ) :
    ∑ x, f x = ∑ i, ∑ j, f ⟨i, j⟩ := by
  exact Finset.sum_sigma Finset.univ
    (fun i => Finset.univ) f

/-- `∑ i, negMulLog(p i) = shannonEntropy p`. -/
lemma sum_negMulLog_eq_shannonEntropy
    {α : Type*} [Fintype α] (p : α → NNReal) :
    ∑ i, negMulLog (p i : ℝ) = shannonEntropy p := by
  simp [shannonEntropy]

/-- Chain rule for Shannon entropy over a sigma type:
`H(P_joint) = H(P_prior) + ∑ᵢ P_prior(i) * H(P_cond_i)`. -/
lemma shannonEntropy_chain_rule {N : ℕ}
    (prior : Fin N → NNReal) (M_map : Fin N → ℕ)
    (P_cond : Π (i : Fin N), (Fin (M_map i) → NNReal))
    (_hprior_sum_1 : ∑ i, prior i = 1)
    (hP_cond_props :
      ∀ i : Fin N, prior i > 0 →
        (∑ j, P_cond i j = 1)) :
    shannonEntropy
        (dependentPairDistSigma prior M_map P_cond) =
      shannonEntropy prior +
        ∑ i, (prior i : ℝ) *
          shannonEntropy (P_cond i) := by
  let P_joint (x : Σ i, Fin (M_map i)) : ℝ :=
    (dependentPairDistSigma prior M_map P_cond x : ℝ)
  let P_prior (i : Fin N) : ℝ := (prior i : ℝ)
  let P_cond_i (i : Fin N) (j : Fin (M_map i)) : ℝ :=
    (P_cond i j : ℝ)
  calc
    shannonEntropy
        (dependentPairDistSigma prior M_map P_cond)
      = ∑ x, (P_joint x).negMulLog := by
        simp only [shannonEntropy, Real.negMulLog_def,
          P_joint]
    _ = ∑ i, ∑ j, (P_joint ⟨i, j⟩).negMulLog := by
        exact sum_sigma_eq_double_sum
          (fun x => (P_joint x).negMulLog)
    _ = ∑ i, ∑ j,
        (P_prior i * P_cond_i i j).negMulLog := by rfl
    _ = ∑ i, ∑ j,
        (P_cond_i i j * (P_prior i).negMulLog +
          P_prior i * (P_cond_i i j).negMulLog) := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      by_cases hp_zero : P_prior i = 0
      · simp [hp_zero, Real.negMulLog_zero]
      by_cases hc_zero : P_cond_i i j = 0
      · simp [hc_zero, Real.negMulLog_zero]
      · have hp_pos : 0 < P_prior i :=
          lt_of_le_of_ne (NNReal.coe_nonneg _)
            (Ne.symm hp_zero)
        have hc_pos : 0 < P_cond_i i j :=
          lt_of_le_of_ne (NNReal.coe_nonneg _)
            (Ne.symm hc_zero)
        rw [negMulLog_mul hp_pos hc_pos]
    _ = (∑ i, ∑ j,
          P_cond_i i j * (P_prior i).negMulLog) +
        (∑ i, ∑ j,
          P_prior i * (P_cond_i i j).negMulLog) := by
      simp_rw [Finset.sum_add_distrib]
    _ = (shannonEntropy prior) +
        (∑ i, (prior i : ℝ) *
          shannonEntropy (P_cond i)) := by
      apply congr_arg₂ (·+·)
      · calc
          ∑ i, ∑ j,
              P_cond_i i j * (P_prior i).negMulLog
            = ∑ i, (∑ j, P_cond_i i j) *
                (P_prior i).negMulLog := by
              simp_rw [Finset.sum_mul]
          _ = ∑ i, 1 * (P_prior i).negMulLog := by
              apply Finset.sum_congr rfl; intro i _
              by_cases hp_zero : prior i = 0
              · simp [P_prior, hp_zero,
                  Real.negMulLog_zero, NNReal.coe_zero]
              · have h_sum_cond_is_1 :
                    ∑ j, P_cond i j = 1 := by
                  exact hP_cond_props i
                    (NNReal.coe_pos.mp
                      (lt_of_le_of_ne
                        (NNReal.coe_nonneg _)
                        (Ne.symm
                          (NNReal.coe_ne_zero.mpr
                            hp_zero))))
                simp [P_cond_i, ← NNReal.coe_sum,
                  h_sum_cond_is_1, NNReal.coe_one]
          _ = shannonEntropy prior := by
              simp only [one_mul, P_prior]
              exact sum_negMulLog_eq_shannonEntropy prior
      · calc
          ∑ i, ∑ j,
              P_prior i * (P_cond_i i j).negMulLog
            = ∑ i, P_prior i *
                (∑ j, (P_cond_i i j).negMulLog) := by
              simp_rw [Finset.mul_sum]
          _ = ∑ i, (prior i : ℝ) *
                shannonEntropy (P_cond i) := by
              apply Finset.sum_congr rfl; intro i _
              simp [P_prior, P_cond_i, shannonEntropy]

/-- The joint distribution `dependentPairDistSigma` sums to `1`. -/
lemma sum_dependentPairDistSigma {N : ℕ}
    (prior : Fin N → NNReal) (M_map : Fin N → ℕ)
    (P_cond : Π i, Fin (M_map i) → NNReal)
    (hprior_sum_1 : ∑ i, prior i = 1)
    (hP_cond_props :
      ∀ i, prior i > 0 → ∑ j, P_cond i j = 1) :
    ∑ x, dependentPairDistSigma prior M_map
      P_cond x = 1 := by
  calc
    ∑ x, dependentPairDistSigma prior M_map P_cond x
      = ∑ i, ∑ j, prior i * P_cond i j := by
        rw [Fintype.sum_sigma, Finset.sum_congr rfl]
        intro i _; rfl
    _ = ∑ i, prior i * (∑ j, P_cond i j) := by
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.mul_sum]
    _ = ∑ i, prior i := by
        apply Finset.sum_congr rfl; intro i _
        by_cases h_prior_zero : prior i = 0
        · simp [h_prior_zero]
        · have h_prior_pos : 0 < prior i := by
            exact lt_of_le_of_ne' bot_le
              h_prior_zero
          have h_sum_cond_is_1 :=
            hP_cond_props i h_prior_pos
          simp [h_sum_cond_is_1]
    _ = 1 := hprior_sum_1

/-- The conditional entropy term is non-negative. -/
lemma condEntropy_term_nonneg {N : ℕ} (i : Fin N)
    (prior : Fin N → NNReal) (M_map : Fin N → ℕ)
    (P_cond : Π i, Fin (M_map i) → NNReal)
    (hP_cond_props :
      ∀ i, prior i > 0 → ∑ j, P_cond i j = 1) :
    0 ≤ (prior i : ℝ) *
      shannonEntropy (P_cond i) := by
  by_cases h_prior_zero : prior i = 0
  · simp [h_prior_zero]
  · have h_prior_pos_real : 0 ≤ (prior i : ℝ) :=
      NNReal.coe_nonneg _
    have h_cond_entropy_nonneg :
        0 ≤ shannonEntropy (P_cond i) := by
      have h_prior_pos : 0 < prior i := by
        exact lt_of_le_of_ne' bot_le
          h_prior_zero
      exact shannonEntropy_nonneg_of_sum (P_cond i)
        (hP_cond_props i h_prior_pos)
    exact mul_nonneg h_prior_pos_real
      h_cond_entropy_nonneg

-- ==============================================================
-- SECTION: The Main Additivity Proof
-- ==============================================================

/-- Shannon entropy (NNReal) satisfies conditional additivity
over sigma types. -/
theorem shannonEntropyNNReal_condAddSigma :
    IsEntropyCondAddSigma shannonEntropyNNReal :=
  ⟨by
    intro N _inst_nezero_N prior M_map P_cond
      hprior_sum_1 hP_cond_props hH_P_cond_zero
    apply NNReal.eq
    simp only [shannonEntropyNNReal]
    have h_joint_nonneg :
        0 ≤ shannonEntropy
          (dependentPairDistSigma prior M_map
            P_cond) := by
      have h_joint_sums_1 :=
        sum_dependentPairDistSigma prior M_map P_cond
          hprior_sum_1
          (fun i h => (hP_cond_props i h).2)
      exact shannonEntropy_nonneg_of_sum _
        h_joint_sums_1
    have h_prior_nonneg :
        0 ≤ shannonEntropy prior :=
      shannonEntropy_nonneg_of_sum _ hprior_sum_1
    rw [Real.toNNReal_of_nonneg h_joint_nonneg,
      Real.toNNReal_of_nonneg h_prior_nonneg]
    simp only [NNReal.coe_add, NNReal.coe_sum,
      NNReal.coe_mul]
    have h_sum_simp :
        ∑ i, (prior i : ℝ) *
          (shannonEntropy (P_cond i)).toNNReal =
        ∑ i, (prior i : ℝ) *
          shannonEntropy (P_cond i) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases h_prior_zero : prior i = 0
      · rw [h_prior_zero, NNReal.coe_zero,
          zero_mul, zero_mul]
      · have h_prior_pos : 0 < prior i :=
          lt_of_le_of_ne' bot_le h_prior_zero
        have h_entropy_nonneg :=
          shannonEntropy_nonneg_of_sum (P_cond i)
            ((hP_cond_props i h_prior_pos).2)
        rw [Real.coe_toNNReal _ h_entropy_nonneg]
    rw [h_sum_simp]
    exact shannonEntropy_chain_rule prior M_map P_cond
      hprior_sum_1
      (fun i h => (hP_cond_props i h).2)⟩

-- ==============================================================
-- SECTION: KL Divergence and Max Uniform
-- ==============================================================

/-- The difference `log n - H(p)` equals the KL divergence sum
`∑ i, p i * log (n * p i)`. -/
lemma entropy_sub_eq_kl_sum
    {α : Type*} [Fintype α] (p : α → NNReal)
    (hp_sum : ∑ i, p i = 1) :
    Real.log (Fintype.card α) - shannonEntropy p =
      ∑ i, (p i : ℝ) *
        Real.log (Fintype.card α * (p i : ℝ)) := by
  let n := Fintype.card α
  calc
    Real.log n - shannonEntropy p
      = (∑ i, (p i : ℝ)) * Real.log n -
          shannonEntropy p := by
        rw [← NNReal.coe_sum, hp_sum,
          NNReal.coe_one, one_mul]
    _ = (∑ i, (p i : ℝ) * Real.log n) -
          ∑ i, Real.negMulLog (p i : ℝ) := by
        simp [shannonEntropy]
        rw [Finset.sum_mul]
    _ = ∑ i, ((p i : ℝ) * Real.log n -
          Real.negMulLog (p i : ℝ)) := by
        rw [Finset.sum_sub_distrib]
    _ = ∑ i, (p i : ℝ) *
          Real.log (n * (p i : ℝ)) := by
        apply sum_congr rfl; intro i _
        by_cases h_pi_zero : p i = 0
        · simp [h_pi_zero, negMulLog_zero]
        · have h_pi_pos : 0 < (p i : ℝ) :=
            NNReal.coe_pos.mpr
              (lt_of_le_of_ne' bot_le h_pi_zero)
          have hn_pos_real : 0 < (n : ℝ) :=
            Nat.cast_pos.mpr
              (Fintype.card_pos_iff.mpr ⟨i⟩)
          simp [negMulLog_def, h_pi_pos.ne']
          rw [← mul_add]
          rw [← Real.log_mul hn_pos_real.ne'
            h_pi_pos.ne']

/-- The KL divergence sum is non-negative (Gibbs' inequality). -/
lemma kl_sum_nonneg
    {α : Type*} [Fintype α] [Nonempty α]
    (p : α → NNReal) (hp_sum : ∑ i, p i = 1) :
    0 ≤ ∑ i, (p i : ℝ) *
      Real.log (Fintype.card α * (p i : ℝ)) := by
  let n := Fintype.card α
  let kl_sum := ∑ i, (p i : ℝ) *
    Real.log (n * (p i : ℝ))
  calc
    kl_sum ≥ - ∑ i, (p i : ℝ) *
        ((n * (p i : ℝ))⁻¹ - 1) := by
      simp only [ge_iff_le]
      rw [← neg_neg kl_sum, neg_le_neg_iff]
      rw [← sum_neg_distrib]
      conv_rhs =>
        arg 2; ext i
        ring_nf
      apply sum_le_sum; intro i _
      by_cases h_pi_zero : p i = 0
      · simp [h_pi_zero]
      · rw [← neg_le_neg_iff]
        rw [neg_neg, neg_add, neg_neg]
        have h_pi_pos : (0 : ℝ) < p i :=
          NNReal.coe_pos.mpr
            (lt_of_le_of_ne' bot_le h_pi_zero)
        have h_n_pos : (0 : ℝ) < n :=
          Nat.cast_pos.mpr Fintype.card_pos
        have h_ne_zero : (p i : ℝ) ≠ 0 :=
          ne_of_gt h_pi_pos
        have h_simplify :
            (p i : ℝ) * ((p i : ℝ))⁻¹ = 1 := by
          simp [h_ne_zero]
        rw [h_simplify, one_mul]
        let h_y := n * (p i : ℝ)
        have h_y_pos : 0 < h_y :=
          mul_pos h_n_pos h_pi_pos
        have h_log_lower :
            Real.log h_y ≥ 1 - h_y⁻¹ := by
          have h :=
            Real.one_sub_inv_le_log_of_pos h_y_pos
          simpa [ge_iff_le] using h
        have h_log_bound :
            Real.log h_y - 1 ≥ -h_y⁻¹ := by
          linarith [h_log_lower]
        have h_final :
            (p i : ℝ) * (Real.log h_y - 1) ≥
              -(n : ℝ)⁻¹ := by
          have h_mul :
              (p i : ℝ) * (Real.log h_y - 1) ≥
                (p i : ℝ) * (-h_y⁻¹) := by
            exact mul_le_mul_of_nonneg_left
              h_log_bound (le_of_lt h_pi_pos)
          rw [mul_neg] at h_mul
          have h_cancel :
              (p i : ℝ) * h_y⁻¹ = (n : ℝ)⁻¹ := by
            simp only [h_y]
            calc
              (p i : ℝ) * (n * (p i : ℝ))⁻¹
                = (p i : ℝ) *
                    ((n : ℝ)⁻¹ * ((p i : ℝ))⁻¹) := by
                  rw [mul_inv_rev]; ring
              _ = ((p i : ℝ) * (n : ℝ)⁻¹) *
                      ((p i : ℝ))⁻¹ := by ring
              _ = (n : ℝ)⁻¹ *
                      ((p i : ℝ) * ((p i : ℝ))⁻¹) := by
                    ring
              _ = (n : ℝ)⁻¹ * 1 := by
                    rw [mul_inv_cancel₀ h_ne_zero]
              _ = (n : ℝ)⁻¹ := by rw [mul_one]
          rw [h_cancel] at h_mul
          exact h_mul
        suffices h_suff :
            -(n : ℝ)⁻¹ ≤ (p i : ℝ) *
              (Real.log (n * (p i : ℝ)) - 1) by
          simp only [h_y] at h_final
          linarith [h_final]
        exact h_final
    _ ≥ 0 := by
        rw [← sum_neg_distrib]
        conv_lhs =>
          arg 2; ext i
          rw [← mul_neg, neg_sub]
        conv_lhs =>
          arg 2; ext i
          rw [mul_sub, mul_one]
        rw [sum_sub_distrib]
        have h_sum_one : ∑ i, (p i : ℝ) = 1 := by
          rw [← NNReal.coe_sum, hp_sum,
            NNReal.coe_one]
        rw [h_sum_one]
        suffices h :
            (∑ i, (p i : ℝ) *
              (n * (p i : ℝ))⁻¹) ≤ 1 by linarith
        set S := Finset.univ.filter
          (fun j => p j ≠ 0) with hS_def
        have h_sum_simplify :
            ∑ i, (p i : ℝ) * (n * (p i : ℝ))⁻¹ =
              S.card * (n : ℝ)⁻¹ := by
          calc
            ∑ i, (p i : ℝ) * (n * (p i : ℝ))⁻¹
              = ∑ i ∈ S,
                  (p i : ℝ) *
                    (n * (p i : ℝ))⁻¹ := by
                symm; apply sum_filter_of_ne
                intro i _ h_ne; contrapose! h_ne
                simp [h_ne]
            _ = ∑ i ∈ S, (n : ℝ)⁻¹ := by
                apply sum_congr rfl; intro i hi
                simp only [hS_def, mem_filter] at hi
                field_simp [NNReal.coe_ne_zero.mpr
                  hi.2, Nat.cast_ne_zero.mpr
                    (ne_of_gt Fintype.card_pos)]
            _ = S.card * (n : ℝ)⁻¹ := by
                simp [sum_const, nsmul_eq_mul]
        rw [h_sum_simplify]
        have h_pos : (0 : ℝ) < n :=
          Nat.cast_pos.mpr Fintype.card_pos
        have h_card_le_n : S.card ≤ n :=
          Finset.card_filter_le _ _
        calc
          (S.card : ℝ) * (n : ℝ)⁻¹
            ≤ (n : ℝ) * (n : ℝ)⁻¹ := by
              apply mul_le_mul_of_nonneg_right
                (Nat.cast_le.mpr h_card_le_n)
                (inv_nonneg.mpr (le_of_lt h_pos))
          _ = 1 := by
              simp [mul_inv_cancel,
                ne_of_gt h_pos]

/-- Shannon entropy is at most `log(card α)`. -/
lemma shannonEntropy_le_log_card
    {α : Type*} [Fintype α] (p : α → NNReal)
    (hp_sum : ∑ i, p i = 1) :
    shannonEntropy p ≤
      Real.log (Fintype.card α) := by
  by_cases h_empty : IsEmpty α
  · exfalso
    have h_zero_sum : ∑ i, p i = 0 := by
      rw [Finset.sum_eq_zero]
      intro i hi
      exact False.elim (h_empty.false i)
    rw [h_zero_sum] at hp_sum
    exact zero_ne_one hp_sum
  · haveI : Nonempty α := not_isEmpty_iff.mp h_empty
    have h :
        0 ≤ Real.log (Fintype.card α) -
          shannonEntropy p := by
      rw [entropy_sub_eq_kl_sum p hp_sum]
      exact kl_sum_nonneg p hp_sum
    linarith

/-- Shannon entropy (NNReal) is maximised by the uniform
distribution. -/
theorem shannonEntropyNNReal_maxUniform :
    IsEntropyMaxUniform shannonEntropyNNReal :=
  ⟨by
    intro α _inst_fintype h_card_pos p hp_sum_1
    simp only [shannonEntropyNNReal]
    rw [Real.toNNReal_le_toNNReal_iff]
    · rw [shannonEntropy_uniformDist h_card_pos]
      apply shannonEntropy_le_log_card
      exact hp_sum_1
    · have h_uniform_sums :
          ∑ i, uniformDist h_card_pos i = 1 :=
        sum_uniformDist h_card_pos
      exact shannonEntropy_nonneg_of_sum
        (uniformDist h_card_pos) h_uniform_sums⟩

-- ==============================================================
-- SECTION: The Bundled Entropy Function
-- ==============================================================

/-- The canonical Shannon entropy function (base e) as an
`EntropyFunction`, bundling the concrete function with its
verified 7 Rota axioms. -/
noncomputable def shannonEntropyFunction :
    EntropyFunction := {
  H_func := shannonEntropyNNReal,
  props := {
    toIsEntropySymmetric :=
      shannonEntropyNNReal_symmetric,
    toIsEntropyZeroOnEmpty :=
      shannonEntropyNNReal_empty,
    toIsEntropyNormalized :=
      shannonEntropyNNReal_normalized,
    toIsEntropyZeroInvariant :=
      shannonEntropyNNReal_zeroInvariant,
    toIsEntropyContinuous :=
      shannonEntropyNNReal_continuous,
    toIsEntropyCondAddSigma :=
      shannonEntropyNNReal_condAddSigma,
    toIsEntropyMaxUniform :=
      shannonEntropyNNReal_maxUniform,
  }
}

-- ==============================================================
-- SECTION: Base-2 Entropy and Fair Coin
-- ==============================================================

/-- Shannon entropy in base 2 (bits). Alias for
`shannonEntropyBits`. -/
noncomputable def shannonEntropyLog2
    {α : Type} [Fintype α] (p : α → NNReal) :
    NNReal :=
  ((shannonEntropy p) / Real.log 2).toNNReal

/-- The entropy of a fair coin flip is exactly 1 bit. -/
theorem entropy_fair_coin :
    let coin_flip_dist :=
      canonicalUniformDist 2 (by norm_num)
    shannonEntropyLog2 coin_flip_dist = 1 := by
  let coin_flip_dist :=
    canonicalUniformDist 2 (by norm_num)
  simp only [shannonEntropyLog2, coin_flip_dist,
    canonicalUniformDist]
  have h2_pos : (2 : ℕ) > 0 := by norm_num
  have h_uniform_entropy :
      shannonEntropy
        (uniformDist (Fintype.card_fin_pos h2_pos)) =
          log 2 := by
    rw [shannonEntropy_uniformDist
      (Fintype.card_fin_pos h2_pos)]
    simp [Fintype.card_fin]
  rw [h_uniform_entropy]
  have h_log2_ne_zero : log 2 ≠ 0 :=
    ne_of_gt (log_pos (by norm_num : (2 : ℝ) > 1))
  rw [div_self h_log2_ne_zero]
  rw [Real.toNNReal_one]

end InformationTheory
