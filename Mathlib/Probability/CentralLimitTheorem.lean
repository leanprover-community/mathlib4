/-
Copyright (c) 2024 Thomas Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Zhu, Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Central limit theorem

We prove the central limit theorem in dimension 1.

## Main statement

* `tendstoInDistribution_inv_sqrt_mul_sum_sub`: Given a sequence of random variables
  `X : ℕ → Ω → ℝ` that are independent, identically distributed with mean `μ` and variance `v`,
  and a random variable `Y : Ω' → ℝ` following `gaussianReal 0 v`, the sequence
  `n ↦ (√n)⁻¹ * (∑ k ∈ Finset.range n, X k ω - n * μ)` converges to `Y` in distribution.

## Tags

central limit theorem
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Filter
open scoped Real Topology

namespace ProbabilityTheory

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ}

lemma charFun_inv_sqrt_mul_sum (hindep : iIndepFun X P)
    (hident : ∀ (i : ℕ), IdentDistrib (X i) (X 0) P P) {n : ℕ} {t : ℝ} :
    charFun (P.map (fun ω ↦ (√n)⁻¹ * ∑ k ∈ Finset.range n, X k ω)) t =
      (charFun (P.map (X 0)) ((√n)⁻¹ * t)) ^ n := by
  have mX n := (hident n).aemeasurable_fst
  rw [charFun_map_mul_comp, (hindep.restrict _).charFun_map_fun_finset_sum_eq_prod (fun _ _ ↦ mX _)]
  · simp [fun i ↦ (hident i).map_eq]
  · exact Finset.aemeasurable_fun_sum _ fun _ _ ↦ mX _

variable [IsProbabilityMeasure P]

lemma tendsto_charFun_inv_sqrt_mul_pow {X : Ω → ℝ}
    (hX : AEMeasurable X P) (h0 : P[X] = 0) (h1 : P[X ^ 2] = 1) (t : ℝ) :
    Tendsto (fun (n : ℕ) ↦ (charFun (P.map X) ((√n)⁻¹ * t)) ^ n) atTop (𝓝 (exp (- t ^ 2 / 2))) := by
  apply tendsto_pow_exp_of_isLittleO_sub_add_div
  suffices (fun (n : ℕ) ↦ charFun (Measure.map X P) ((√n)⁻¹ * t) -
      (1 + (-(((√n)⁻¹ * t) ^ 2 / 2) : ℂ))) =o[atTop] fun n ↦ ((√n)⁻¹ * t) ^ 2 by
    have aux : (fun (n : ℕ) ↦ ‖(1 / n : ℂ)‖) = fun (n : ℕ) ↦ ‖(1 / n : ℝ)‖ := by simp
    rw [← Asymptotics.isLittleO_norm_right, aux, Asymptotics.isLittleO_norm_right]
    refine .of_const_mul_right (c := t ^ 2) ?_
    convert this using 4 with n <;> norm_cast <;> simp [field]
  have : Tendsto (fun (n : ℕ) ↦ (√n)⁻¹ * t) atTop (𝓝 0) := by
    rw [← zero_mul t]
    exact .mul_const t (tendsto_inv_atTop_zero.comp <| Real.tendsto_sqrt_atTop.comp <|
      tendsto_natCast_atTop_atTop)
  convert (taylor_charFun_two hX h0 h1).comp_tendsto this using 2
  simp
  ring

variable [IsProbabilityMeasure P']

/-- **Central Limit Theorem:** Given a sequence of random variables `X : ℕ → Ω → ℝ` that are
independent, identically distributed, centered and with variance `1` and a random variable
`Y : Ω' → ℝ` following `gaussianReal 0 1`, the sequence
`n ↦ (√n)⁻¹ * ∑ k ∈ Finset.range n, X k` converges to `Y` in distribution. -/
theorem tendstoInDistribution_inv_sqrt_mul_sum (hY : HasLaw Y (gaussianReal 0 1) P')
    (h0 : P[X 0] = 0) (h1 : P[X 0 ^ 2] = 1) (hindep : iIndepFun X P)
    (hident : ∀ (i : ℕ), IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ (√n)⁻¹ * ∑ k ∈ Finset.range n, X k ω) atTop Y
      (fun _ ↦ P) P' where
  forall_aemeasurable n :=
    .const_mul (Finset.aemeasurable_fun_sum _ fun _ _ ↦ (hident _).aemeasurable_fst) _
  tendsto := by
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t ↦ ?_
    rw! [hY.map_eq]
    simpa [charFun_inv_sqrt_mul_sum hindep hident, charFun_gaussianReal, neg_div] using
      tendsto_charFun_inv_sqrt_mul_pow (hident 0).aemeasurable_fst h0 h1 t

/-- **Central Limit Theorem:** Given a sequence of random variables `X : ℕ → Ω → ℝ` that are
independent, identically distributed with mean `μ` and non-zero variance `v`, and a random variable
`Y : Ω' → ℝ` following `gaussianReal 0 1`, the sequence
`n ↦ (√(n * v)⁻¹ * (∑ k ∈ Finset.range n, X k ω - n * μ)` converges to `Y` in distribution. -/
private theorem tendstoInDistribution_inv_sqrt_mul_var_mul_sum_sub
    (hY : HasLaw Y (gaussianReal 0 1) P')
    (hX : Var[X 0; P] ≠ 0) (hindep : iIndepFun X P)
    (hident : ∀ (i : ℕ), IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ (√(n * Var[X 0; P]))⁻¹ * (∑ k ∈ Finset.range n, X k ω - n * P[X 0]))
      atTop Y (fun _ ↦ P) P' := by
  have mX0 := (hident 0).aemeasurable_fst
  have intX0 : Integrable (X 0) P := memLp_one_iff_integrable.1 <|
    (memLp_two_of_variance_ne_zero mX0.aestronglyMeasurable hX).mono_exponent (by simp)
  have this (n : ℕ) ω : (√(n * Var[X 0; P]))⁻¹ * (∑ k ∈ Finset.range n, X k ω - n * P[X 0]) =
      (√n)⁻¹ * ∑ k ∈ Finset.range n, (X k ω - P[X 0]) / √Var[X 0; P] := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    simp [field]
  simp_rw [this]
  convert tendstoInDistribution_inv_sqrt_mul_sum hY ?_ ?_ ?_ ?_
  · rw [integral_div, integral_sub intX0 (by simp)]
    simp
  · simp only [Pi.pow_apply, div_pow]
    rw [integral_div, ← variance_eq_integral mX0, Real.sq_sqrt (variance_nonneg _ _), div_self hX]
  · exact hindep.comp (fun _ x ↦ (x - P[X 0]) / √Var[X 0; P]) (by fun_prop)
  · convert fun n ↦ (hident n).comp (u := fun x ↦ (x - P[X 0]) / √Var[X 0; P]) (by fun_prop)

/-- **Central Limit Theorem:** Given a sequence of random variables `X : ℕ → Ω → ℝ` that are
independent, identically distributed with mean `μ` and variance `v`, and a random variable
`Y : Ω' → ℝ` following `gaussianReal 0 v`, the sequence
`n ↦ (√n)⁻¹ * (∑ k ∈ Finset.range n, X k ω - n * μ)` converges to `Y` in distribution. -/
theorem tendstoInDistribution_inv_sqrt_mul_sum_sub
    (hY : HasLaw Y (gaussianReal 0 Var[X 0; P].toNNReal) P')
    (hX : MemLp (X 0) 2 P) (hindep : iIndepFun X P)
    (hident : ∀ (i : ℕ), IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ (√n)⁻¹ * (∑ k ∈ Finset.range n, X k ω - n * P[X 0]))
      atTop Y (fun _ ↦ P) P' := by
  obtain h | h := eq_or_ne Var[X 0; P] 0
  · have : ∀ᵐ ω ∂P, ∀ n, X n ω = P[X 0] := by
      refine ae_all_iff.2 fun n ↦ ?_
      convert (ae_eq_integral_of_variance_eq_zero ((hident n).memLp_iff.2 hX)) ?_ using 3
      · rw [(hident n).integral_eq]
      · rwa [(hident n).variance_eq]
    have mX (n : ℕ) := (hident n).aemeasurable_fst
    refine tendstoInDistribution_of_identDistrib 0 (fun n ↦ ?_) ?_
    · refine ⟨by fun_prop, by fun_prop, Measure.map_congr ?_⟩
      filter_upwards [this] with ω hω
      simp [hω]
    · exact ⟨by fun_prop, by fun_prop, by simp [hY.map_eq, h]⟩
  have : HasLaw (fun ω ↦ Y ω / √Var[X 0; P]) (gaussianReal 0 1) P' := by
    convert gaussianReal_div_const hY _
    · simp
    · ext; simp [h]
  convert (tendstoInDistribution_inv_sqrt_mul_var_mul_sum_sub this h hindep hident).continuous_comp
    (g := (√Var[X 0; P] * ·)) (by fun_prop)
  · simp [field] -- simp [field, hX] triggers the unused simp arguments linter
    field_simp [h]
  · ext
    simp [field] -- simp [field, hX] triggers the unused simp arguments linter
    field_simp [h]

end ProbabilityTheory

section Multivariate

open scoped RealInnerProductSpace

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'}
  [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {d : ℕ+} {X : ℕ → Ω → EuclideanSpace ℝ (Fin d)} {Y : Ω' → EuclideanSpace ℝ (Fin d)}

theorem tendsto_map_inv_sqrt_smul_sum
    (h0 : P[X 0] = 0)
    (h1 : ∀ i j, P[(fun ω ↦ (X 0 ω i) * (X 0 ω j))] = if i = j then 1 else 0)
    (hindep : iIndepFun X P)
    (hident : ∀ (i : ℕ), IdentDistrib (X i) (X 0) P P) :
    Tendsto
      (fun n : ℕ =>
        ProbabilityMeasure.map
          (⟨P, inferInstance⟩ : ProbabilityMeasure Ω)
          ((Finset.aemeasurable_fun_sum (Finset.range n)
            (fun k _ ↦ (hident k).aemeasurable_fst)).const_smul ((√n)⁻¹)))
      atTop
      (𝓝
        ((⟨stdGaussian (EuclideanSpace ℝ (Fin d)), inferInstance⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin d))))) := by
  have i0 : Integrable (X 0) P := by
    have h_L2 : MemLp (fun ω => X 0 ω) 2 P := by
      have hXae : ∀ n, AEMeasurable (X n) P := fun n => (hident n).aemeasurable_fst
      refine ⟨(hXae 0).aestronglyMeasurable, ?_⟩
      unfold eLpNorm
      simp [eLpNorm']
      ring_nf
      rw [ENNReal.rpow_lt_top_iff_of_pos one_half_pos]
      conv_lhs => {
        arg 2
        enter [ω]
        rw [←ofReal_norm_eq_enorm, ←ENNReal.ofReal_pow (by {simp [norm_nonneg]}),
          ←real_inner_self_eq_norm_sq]
        simp [inner, ←pow_two]
        rw [ENNReal.ofReal_sum_of_nonneg (fun _ => by {simp [sq_nonneg]})]
      }
      rw [lintegral_finset_sum' _ (fun _ => by {fun_prop})]
      rw [ENNReal.sum_lt_top]
      intro i hi
      conv_lhs => {
        arg 2
        enter [a]
        rw [←Real.enorm_eq_ofReal (by simp [sq_nonneg])]
      }
      rw [←hasFiniteIntegral_def]
      refine Integrable.hasFiniteIntegral ?_
      exact Integrable.of_integral_ne_zero (by {
        simp_rw [pow_two]
        rw [h1 i i]
        simp
      })
    apply MemLp.integrable (by norm_num : 1 ≤ (2 : ENNReal)) h_L2
  let μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) :=
    ⟨stdGaussian (EuclideanSpace ℝ (Fin d)), inferInstance⟩
  let μn : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) :=
    fun n =>
      ProbabilityMeasure.map
        (⟨P, inferInstance⟩ : ProbabilityMeasure Ω)
        ((Finset.aemeasurable_fun_sum (Finset.range n)
          (fun k _ ↦ (hident k).aemeasurable_fst)).const_smul ((√n)⁻¹))
  change Tendsto μn atTop (𝓝 μ)
  refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 ?_
  intro t
  by_cases ht : t = 0
  · simp [ht]
  have h_ne : ‖t‖ ≠ 0 := by simpa [norm_eq_zero] using ht
  have : Invertible ‖t‖ := invertibleOfNonzero h_ne
  let t' : EuclideanSpace ℝ (Fin d) := ‖t‖⁻¹ • t
  let Y : ℕ → Ω → ℝ := fun i ω => ⟪X i ω, t'⟫
  have hY_ae : ∀ i, AEMeasurable (Y i) P := by
    intro i
    dsimp [Y]
    exact AEMeasurable.inner_const ((hident i).aemeasurable_fst)
  have h0_Y : P[Y 0] = 0 := by
    dsimp [Y]
    calc
      ∫ ω : Ω, ⟪X 0 ω, t'⟫ ∂P
          = ∫ ω : Ω, ⟪t', (X 0 ω)⟫ ∂P := by
              simp only [real_inner_comm]
      _   = ⟪t', P[X 0]⟫ := by
            apply integral_inner i0
      _   = ⟪t', 0⟫ := by rw [h0]
      _   = 0 := by simp
  have h1_Y : P[(Y 0) ^ 2] = 1 := by
    dsimp [Y]
    calc
      P[fun ω => ⟪(X 0 ω), t'⟫ ^ 2]
        = ∫ ω, ∑ i, ∑ j, (t' i * t' j) * (X 0 ω i * X 0 ω j) ∂P := by
            have h_expand :
                ∀ ω,
                  ⟪X 0 ω, t'⟫ ^ 2
                    = ∑ i, ∑ j, (t' i * t' j) * (X 0 ω i * X 0 ω j) := by
              intro ω
              rw [PiLp.inner_apply]
              conv_lhs => {
                arg 1
                arg 2
                intro
                unfold inner
                erw [@RCLike.inner_apply ℝ _ ((X 0 ω).ofLp _ : ℝ) (t'.ofLp _ : ℝ)]
                simp
              }
              simp_rw [pow_two, Finset.sum_mul_sum, ←mul_assoc, mul_comm, ←mul_assoc]
            simp [h_expand]
      _ = ∑ i, ∑ j, (t' i * t' j) * ∫ ω, X 0 ω i * X 0 ω j ∂P := by
          have h_L2_pi (idx : Fin d) : MemLp (fun ω => (X 0 ω).ofLp idx) 2 P := by
            constructor
            · have h_cont : Continuous (fun (x : EuclideanSpace ℝ (Fin d)) => x.ofLp idx) := by
                fun_prop
              exact Continuous.comp_aestronglyMeasurable h_cont i0.aestronglyMeasurable
            · unfold eLpNorm
              simp [eLpNorm']
              ring_nf
              rw [ENNReal.rpow_lt_top_iff_of_pos one_half_pos]
              simp_rw [Real.enorm_eq_ofReal_abs]
              conv_lhs =>
                arg 2
                enter [a]
                rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs, ← abs_sq,
                  ← Real.enorm_eq_ofReal_abs, pow_two]
              rw [← hasFiniteIntegral_def]
              refine Integrable.hasFiniteIntegral ?_
              exact Integrable.of_integral_ne_zero (by
                rw [h1 idx idx]
                simp)
          have h_integrable_prod (i' j' : Fin d) :
              Integrable (fun ω ↦ X 0 ω i' * X 0 ω j') P := by
            apply MemLp.integrable
            · rfl
            exact
              @MemLp.mul Ω _ ℝ _ P 2 2 1
                (fun ω => X 0 ω j') (fun ω => X 0 ω i')
                (h_L2_pi j') (h_L2_pi i') _
          rw [integral_finset_sum]
          · apply Finset.sum_congr rfl
            intro i hi
            rw [integral_finset_sum]
            · apply Finset.sum_congr rfl
              intro j hj
              rw [integral_const_mul]
            · intro j hj
              exact (h_integrable_prod i j).const_mul (t' i * t' j)
          · intro i hi
            apply MeasureTheory.integrable_finset_sum
            intro j hj
            exact (h_integrable_prod i j).const_mul (t' i * t' j)
      _ = ∑ i, ∑ j, (t' i * t' j) * (if i = j then 1 else 0) := by
          simp_rw [h1]
      _ = ∑ i, (t' i) ^ 2 := by
          simp [pow_two]
      _ = ‖t'‖ ^ 2 := by
          rw [EuclideanSpace.norm_sq_eq]
          simp [pow_two]
      _ = 1 := by
          simp [t', norm_smul]
  have hindepY : iIndepFun Y P := by
    refine hindep.comp (fun _ x ↦ ⟪x, t'⟫) ?_
    simpa using (Measurable.inner measurable_id measurable_const)
  have hidentY : ∀ i, IdentDistrib (Y i) (Y 0) P P := by
    intro i
    refine (hident i).comp (u := fun x ↦ ⟪x, t'⟫) ?_
    simpa using (Measurable.inner measurable_id measurable_const)
  have hchar_scalar :
      Tendsto
        (fun n : ℕ => charFun (P.map (Y 0)) ((√n)⁻¹ * ‖t‖) ^ n)
        atTop
        (𝓝 (Complex.exp (-(‖t‖ ^ 2 / 2)))) := by
    simpa [mul_comm, mul_left_comm, mul_assoc, pow_two, neg_div]
      using
        (tendsto_charFun_inv_sqrt_mul_pow
          (P := P) (X := Y 0) (hY_ae 0) h0_Y h1_Y ‖t‖)
  have h_proj_sum :
      ∀ (n : ℕ) ω,
        ⟪((√n)⁻¹ • ∑ k ∈ Finset.range n, X k ω), t⟫
          = ‖t‖ * ((√n)⁻¹ * ∑ k ∈ Finset.range n, Y k ω) := by
    intro n ω
    calc
      ⟪((√n)⁻¹ • ∑ k ∈ Finset.range n, X k ω), t⟫
          = (√n)⁻¹ * ⟪∑ k ∈ Finset.range n, X k ω, t⟫ := by
              rw [inner_smul_left]
              simp
      _   = (√n)⁻¹ * ∑ k ∈ Finset.range n, ⟪X k ω, t⟫ := by
              rw [sum_inner]
      _   = (√n)⁻¹ * ∑ k ∈ Finset.range n, (‖t‖ * ⟪X k ω, t'⟫) := by
              simp [t', inner_smul_right, ← mul_assoc,
                mul_inv_cancel_of_invertible ‖t‖]
      _   = ‖t‖ * ((√n)⁻¹ * ∑ k ∈ Finset.range n, Y k ω) := by
              dsimp [Y]
              ring_nf
              simp [Finset.mul_sum, mul_assoc]
  have h_char_μ :
      charFun μ t = Complex.exp (-(‖t‖ ^ 2 / 2)) := by
    dsimp [μ]
    rw [charFun_stdGaussian, neg_div]
  have h_char_μn :
      ∀ n,
        charFun (μn n) t
          = charFun (P.map (Y 0)) ((√n)⁻¹ * ‖t‖) ^ n := by
    intro n
    have hsum_ae :
        (fun ω =>
          ⟪((√n)⁻¹ • ∑ k ∈ Finset.range n, X k ω), t⟫)
        =ᵐ[P]
        (fun ω => ‖t‖ * ((√n)⁻¹ * ∑ k ∈ Finset.range n, Y k ω)) :=
      Filter.Eventually.of_forall (h_proj_sum n)
    simp only [μn, charFun]
    rw [ProbabilityMeasure.toMeasure_map]
    simp_rw [ProbabilityMeasure.coe_mk]
    have h_cont : Continuous (fun x : EuclideanSpace ℝ (Fin d) ↦
      Complex.exp (↑⟪x, t⟫ * Complex.I)) := by fun_prop
    have h_meas : AEMeasurable ((√n)⁻¹ • fun a ↦ ∑ i ∈ Finset.range n, X i a) P :=
      (Finset.aemeasurable_fun_sum (Finset.range n)
        (fun k _ ↦ (hident k).aemeasurable_fst)).const_smul ((√n)⁻¹)
    rw [integral_map h_meas h_cont.aestronglyMeasurable]
    simp_rw [Pi.smul_apply]
    simp_rw [h_proj_sum]
    change _ = charFun (Measure.map (Y 0) P) ((√↑n)⁻¹ * ‖t‖) ^ n
    have h_LHS : ∫ (x : Ω), cexp (↑(‖t‖ * ((√↑n)⁻¹ * ∑ k ∈ Finset.range n, Y k x)) * I) ∂P =
                 charFun (Measure.map (fun ω ↦ (√↑n)⁻¹ * ∑ k ∈ Finset.range n, Y k ω) P) ‖t‖ := by
      rw [charFun_apply_real]
      have h_meas_Y : AEMeasurable (fun ω ↦ (√↑n)⁻¹ * ∑ i ∈ Finset.range n, Y i ω) P := by
        apply AEMeasurable.mul aemeasurable_const
        exact Finset.aemeasurable_fun_sum (Finset.range n) (fun k _ ↦ hY_ae k)
      have h_cont_Y : Continuous (fun (x : ℝ) ↦ Complex.exp (↑‖t‖ * ↑x * Complex.I)) :=
        by fun_prop
      rw [integral_map h_meas_Y h_cont_Y.aestronglyMeasurable]
      simp_rw [← Complex.ofReal_mul]
    rw [h_LHS]
    rw [charFun_inv_sqrt_mul_sum]
    · apply hindepY
    exact hidentY
  simp_rw [h_char_μn, h_char_μ]
  exact hchar_scalar

/-- **Multivariate Central Limit Theorem:** Given a sequence of random variables `X : ℕ → Ω →
EuclideanSpace ℝ (Fin d)` that are independent, identically distributed, centered and with an
identity covariance matrix, and a random variable `Y : Ω' → EuclideanSpace ℝ (Fin d)` following
`stdGaussian (EuclideanSpace ℝ (Fin d))`, the sequence `n ↦ (√n)⁻¹ • ∑ k ∈ Finset.range n, X k`
converges to `Y` in distribution. -/
theorem tendstoInDistribution_inv_sqrt_smul_sum
    (hY : HasLaw Y (stdGaussian (EuclideanSpace ℝ (Fin d))) P') (h0 : P[X 0] = 0)
    (h1 : ∀ i j, P[(fun ω ↦ (X 0 ω i) * (X 0 ω j))] = if i = j then 1 else 0)
    (hindep : iIndepFun X P) (hident : ∀ (i : ℕ), IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ (√n)⁻¹ • ∑ k ∈ Finset.range n, X k ω) atTop Y
      (fun _ ↦ P) P' where
  forall_aemeasurable n :=
    .const_smul (Finset.aemeasurable_fun_sum _ fun _ _ ↦ (hident _).aemeasurable_fst) ((√n)⁻¹)
  tendsto := by
    have hclt :
        Tendsto
          (fun n : ℕ =>
            ProbabilityMeasure.map
              (⟨P, inferInstance⟩ : ProbabilityMeasure Ω)
              ((Finset.aemeasurable_fun_sum (Finset.range n)
              (fun k _ ↦ (hident k).aemeasurable_fst)).const_smul ((√n)⁻¹)))
          atTop
          (𝓝
            ((⟨stdGaussian (EuclideanSpace ℝ (Fin d)),
                inferInstance⟩ :
              ProbabilityMeasure (EuclideanSpace ℝ (Fin d))))) :=
      tendsto_map_inv_sqrt_smul_sum (P := P) (d := d) (X := X) h0 h1 hindep hident
    have hmapY_eq : Measure.map Y P' = stdGaussian (EuclideanSpace ℝ (Fin d)) := hY.map_eq
    have hmapY_prob : IsProbabilityMeasure (Measure.map Y P') := by
      rw [hmapY_eq]
      exact inferInstance
    have hY' :
        (⟨Measure.map Y P', hmapY_prob⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) =
        (⟨stdGaussian (EuclideanSpace ℝ (Fin d)),
          inferInstance⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) := by
      apply Subtype.ext
      exact hmapY_eq
    simpa [hY'] using hclt

end Multivariate
