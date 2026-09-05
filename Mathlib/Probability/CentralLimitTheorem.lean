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
  rw [charFun_map_mul_comp, (hindep.restrict _).charFun_map_fun_finsetSum_eq_prod (fun _ _ ↦ mX _)]
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
    convert! this using 4 with n <;> norm_cast <;> simp [field]
  have : Tendsto (fun (n : ℕ) ↦ (√n)⁻¹ * t) atTop (𝓝 0) := by
    rw [← zero_mul t]
    exact .mul_const t (tendsto_inv_atTop_zero.comp <| Real.tendsto_sqrt_atTop.comp <|
      tendsto_natCast_atTop_atTop)
  convert! (taylor_charFun_two hX h0 h1).comp_tendsto this using 2
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
  have (n : ℕ) ω : (√(n * Var[X 0; P]))⁻¹ * (∑ k ∈ Finset.range n, X k ω - n * P[X 0]) =
      (√n)⁻¹ * ∑ k ∈ Finset.range n, (X k ω - P[X 0]) / √Var[X 0; P] := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    simp [field]
  simp_rw [this]
  convert! tendstoInDistribution_inv_sqrt_mul_sum hY ?_ ?_ ?_ ?_
  · rw [integral_div, integral_sub intX0 (by simp)]
    simp
  · simp only [Pi.pow_apply, div_pow]
    rw [integral_div, ← variance_eq_integral mX0, Real.sq_sqrt (variance_nonneg _ _), div_self hX]
  · exact hindep.comp (fun _ x ↦ (x - P[X 0]) / √Var[X 0; P]) (by fun_prop)
  · convert! fun n ↦ (hident n).comp (u := fun x ↦ (x - P[X 0]) / √Var[X 0; P]) (by fun_prop)

/-- **Central Limit Theorem:** Given a sequence of random variables `X : ℕ → Ω → ℝ` that are
independent, identically distributed with mean `μ` and variance `v`, and a random variable
`Y : Ω' → ℝ` following `gaussianReal 0 v`, the sequence
`n ↦ (√n)⁻¹ * (∑ k ∈ Finset.range n, X k ω - n * μ)` converges to `Y` in distribution. -/
@[wikidata Q190391]
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
      convert! (ae_eq_integral_of_variance_eq_zero ((hident n).memLp_iff.2 hX)) ?_ using 3
      · rw [(hident n).integral_eq]
      · rwa [(hident n).variance_eq]
    have mX (n : ℕ) := (hident n).aemeasurable_fst
    refine tendstoInDistribution_of_identDistrib 0 (fun n ↦ ?_) ?_
    · refine ⟨by fun_prop, by fun_prop, Measure.map_congr ?_⟩
      filter_upwards [this] with ω hω
      simp [hω]
    · exact ⟨by fun_prop, by fun_prop, by simp [hY.map_eq, h]⟩
  have : HasLaw (fun ω ↦ Y ω / √Var[X 0; P]) (gaussianReal 0 1) P' := by
    convert! gaussianReal_div_const hY _
    · simp
    · ext; simp [h]
  convert!
    (tendstoInDistribution_inv_sqrt_mul_var_mul_sum_sub this h hindep hident).continuous_comp (g :=
      (√Var[X 0; P] * ·)) (by fun_prop)
  · simp [field]
    field_simp [h]
  · ext
    simp [field]
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
          (fun ω ↦ (√n)⁻¹ • ∑ k ∈ Finset.range n, X k ω))
      atTop
      (𝓝
        ((⟨stdGaussian (EuclideanSpace ℝ (Fin d)), inferInstance⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin d))))) := by
  have hL2 : MemLp (X 0) 2 P := .of_eval_piLp fun i ↦
    (memLp_two_iff_integrable_sq ((by fun_prop : Continuous
      (fun x : EuclideanSpace ℝ (Fin d) ↦ x i)).comp_aestronglyMeasurable
        (hident 0).aemeasurable_fst.aestronglyMeasurable)).2 <| .of_integral_ne_zero <| by
      simp [h1 i i, pow_two]
  refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 ?_
  intro t
  change Tendsto
    (fun n : ℕ ↦ charFun (P.map (fun ω ↦ (√n)⁻¹ • ∑ k ∈ Finset.range n, X k ω)) t)
    atTop (𝓝 (charFun (stdGaussian (EuclideanSpace ℝ (Fin d))) t))
  by_cases ht : t = 0
  · simp [ht]
  have : Invertible ‖t‖ := invertibleOfNonzero (by simpa [norm_eq_zero] using ht)
  let t' : EuclideanSpace ℝ (Fin d) := ‖t‖⁻¹ • t
  let Y : ℕ → Ω → ℝ := fun i ω => ⟪X i ω, t'⟫
  convert tendsto_charFun_inv_sqrt_mul_pow
    (P := P) (X := Y 0) (by simpa [Y] using
      AEMeasurable.inner_const (hident 0).aemeasurable_fst) (by
        dsimp [Y]
        calc
          ∫ ω : Ω, ⟪X 0 ω, t'⟫ ∂P = ∫ ω : Ω, ⟪t', X 0 ω⟫ ∂P := by
            simp only [real_inner_comm]
          _ = ⟪t', P[X 0]⟫ := integral_inner (hL2.integrable <| by norm_num) t'
          _ = ⟪t', 0⟫ := by rw [h0]
          _ = 0 := by simp) (by
        dsimp [Y]
        calc
          P[fun ω => ⟪X 0 ω, t'⟫ ^ 2] =
              ∫ ω, ∑ i, ∑ j, (t' i * t' j) * (X 0 ω i * X 0 ω j) ∂P := by
            congr 1
            funext ω
            change ⟪X 0 ω, t'⟫ ^ 2 = _
            rw [PiLp.inner_apply]
            conv_lhs =>
              arg 1
              arg 2
              intro
              rw [RCLike.inner_apply]
              simp
            simp_rw [pow_two, Finset.sum_mul_sum, ← mul_assoc, mul_comm, ← mul_assoc]
          _ = ∑ i, ∑ j, (t' i * t' j) * ∫ ω, X 0 ω i * X 0 ω j ∂P := by
            rw [integral_finsetSum]
            · apply Finset.sum_congr rfl
              intro i hi
              rw [integral_finsetSum]
              · apply Finset.sum_congr rfl
                intro j hj
                rw [integral_const_mul]
              · intro j hj
                exact ((@MemLp.mul Ω _ ℝ _ P 2 2 1 _ _
                  (hL2.eval_piLp j) (hL2.eval_piLp i) _).integrable <| by norm_num).const_mul _
            · intro i hi
              apply integrable_finsetSum
              intro j hj
              exact ((@MemLp.mul Ω _ ℝ _ P 2 2 1 _ _
                (hL2.eval_piLp j) (hL2.eval_piLp i) _).integrable <| by norm_num).const_mul _
          _ = ∑ i, ∑ j, (t' i * t' j) * (if i = j then 1 else 0) := by simp_rw [h1]
          _ = ∑ i, (t' i) ^ 2 := by simp [pow_two]
          _ = ‖t'‖ ^ 2 := by rw [EuclideanSpace.norm_sq_eq]; simp [pow_two]
          _ = 1 := by simp [t', norm_smul]) ‖t‖ using 1
  · ext n
    rw [charFun_map_eq_charFun_map_inner_one <|
      (Finset.aemeasurable_fun_sum (Finset.range n)
        (fun k _ ↦ (hident k).aemeasurable_fst)).fun_const_smul ((√n)⁻¹)]
    rw [Measure.map_congr (Filter.Eventually.of_forall fun ω ↦ by
      calc
        ⟪((√n)⁻¹ • ∑ k ∈ Finset.range n, X k ω), t⟫
            = (√n)⁻¹ * ⟪∑ k ∈ Finset.range n, X k ω, t⟫ := by
                rw [inner_smul_left]
                simp
        _ = (√n)⁻¹ * ∑ k ∈ Finset.range n, ⟪X k ω, t⟫ := by
                rw [sum_inner]
        _ = (√n)⁻¹ * ∑ k ∈ Finset.range n, (‖t‖ * ⟪X k ω, t'⟫) := by
                simp [t', inner_smul_right, ← mul_assoc,
                  mul_inv_cancel_of_invertible ‖t‖]
        _ = ‖t‖ * ((√n)⁻¹ * ∑ k ∈ Finset.range n, Y k ω) := by
                dsimp [Y]
                ring_nf
                simp [Finset.mul_sum, mul_assoc])]
    rw [charFun_map_mul_comp]
    · simpa [mul_assoc] using charFun_inv_sqrt_mul_sum (X := Y)
        (hindep.comp (fun _ x ↦ ⟪x, t'⟫) (by fun_prop))
        (fun i ↦ (hident i).comp (u := fun x ↦ ⟪x, t'⟫) (by fun_prop))
    · exact aemeasurable_const.mul <| Finset.aemeasurable_fun_sum _ fun k _ ↦ by
        simpa [Y] using AEMeasurable.inner_const (hident k).aemeasurable_fst
  · rw [charFun_stdGaussian, neg_div]

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
    .const_smul
      (Finset.aemeasurable_fun_sum _ fun _ _ ↦ (hident _).aemeasurable_fst) ((√n)⁻¹)
  tendsto := by
    change Tendsto
      (fun n : ℕ ↦ ProbabilityMeasure.map (⟨P, inferInstance⟩ : ProbabilityMeasure Ω)
        (fun ω ↦ (√n)⁻¹ • ∑ k ∈ Finset.range n, X k ω)) atTop
      (𝓝 (⟨P'.map Y, inferInstance⟩ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))))
    simpa only [hY.map_eq] using
      tendsto_map_inv_sqrt_smul_sum h0 h1 hindep hident

end Multivariate
