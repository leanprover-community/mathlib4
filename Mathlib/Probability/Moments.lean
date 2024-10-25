/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Variance
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Measure.Tilted

/-!
# Moments and moment generating function

## Main definitions

* `ProbabilityTheory.moment X p μ`: `p`th moment of a real random variable `X` with respect to
  measure `μ`, `μ[X^p]`
* `ProbabilityTheory.centralMoment X p μ`:`p`th central moment of `X` with respect to measure `μ`,
  `μ[(X - μ[X])^p]`
* `ProbabilityTheory.mgf X μ t`: moment generating function of `X` with respect to measure `μ`,
  `μ[exp(t*X)]`
* `ProbabilityTheory.cgf X μ t`: cumulant generating function, logarithm of the moment generating
  function

## Main results

* `ProbabilityTheory.IndepFun.mgf_add`: if two real random variables `X` and `Y` are independent
  and their mgfs are defined at `t`, then `mgf (X + Y) μ t = mgf X μ t * mgf Y μ t`
* `ProbabilityTheory.IndepFun.cgf_add`: if two real random variables `X` and `Y` are independent
  and their cgfs are defined at `t`, then `cgf (X + Y) μ t = cgf X μ t + cgf Y μ t`
* `ProbabilityTheory.measure_ge_le_exp_cgf` and `ProbabilityTheory.measure_le_le_exp_cgf`:
  Chernoff bound on the upper (resp. lower) tail of a random variable. For `t` nonnegative such that
  the cgf exists, `ℙ(ε ≤ X) ≤ exp(- t*ε + cgf X ℙ t)`. See also
  `ProbabilityTheory.measure_ge_le_exp_mul_mgf` and
  `ProbabilityTheory.measure_le_le_exp_mul_mgf` for versions of these results using `mgf` instead
  of `cgf`.
* `ProbabilityTheory.tilt_first_deriv`: derivation of `mgf X μ t` is
  `μ[exp (t * X ω) * X ω]`. In order to deal with the differentiation of parametric integrals,
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` are used in the proof.
* `ProbabilityTheory.tilt_second_deriv`: derivation of `μ[fun ω ↦ rexp (t * X ω) * X ω]` is
  `μ[fun ω ↦ rexp (t * X ω) * X ω ^ 2]`. In order to deal with the differentiation of
  parametric integrals, `hasDerivAt_integral_of_dominated_loc_of_deriv_le` are used in the proof.
* `ProbabilityTheory.cum_deriv_one`: first derivative of cumulant `cgf X μ t`.
  It can be described by exponential tilting.
* `ProbabilityTheory.cum_deriv_two`: second derivative of cumulant `cgf X μ t`.
-/


open MeasureTheory Filter Finset Real

noncomputable section

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal

namespace ProbabilityTheory

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {X : Ω → ℝ} {p : ℕ} {μ : Measure Ω}

/-- Moment of a real random variable, `μ[X ^ p]`. -/
def moment (X : Ω → ℝ) (p : ℕ) (μ : Measure Ω) : ℝ :=
  μ[X ^ p]

/-- Central moment of a real random variable, `μ[(X - μ[X]) ^ p]`. -/
def centralMoment (X : Ω → ℝ) (p : ℕ) (μ : Measure Ω) : ℝ := by
  have m := fun (x : Ω) => μ[X] -- Porting note: Lean deems `μ[(X - fun x => μ[X]) ^ p]` ambiguous
  exact μ[(X - m) ^ p]

@[simp]
theorem moment_zero (hp : p ≠ 0) : moment 0 p μ = 0 := by
  simp only [moment, hp, zero_pow, Ne, not_false_iff, Pi.zero_apply, integral_const,
    smul_eq_mul, mul_zero, integral_zero]

@[simp]
theorem centralMoment_zero (hp : p ≠ 0) : centralMoment 0 p μ = 0 := by
  simp only [centralMoment, hp, Pi.zero_apply, integral_const, smul_eq_mul,
    mul_zero, zero_sub, Pi.pow_apply, Pi.neg_apply, neg_zero, zero_pow, Ne, not_false_iff]

theorem centralMoment_one' [IsFiniteMeasure μ] (h_int : Integrable X μ) :
    centralMoment X 1 μ = (1 - (μ Set.univ).toReal) * μ[X] := by
  simp only [centralMoment, Pi.sub_apply, pow_one]
  rw [integral_sub h_int (integrable_const _)]
  simp only [sub_mul, integral_const, smul_eq_mul, one_mul]

@[simp]
theorem centralMoment_one [IsZeroOrProbabilityMeasure μ] : centralMoment X 1 μ = 0 := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | h
  · simp [centralMoment]
  by_cases h_int : Integrable X μ
  · rw [centralMoment_one' h_int]
    simp only [measure_univ, ENNReal.one_toReal, sub_self, zero_mul]
  · simp only [centralMoment, Pi.sub_apply, pow_one]
    have : ¬Integrable (fun x => X x - integral μ X) μ := by
      refine fun h_sub => h_int ?_
      have h_add : X = (fun x => X x - integral μ X) + fun _ => integral μ X := by ext1 x; simp
      rw [h_add]
      exact h_sub.add (integrable_const _)
    rw [integral_undef this]

theorem centralMoment_two_eq_variance [IsFiniteMeasure μ] (hX : Memℒp X 2 μ) :
    centralMoment X 2 μ = variance X μ := by rw [hX.variance_eq]; rfl

section MomentGeneratingFunction

variable {t : ℝ}

/-- Moment generating function of a real random variable `X`: `fun t => μ[exp(t*X)]`. -/
def mgf (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) : ℝ :=
  μ[fun ω => exp (t * X ω)]

/-- Cumulant generating function of a real random variable `X`: `fun t => log μ[exp(t*X)]`. -/
def cgf (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) : ℝ :=
  log (mgf X μ t)

@[simp]
theorem mgf_zero_fun : mgf 0 μ t = (μ Set.univ).toReal := by
  simp only [mgf, Pi.zero_apply, mul_zero, exp_zero, integral_const, smul_eq_mul, mul_one]

@[simp]
theorem cgf_zero_fun : cgf 0 μ t = log (μ Set.univ).toReal := by simp only [cgf, mgf_zero_fun]

@[simp]
theorem mgf_zero_measure : mgf X (0 : Measure Ω) t = 0 := by simp only [mgf, integral_zero_measure]

@[simp]
theorem cgf_zero_measure : cgf X (0 : Measure Ω) t = 0 := by
  simp only [cgf, log_zero, mgf_zero_measure]

@[simp]
theorem mgf_const' (c : ℝ) : mgf (fun _ => c) μ t = (μ Set.univ).toReal * exp (t * c) := by
  simp only [mgf, integral_const, smul_eq_mul]

-- @[simp] -- Porting note: `simp only` already proves this
theorem mgf_const (c : ℝ) [IsProbabilityMeasure μ] : mgf (fun _ => c) μ t = exp (t * c) := by
  simp only [mgf_const', measure_univ, ENNReal.one_toReal, one_mul]

@[simp]
theorem cgf_const' [IsFiniteMeasure μ] (hμ : μ ≠ 0) (c : ℝ) :
    cgf (fun _ => c) μ t = log (μ Set.univ).toReal + t * c := by
  simp only [cgf, mgf_const']
  rw [log_mul _ (exp_pos _).ne']
  · rw [log_exp _]
  · rw [Ne, ENNReal.toReal_eq_zero_iff, Measure.measure_univ_eq_zero]
    simp only [hμ, measure_ne_top μ Set.univ, or_self_iff, not_false_iff]

@[simp]
theorem cgf_const [IsProbabilityMeasure μ] (c : ℝ) : cgf (fun _ => c) μ t = t * c := by
  simp only [cgf, mgf_const, log_exp]

@[simp]
theorem mgf_zero' : mgf X μ 0 = (μ Set.univ).toReal := by
  simp only [mgf, zero_mul, exp_zero, integral_const, smul_eq_mul, mul_one]

-- @[simp] -- Porting note: `simp only` already proves this
theorem mgf_zero [IsProbabilityMeasure μ] : mgf X μ 0 = 1 := by
  simp only [mgf_zero', measure_univ, ENNReal.one_toReal]

theorem cgf_zero' : cgf X μ 0 = log (μ Set.univ).toReal := by simp only [cgf, mgf_zero']

@[simp]
theorem cgf_zero [IsZeroOrProbabilityMeasure μ] : cgf X μ 0 = 0 := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | h <;> simp [cgf_zero']

theorem mgf_undef (hX : ¬Integrable (fun ω => exp (t * X ω)) μ) : mgf X μ t = 0 := by
  simp only [mgf, integral_undef hX]

theorem cgf_undef (hX : ¬Integrable (fun ω => exp (t * X ω)) μ) : cgf X μ t = 0 := by
  simp only [cgf, mgf_undef hX, log_zero]

theorem mgf_nonneg : 0 ≤ mgf X μ t := by
  unfold mgf; positivity

theorem mgf_pos' (hμ : μ ≠ 0) (h_int_X : Integrable (fun ω => exp (t * X ω)) μ) :
    0 < mgf X μ t := by
  simp_rw [mgf]
  have : ∫ x : Ω, exp (t * X x) ∂μ = ∫ x : Ω in Set.univ, exp (t * X x) ∂μ := by
    simp only [Measure.restrict_univ]
  rw [this, setIntegral_pos_iff_support_of_nonneg_ae _ _]
  · have h_eq_univ : (Function.support fun x : Ω => exp (t * X x)) = Set.univ := by
      ext1 x
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact (exp_pos _).ne'
    rw [h_eq_univ, Set.inter_univ _]
    refine Ne.bot_lt ?_
    simp only [hμ, ENNReal.bot_eq_zero, Ne, Measure.measure_univ_eq_zero, not_false_iff]
  · filter_upwards with x
    rw [Pi.zero_apply]
    exact (exp_pos _).le
  · rwa [integrableOn_univ]

theorem mgf_pos [IsProbabilityMeasure μ] (h_int_X : Integrable (fun ω => exp (t * X ω)) μ) :
    0 < mgf X μ t :=
  mgf_pos' (IsProbabilityMeasure.ne_zero μ) h_int_X

theorem mgf_neg : mgf (-X) μ t = mgf X μ (-t) := by simp_rw [mgf, Pi.neg_apply, mul_neg, neg_mul]

theorem cgf_neg : cgf (-X) μ t = cgf X μ (-t) := by simp_rw [cgf, mgf_neg]

theorem mgf_smul_left (α : ℝ) : mgf (α • X) μ t = mgf X μ (α * t) := by
  simp_rw [mgf, Pi.smul_apply, smul_eq_mul, mul_comm α t, mul_assoc]

/-- This is a trivial application of `IndepFun.comp` but it will come up frequently. -/
theorem IndepFun.exp_mul {X Y : Ω → ℝ} (h_indep : IndepFun X Y μ) (s t : ℝ) :
    IndepFun (fun ω => exp (s * X ω)) (fun ω => exp (t * Y ω)) μ := by
  have h_meas : ∀ t, Measurable fun x => exp (t * x) := fun t => (measurable_id'.const_mul t).exp
  change IndepFun ((fun x => exp (s * x)) ∘ X) ((fun x => exp (t * x)) ∘ Y) μ
  exact IndepFun.comp h_indep (h_meas s) (h_meas t)

theorem IndepFun.mgf_add {X Y : Ω → ℝ} (h_indep : IndepFun X Y μ)
    (hX : AEStronglyMeasurable (fun ω => exp (t * X ω)) μ)
    (hY : AEStronglyMeasurable (fun ω => exp (t * Y ω)) μ) :
    mgf (X + Y) μ t = mgf X μ t * mgf Y μ t := by
  simp_rw [mgf, Pi.add_apply, mul_add, exp_add]
  exact (h_indep.exp_mul t t).integral_mul hX hY

theorem IndepFun.mgf_add' {X Y : Ω → ℝ} (h_indep : IndepFun X Y μ) (hX : AEStronglyMeasurable X μ)
    (hY : AEStronglyMeasurable Y μ) : mgf (X + Y) μ t = mgf X μ t * mgf Y μ t := by
  have A : Continuous fun x : ℝ => exp (t * x) := by fun_prop
  have h'X : AEStronglyMeasurable (fun ω => exp (t * X ω)) μ :=
    A.aestronglyMeasurable.comp_aemeasurable hX.aemeasurable
  have h'Y : AEStronglyMeasurable (fun ω => exp (t * Y ω)) μ :=
    A.aestronglyMeasurable.comp_aemeasurable hY.aemeasurable
  exact h_indep.mgf_add h'X h'Y

theorem IndepFun.cgf_add {X Y : Ω → ℝ} (h_indep : IndepFun X Y μ)
    (h_int_X : Integrable (fun ω => exp (t * X ω)) μ)
    (h_int_Y : Integrable (fun ω => exp (t * Y ω)) μ) :
    cgf (X + Y) μ t = cgf X μ t + cgf Y μ t := by
  by_cases hμ : μ = 0
  · simp [hμ]
  simp only [cgf, h_indep.mgf_add h_int_X.aestronglyMeasurable h_int_Y.aestronglyMeasurable]
  exact log_mul (mgf_pos' hμ h_int_X).ne' (mgf_pos' hμ h_int_Y).ne'

theorem aestronglyMeasurable_exp_mul_add {X Y : Ω → ℝ}
    (h_int_X : AEStronglyMeasurable (fun ω => exp (t * X ω)) μ)
    (h_int_Y : AEStronglyMeasurable (fun ω => exp (t * Y ω)) μ) :
    AEStronglyMeasurable (fun ω => exp (t * (X + Y) ω)) μ := by
  simp_rw [Pi.add_apply, mul_add, exp_add]
  exact AEStronglyMeasurable.mul h_int_X h_int_Y

theorem aestronglyMeasurable_exp_mul_sum {X : ι → Ω → ℝ} {s : Finset ι}
    (h_int : ∀ i ∈ s, AEStronglyMeasurable (fun ω => exp (t * X i ω)) μ) :
    AEStronglyMeasurable (fun ω => exp (t * (∑ i ∈ s, X i) ω)) μ := by
  classical
  induction' s using Finset.induction_on with i s hi_notin_s h_rec h_int
  · simp only [Pi.zero_apply, sum_apply, sum_empty, mul_zero, exp_zero]
    exact aestronglyMeasurable_const
  · have : ∀ i : ι, i ∈ s → AEStronglyMeasurable (fun ω : Ω => exp (t * X i ω)) μ := fun i hi =>
      h_int i (mem_insert_of_mem hi)
    specialize h_rec this
    rw [sum_insert hi_notin_s]
    apply aestronglyMeasurable_exp_mul_add (h_int i (mem_insert_self _ _)) h_rec

theorem IndepFun.integrable_exp_mul_add {X Y : Ω → ℝ} (h_indep : IndepFun X Y μ)
    (h_int_X : Integrable (fun ω => exp (t * X ω)) μ)
    (h_int_Y : Integrable (fun ω => exp (t * Y ω)) μ) :
    Integrable (fun ω => exp (t * (X + Y) ω)) μ := by
  simp_rw [Pi.add_apply, mul_add, exp_add]
  exact (h_indep.exp_mul t t).integrable_mul h_int_X h_int_Y

theorem iIndepFun.integrable_exp_mul_sum [IsFiniteMeasure μ] {X : ι → Ω → ℝ}
    (h_indep : iIndepFun (fun _ => inferInstance) X μ) (h_meas : ∀ i, Measurable (X i))
    {s : Finset ι} (h_int : ∀ i ∈ s, Integrable (fun ω => exp (t * X i ω)) μ) :
    Integrable (fun ω => exp (t * (∑ i ∈ s, X i) ω)) μ := by
  classical
  induction' s using Finset.induction_on with i s hi_notin_s h_rec h_int
  · simp only [Pi.zero_apply, sum_apply, sum_empty, mul_zero, exp_zero]
    exact integrable_const _
  · have : ∀ i : ι, i ∈ s → Integrable (fun ω : Ω => exp (t * X i ω)) μ := fun i hi =>
      h_int i (mem_insert_of_mem hi)
    specialize h_rec this
    rw [sum_insert hi_notin_s]
    refine IndepFun.integrable_exp_mul_add ?_ (h_int i (mem_insert_self _ _)) h_rec
    exact (h_indep.indepFun_finset_sum_of_not_mem h_meas hi_notin_s).symm

theorem iIndepFun.mgf_sum {X : ι → Ω → ℝ}
    (h_indep : iIndepFun (fun _ => inferInstance) X μ) (h_meas : ∀ i, Measurable (X i))
    (s : Finset ι) : mgf (∑ i ∈ s, X i) μ t = ∏ i ∈ s, mgf (X i) μ t := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  classical
  induction' s using Finset.induction_on with i s hi_notin_s h_rec h_int
  · simp only [sum_empty, mgf_zero_fun, measure_univ, ENNReal.one_toReal, prod_empty]
  · have h_int' : ∀ i : ι, AEStronglyMeasurable (fun ω : Ω => exp (t * X i ω)) μ := fun i =>
      ((h_meas i).const_mul t).exp.aestronglyMeasurable
    rw [sum_insert hi_notin_s,
      IndepFun.mgf_add (h_indep.indepFun_finset_sum_of_not_mem h_meas hi_notin_s).symm (h_int' i)
        (aestronglyMeasurable_exp_mul_sum fun i _ => h_int' i),
      h_rec, prod_insert hi_notin_s]

theorem iIndepFun.cgf_sum {X : ι → Ω → ℝ}
    (h_indep : iIndepFun (fun _ => inferInstance) X μ) (h_meas : ∀ i, Measurable (X i))
    {s : Finset ι} (h_int : ∀ i ∈ s, Integrable (fun ω => exp (t * X i ω)) μ) :
    cgf (∑ i ∈ s, X i) μ t = ∑ i ∈ s, cgf (X i) μ t := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  simp_rw [cgf]
  rw [← log_prod _ _ fun j hj => ?_]
  · rw [h_indep.mgf_sum h_meas]
  · exact (mgf_pos (h_int j hj)).ne'

/-- **Chernoff bound** on the upper tail of a real random variable. -/
theorem measure_ge_le_exp_mul_mgf [IsFiniteMeasure μ] (ε : ℝ) (ht : 0 ≤ t)
    (h_int : Integrable (fun ω => exp (t * X ω)) μ) :
    (μ {ω | ε ≤ X ω}).toReal ≤ exp (-t * ε) * mgf X μ t := by
  rcases ht.eq_or_lt with ht_zero_eq | ht_pos
  · rw [ht_zero_eq.symm]
    simp only [neg_zero, zero_mul, exp_zero, mgf_zero', one_mul]
    gcongr
    exacts [measure_ne_top _ _, Set.subset_univ _]
  calc
    (μ {ω | ε ≤ X ω}).toReal = (μ {ω | exp (t * ε) ≤ exp (t * X ω)}).toReal := by
      congr with ω
      simp only [Set.mem_setOf_eq, exp_le_exp, gt_iff_lt]
      exact ⟨fun h => mul_le_mul_of_nonneg_left h ht_pos.le,
        fun h => le_of_mul_le_mul_left h ht_pos⟩
    _ ≤ (exp (t * ε))⁻¹ * μ[fun ω => exp (t * X ω)] := by
      have : exp (t * ε) * (μ {ω | exp (t * ε) ≤ exp (t * X ω)}).toReal ≤
          μ[fun ω => exp (t * X ω)] :=
        mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun x => (exp_pos _).le) h_int _
      rwa [mul_comm (exp (t * ε))⁻¹, ← div_eq_mul_inv, le_div_iff₀' (exp_pos _)]
    _ = exp (-t * ε) * mgf X μ t := by rw [neg_mul, exp_neg]; rfl

/-- **Chernoff bound** on the lower tail of a real random variable. -/
theorem measure_le_le_exp_mul_mgf [IsFiniteMeasure μ] (ε : ℝ) (ht : t ≤ 0)
    (h_int : Integrable (fun ω => exp (t * X ω)) μ) :
    (μ {ω | X ω ≤ ε}).toReal ≤ exp (-t * ε) * mgf X μ t := by
  rw [← neg_neg t, ← mgf_neg, neg_neg, ← neg_mul_neg (-t)]
  refine Eq.trans_le ?_ (measure_ge_le_exp_mul_mgf (-ε) (neg_nonneg.mpr ht) ?_)
  · congr with ω
    simp only [Pi.neg_apply, neg_le_neg_iff]
  · simp_rw [Pi.neg_apply, neg_mul_neg]
    exact h_int

/-- **Chernoff bound** on the upper tail of a real random variable. -/
theorem measure_ge_le_exp_cgf [IsFiniteMeasure μ] (ε : ℝ) (ht : 0 ≤ t)
    (h_int : Integrable (fun ω => exp (t * X ω)) μ) :
    (μ {ω | ε ≤ X ω}).toReal ≤ exp (-t * ε + cgf X μ t) := by
  refine (measure_ge_le_exp_mul_mgf ε ht h_int).trans ?_
  rw [exp_add]
  exact mul_le_mul le_rfl (le_exp_log _) mgf_nonneg (exp_pos _).le

/-- **Chernoff bound** on the lower tail of a real random variable. -/
theorem measure_le_le_exp_cgf [IsFiniteMeasure μ] (ε : ℝ) (ht : t ≤ 0)
    (h_int : Integrable (fun ω => exp (t * X ω)) μ) :
    (μ {ω | X ω ≤ ε}).toReal ≤ exp (-t * ε + cgf X μ t) := by
  refine (measure_le_le_exp_mul_mgf ε ht h_int).trans ?_
  rw [exp_add]
  exact mul_le_mul le_rfl (le_exp_log _) mgf_nonneg (exp_pos _).le

end MomentGeneratingFunction

section GeneratingFunctionDerivatives

lemma aemeasurable_expt {X : Ω → ℝ} (t : ℝ) (hX : AEMeasurable X μ) :
    AEStronglyMeasurable (fun ω ↦ rexp (t * (X ω))) μ :=
  aestronglyMeasurable_iff_aemeasurable.mpr <| measurable_exp.comp_aemeasurable' (hX.const_mul t)

lemma integrable_expt [IsFiniteMeasure μ] {X : Ω → ℝ} (t b : ℝ) (ht : t > 0)
    (hX : AEMeasurable X μ) (hb : ∀ᵐ ω ∂μ, X ω ≤ b) :
    Integrable (fun ω ↦ exp (t * (X ω))) μ := by
  have hm1 : HasFiniteIntegral (fun ω ↦ rexp (t * X ω)) μ := by
    have b' : ∀ᵐ ω ∂μ, rexp (t * X ω) ≤ rexp (t * b) := by
      filter_upwards [hb] with ω hb
      using exp_le_exp.mpr (mul_le_mul_of_nonneg_left hb (le_of_lt ht))
    have p : ∀ᵐ ω ∂μ, ‖rexp (t * X ω)‖₊ ≤ rexp (t * b) := by
      filter_upwards [b'] with ω b'
      rw [(by simp only [coe_nnnorm, norm_eq_abs, abs_exp] : ‖rexp (t * X ω)‖₊ = rexp (t * X ω))]
      exact b'
    have p'' : ∫⁻ ω, ‖rexp (t * X ω)‖₊ ∂μ ≤ ∫⁻ _, ‖rexp (t * b)‖₊ ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [p] with ω p
      simp only [ENNReal.coe_le_coe]
      rw [← (by simp only [coe_nnnorm, norm_eq_abs, abs_exp] : ‖rexp (t * b)‖₊ = rexp (t * b))] at p
      exact p
    suffices ∫⁻ _, ↑‖rexp (t * b)‖₊ ∂μ < ⊤ from lt_of_le_of_lt p'' this
    simp only [lintegral_const]
    apply ENNReal.mul_lt_top ENNReal.coe_lt_top (IsFiniteMeasure.measure_univ_lt_top)
  exact ⟨aestronglyMeasurable_iff_aemeasurable.mpr <|
    measurable_exp.comp_aemeasurable' (hX.const_mul t), hm1⟩

lemma integrable_expt_bound [IsFiniteMeasure μ] {X : Ω → ℝ} {t a b : ℝ} (hX : AEMeasurable X μ)
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    Integrable (fun ω ↦ exp (t * (X ω))) μ := by
  have ha : ∀ᵐ ω ∂μ, a ≤ X ω := h.mono fun ω h ↦ h.1
  cases lt_trichotomy t 0 with
  | inr ht => cases ht with
    | inr ht => exact integrable_expt t b ht hX (h.mono fun ω h ↦ h.2)
    | inl ht => rw [ht]; simp only [zero_mul, exp_zero, integrable_const]
  | inl ht =>
    rw [(by ext ω; rw [(by ring : - t * (- X ω) = t * X ω)] :
      (fun ω ↦ rexp (t * X ω)) = (fun ω ↦ rexp (- t * (- X ω))))]
    exact integrable_expt _ _ (by linarith : -t > 0) hX.neg
      (by filter_upwards [ha] with ω ha using neg_le_neg ha)

lemma tilt_var_bound [IsProbabilityMeasure μ] (a b t : ℝ) {X : Ω → ℝ}
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b)
    (hX : AEMeasurable X μ) :
    variance X (μ.tilted (fun ω ↦ t * X ω)) ≤ ((b - a) / 2) ^ 2 := by
  have _ : IsProbabilityMeasure (μ.tilted fun ω ↦ t * X ω) :=
    isProbabilityMeasure_tilted (integrable_expt_bound hX h)
  exact variance_le_sq_of_bounded
      ((tilted_absolutelyContinuous μ fun ω ↦ t * X ω) h)
      (hX.mono_ac (tilted_absolutelyContinuous μ fun ω ↦ t * X ω))

theorem integrable_bounded [IsFiniteMeasure μ] (a b : ℝ)
    {X : Ω → ℝ} (hX : AEMeasurable X μ) (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    Integrable X μ :=
  memℒp_one_iff_integrable.mp
    memℒp_of_bounded h (aestronglyMeasurable_iff_aemeasurable.mpr hX)

/-- Derivation of `mgf X μ t` is `μ[exp (t * X ω) * X ω]`.
In order to deal with the differentiation of parametric integrals,
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` are used in the proof. -/
theorem tilt_first_deriv [IsFiniteMeasure μ] (t a b : ℝ)
    {X : Ω → ℝ} (hX : AEMeasurable X μ) (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b):
    let g := fun t ↦ mgf X μ t
    let g' := fun t ↦ μ[fun ω ↦ rexp (t * X ω) * X ω]
    Integrable (fun ω ↦ rexp (t * X ω) * X ω) μ → HasDerivAt g (g' t) t := by
  have ha : ∀ᵐ ω ∂μ, a ≤ X ω := h.mono fun ω h ↦ h.1
  have hb : ∀ᵐ ω ∂μ, X ω ≤ b := h.mono fun ω h ↦ h.2
  set c := max ‖a‖ ‖b‖
  set e := (fun t ↦ fun ω ↦ rexp (t * X ω))
  set e' := (fun t ↦ fun ω ↦ rexp (t * X ω) * X ω)
  suffices MeasureTheory.Integrable (e' t) μ ∧
    HasDerivAt (fun t ↦ μ[e t]) (μ[e' t]) t from by
    dsimp [mgf]
    simp only [this.2, implies_true]
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
  · exact LE.le.trans_lt (abs_nonneg t) (lt_add_one |t|)
  · exact Filter.Eventually.of_forall
      (by intro t'; apply aemeasurable_expt _ hX : ∀ (x : ℝ), AEStronglyMeasurable (e x) μ)
  · simp only [e]; apply integrable_expt_bound hX h
  · simp only [e']
    apply AEMeasurable.aestronglyMeasurable;
    apply AEMeasurable.mul _ hX
    apply Measurable.comp_aemeasurable' _ _
    · exact measurable_exp
    · exact hX.const_mul t
  · set bound := fun ω ↦ rexp ((2 * |t| + 1) * |X ω|) * |X ω|
    apply ae_of_all μ
    change ∀ y, ∀ x ∈ Metric.ball t (|t| + 1), ‖e' x y‖ ≤ bound y
    intros y x b1
    calc
    _ = |rexp (x * X y)| * |X y| := abs_mul (rexp (x * X y)) (X y)
    _ = rexp (x * X y) * |X y| := by simp only [abs_exp]
    _ ≤ rexp (|x * X y|) * |X y| :=
      mul_le_mul_of_nonneg_right (exp_le_exp.mpr (le_abs_self (x * X y))) (abs_nonneg (X y))
    _ = rexp (|x| * |X y|) * |X y| := by
      rw [abs_mul x (X y)]
    _ ≤ rexp ((2 * |t| + 1) * |X y|) * |X y| := by
      have p2 : |x| ≤ 2 * |t| + 1 := by
        simp only [Metric.mem_ball] at b1
        linarith [le_trans' (le_of_lt b1) (abs_sub_abs_le_abs_sub x t)]
      exact mul_le_mul_of_nonneg_right
        (exp_le_exp.mpr (mul_le_mul_of_nonneg_right p2 (abs_nonneg (X y)))) (abs_nonneg (X y))
  · apply MeasureTheory.Integrable.bdd_mul'
    · exact MeasureTheory.Integrable.abs (integrable_bounded a b hX h)
    · apply aemeasurable_expt (2 * |t| + 1) _
      apply Measurable.comp_aemeasurable' _ hX
      apply measurable_norm
    · filter_upwards [ha, hb] with ω ha hb
      change ‖rexp ((2 * |t| + 1) * |X ω|)‖ ≤ rexp ((2 * |t| + 1) * |c|)
      simp only [norm_eq_abs, abs_exp, exp_le_exp]
      exact mul_le_mul_of_nonneg_left (le_trans' (le_abs_self (max ‖a‖ ‖b‖))
        (abs_le_max_abs_abs ha hb)) (by linarith [abs_nonneg t] : 0 ≤ 2 * |t| + 1)
  suffices ∀ ω, ∀ x ∈ Metric.ball t (|t| + 1),
    HasDerivAt (fun x ↦ e x ω) (e' x ω) x from ae_of_all μ this
  intros ω x _
  exact HasDerivAt.exp (hasDerivAt_mul_const (X ω))

/-- Derivation of `μ[fun ω ↦ rexp (t * X ω) * X ω]` is `μ[fun ω ↦ rexp (t * X ω) * X ω ^ 2]`.
In order to deal with the differentiation of parametric integrals,
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` are used in the proof. -/
theorem tilt_second_deriv  [IsFiniteMeasure μ] (t a b : ℝ)
    {X : Ω → ℝ} (hX : AEMeasurable X μ) (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    let g := fun t ↦ μ[fun ω ↦ rexp (t * X ω) * X ω]
    let g' := fun t ↦ μ[fun ω ↦ rexp (t * X ω) * X ω ^ 2]
    Integrable (fun ω ↦ rexp (t * X ω) * (X ω ^ 2)) μ → HasDerivAt g (g' t) t := by
  have ha : ∀ᵐ ω ∂μ, a ≤ X ω := h.mono fun ω h ↦ h.1
  have hb : ∀ᵐ ω ∂μ, X ω ≤ b := h.mono fun ω h ↦ h.2
  set c := max ‖a‖ ‖b‖
  set e := (fun t ↦ fun ω ↦ rexp (t * X ω) * X ω)
  set e' := (fun t ↦ fun ω ↦ rexp (t * X ω) * (X ω ^ 2))
  suffices MeasureTheory.Integrable (e' t) μ ∧
    HasDerivAt (fun t ↦ μ[e t]) (μ[e' t]) t from by
    simp only [this.2, implies_true]
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
  · exact LE.le.trans_lt (abs_nonneg t) (lt_add_one |t|)
  · apply Filter.Eventually.of_forall
    intro t'
    dsimp only [e]
    rw [aestronglyMeasurable_iff_aemeasurable]
    apply AEMeasurable.mul _ hX
    exact Measurable.comp_aemeasurable' measurable_exp (hX.const_mul t')
  · simp only [e];
    apply MeasureTheory.Integrable.bdd_mul'
      (integrable_bounded a b hX h) (aemeasurable_expt t hX)
    · filter_upwards [ha, hb] with ω ha hb
      change ‖rexp (t * X ω)‖ ≤ rexp (|t| * c)
      simp only [norm_eq_abs, abs_exp, exp_le_exp]
      calc
      _ ≤ |t * X ω| := le_abs_self (t * X ω)
      _ = |t| * |X ω| := abs_mul t (X ω)
      _ ≤ |t| * c := by
        apply mul_le_mul_of_nonneg_left
        rw [← (by dsimp only [c]; simp only
          [norm_eq_abs, abs_eq_self, le_max_iff, abs_nonneg, or_self] :
          |c| = c)]
        exact le_trans' (le_abs_self (max ‖a‖ ‖b‖)) (abs_le_max_abs_abs ha hb)
        exact abs_nonneg t
  · dsimp only [e']
    rw [aestronglyMeasurable_iff_aemeasurable]
    apply AEMeasurable.mul
    · apply Measurable.comp_aemeasurable' _ _
      · exact measurable_exp
      · exact hX.const_mul t
    exact hX.pow_const 2
  · set bound := fun ω ↦ rexp ((2 * |t| + 1) * |X ω|) * (|X ω| ^ 2)
    suffices ∀ ω, ∀ x ∈ Metric.ball t (|t| + 1), ‖e' x ω‖ ≤ bound ω from ae_of_all μ this
    intros ω x h
    dsimp [e', bound]
    simp only [sq_abs]
    change |rexp (x * X ω) * X ω ^ 2| ≤ rexp ((2 * |t| + 1) * |X ω|) * X ω ^ 2
    calc
    _ = |rexp (x * X ω)| * |(X ω ^ 2)| := abs_mul (rexp (x * X ω)) (X ω ^ 2)
    _ = rexp (x * X ω) * (X ω ^ 2) := by simp only [abs_exp, abs_pow, sq_abs]
    _ ≤ rexp ((2 * |t| + 1) * |X ω|) * X ω ^ 2 := by
      suffices rexp (x * X ω) ≤
        rexp ((2 * |t| + 1) * |X ω|) from mul_le_mul_of_nonneg_right this (sq_nonneg (X ω))
      simp only [exp_le_exp]
      calc
      _ ≤ |x * X ω| := le_abs_self (x * X ω)
      _ = |x| * |X ω| := abs_mul x (X ω)
      _ ≤ (2 * |t| + 1) * |X ω| := by
        suffices |x| ≤ 2 * |t| + 1 from mul_le_mul_of_nonneg_right this (abs_nonneg (X ω))
        simp only [Metric.mem_ball] at h
        linarith [le_trans' (le_of_lt h) (abs_sub_abs_le_abs_sub x t)]
  · apply MeasureTheory.Integrable.bdd_mul'
    · simp only [sq_abs]
      rw [(by ext ω; ring : (fun ω ↦ X ω ^ 2) = (fun ω ↦ X ω * X ω))]
      apply MeasureTheory.Integrable.bdd_mul'
        (integrable_bounded a b hX h) (aestronglyMeasurable_iff_aemeasurable.mpr hX)
      · filter_upwards [ha, hb] with x ha hb
        exact (by simp only [norm_eq_abs]; exact
          le_trans' (le_abs_self (max ‖a‖ ‖b‖)) (abs_le_max_abs_abs ha hb) : ‖X x‖ ≤ |c|)
    · apply aemeasurable_expt (2 * |t| + 1) _
      apply Measurable.comp_aemeasurable' _ hX
      apply measurable_norm
    · filter_upwards [ha, hb] with ω ha hb
      change ‖rexp ((2 * |t| + 1) * |X ω|)‖ ≤ ‖rexp ((2 * |t| + 1) * c)‖
      simp only [norm_eq_abs, abs_exp, exp_le_exp]
      rw [← (abs_eq_self.mpr (le_trans' (le_max_left |a| ‖b‖) (abs_nonneg a)) : |c| = c)]
      exact mul_le_mul_of_nonneg_left
        (le_trans' (le_abs_self (max ‖a‖ ‖b‖)) (abs_le_max_abs_abs ha hb))
        (by linarith [abs_nonneg t] : 0 ≤ 2 * |t| + 1)
  suffices ∀ ω, ∀ x ∈ Metric.ball t (|t| + 1),
    HasDerivAt (fun x ↦ e x ω) (e' x ω) x from ae_of_all μ this
  intros ω x _
  dsimp only [e, e']
  suffices HasDerivAt (fun x ↦ rexp (x * X ω)) (rexp (x * X ω) * X ω) x from by
    rw [(by ring : rexp (x * X ω) * X ω ^ 2 = (rexp (x * X ω) * X ω) * X ω)]
    exact HasDerivAt.mul_const this (X ω)
  exact HasDerivAt.exp (hasDerivAt_mul_const (X ω))

theorem integrable_deriv_expt [IsFiniteMeasure μ] (t a b : ℝ)
    {X : Ω → ℝ} (hX : AEMeasurable X μ) (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b):
    Integrable (fun ω ↦ rexp (t * X ω) * X ω) μ := by
  have ha : ∀ᵐ ω ∂μ, a ≤ X ω := h.mono fun ω h ↦ h.1
  have hb : ∀ᵐ ω ∂μ, X ω ≤ b := h.mono fun ω h ↦ h.2
  apply MeasureTheory.Integrable.bdd_mul'
    (integrable_bounded a b hX h) (aemeasurable_expt _ hX)
  · set c := max ‖a‖ ‖b‖
    filter_upwards [ha, hb] with ω ha hb
    change ‖rexp (t * X ω)‖ ≤ ‖rexp (|t| * c)‖
    simp only [norm_eq_abs, abs_exp, exp_le_exp]
    rw [← (abs_eq_self.mpr (le_trans' (le_max_left |a| ‖b‖) (abs_nonneg a)) : |c| = c)]
    calc
    _ ≤ |t * X ω| := le_abs_self (t * X ω)
    _ = |t| * |X ω| := abs_mul t (X ω)
    _ ≤ |t| * |c| :=
      mul_le_mul_of_nonneg_left (le_trans' (le_abs_self (max ‖a‖ ‖b‖))
        (abs_le_max_abs_abs ha hb) : |X ω| ≤ |c|) (abs_nonneg t)

theorem integral_tilted [IsFiniteMeasure μ]
    (t : ℝ) (f : ℝ → ℝ) {X : Ω → ℝ} (hX : AEMeasurable X μ):
    (μ.tilted (fun ω ↦ t * X ω))[fun ω ↦ f (X ω)] =
    (μ[fun ω ↦ rexp (t * X ω) * f (X ω)]) / mgf X μ t := by
  calc
  _ = (∫ ω, ((∂Measure.tilted μ fun ω ↦ t * X ω/∂μ) ω).toReal • f (X ω) ∂μ) :=
    Eq.symm (MeasureTheory.integral_rnDeriv_smul (tilted_absolutelyContinuous μ fun ω ↦ t * X ω))
  _ = ∫ ω, (rexp (t * X ω) / μ[fun ω ↦ rexp (t * X ω)]) * f (X ω) ∂μ := by
    apply integral_congr_ae
    filter_upwards [rnDeriv_tilted_left_self (hX.const_mul t)] with ω w
    rw [w]
    simp only [smul_eq_mul, mul_eq_mul_right_iff, ENNReal.toReal_ofReal_eq_iff]
    left
    have q2 : 0 ≤ μ[fun ω ↦ rexp (t * X ω)] := by
      apply integral_nonneg
      apply Pi.le_def.mpr _
      intro i
      simp only [Pi.zero_apply]
      exact exp_nonneg (t * X i)
    exact div_nonneg (exp_nonneg (t * X ω)) q2
  _ = (∫ ω, (rexp (t * X ω) * f (X ω)) / (μ[fun ω ↦ rexp (t * X ω)]) ∂μ) := by
    refine integral_congr_ae (ae_of_all μ fun a ↦ ?_)
    simp only
    ring
  _ = (∫ ω, rexp (t * X ω) * f (X ω) ∂μ) / μ[fun ω ↦ rexp (t * X ω)] :=
    integral_div (μ[fun ω ↦ rexp (t * X ω)]) fun a ↦ rexp (t * X a) * f (X a)

/-! ### Derivatives of cumulant-/

/-- First derivative of cumulant `cgf X μ f`.
It can be described by exponential tilting.-/
theorem cum_deriv_one [IsFiniteMeasure μ] [NeZero μ] (a b : ℝ)
    {X : Ω → ℝ} (hX : AEMeasurable X μ) (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    let f := fun t ↦ cgf X μ t
    let f' := fun t ↦ (μ.tilted (fun ω ↦ t * X ω)) [X]
    ∀ x : ℝ, HasDerivAt f (f' x) x := by
  intros f f' t
  set g := fun t ↦ μ[fun ω ↦ rexp (t * X ω)]
  set g' := fun t ↦ μ[fun ω ↦ rexp (t * X ω) * X ω]
  dsimp [f']
  have r0 : ((μ.tilted (fun ω ↦ t * X ω)) [fun ω ↦ id (X ω)]) =
    μ[fun ω ↦ rexp (t * X ω) * id (X ω)] / μ[fun ω ↦ rexp (t * X ω)] :=
    integral_tilted t id hX
  simp at r0
  rw [r0]
  apply HasDerivAt.log
    (tilt_first_deriv _ _ _ hX h (integrable_deriv_expt t a b hX h))
    (mgf_pos' (NeZero.ne μ) (integrable_expt_bound hX h)).ne'

/-- Second derivative of cumulant `cgf X μ f`-/
theorem cum_deriv_two [IsFiniteMeasure μ] [NeZero μ] (a b : ℝ)
    {X : Ω → ℝ} (hX : AEMeasurable X μ) (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    let g' := fun t ↦ (μ.tilted (fun ω ↦ t * X ω))[X];
    let g'' := fun t ↦ (μ.tilted (fun ω ↦ t * X ω)) [X ^ 2] - (μ.tilted (fun ω ↦ t * X ω))[X] ^ 2;
    ∀ x : ℝ, HasDerivAt g' (g'' x) x := by
  have ha : ∀ᵐ ω ∂μ, a ≤ X ω := h.mono fun ω h ↦ h.1
  have hb : ∀ᵐ ω ∂μ, X ω ≤ b := h.mono fun ω h ↦ h.2
  intro g' g'' t
  have r0 : (fun t ↦ ((μ.tilted (fun ω ↦ t * X ω))[fun ω ↦ id (X ω)])) =
    fun t ↦ μ[fun ω ↦ rexp (t * X ω) * id (X ω)] / μ[fun ω ↦ rexp (t * X ω)] := by
    ext t
    exact integral_tilted t id hX
  have r01 : (μ.tilted (fun ω ↦ t * X ω))[fun ω ↦ id (X ω)]  =
    μ[fun ω ↦ rexp (t * X ω) * id (X ω)] / μ[fun ω ↦ rexp (t * X ω)] :=
    integral_tilted t id hX
  have r0' : (μ.tilted (fun ω ↦ t * X ω))[fun ω ↦ (fun s ↦ s ^ 2) (X ω)] =
    μ[fun ω ↦ rexp (t * X ω) * (fun s ↦ s ^ 2) (X ω)] / μ[fun ω ↦ rexp (t * X ω)] :=
    integral_tilted t (fun x ↦ x ^ 2) hX
  simp only [id_eq] at r0 r0' r01
  dsimp [g', g'']
  rw [r0, r0', r01]
  field_simp
  have p : ((μ[fun ω ↦ rexp (t * X ω) * X ω ^ 2]) / μ[fun ω ↦ rexp (t * X ω)]) =
  ((μ[fun ω ↦ rexp (t * X ω) * X ω ^ 2]) * (μ[fun ω ↦ rexp (t * X ω)])) /
  ((μ[fun ω ↦ rexp (t * X ω)]) * (μ[fun ω ↦ rexp (t * X ω)])) := by
    apply Eq.symm (mul_div_mul_right (∫ ω, rexp (t * X ω) * X ω ^ 2 ∂μ)
    (μ[fun ω ↦ rexp (t * X ω)]) _)
    exact (mgf_pos' (NeZero.ne μ) (integrable_expt_bound hX h)).ne'
  rw [p, Eq.symm (pow_two (∫ ω, rexp (t * X ω) ∂μ))]
  have p'' : (((μ[fun ω ↦ rexp (t * X ω) * X ω ^ 2]) *
    (μ[fun ω ↦ rexp (t * X ω)])) / (μ[fun ω ↦ rexp (t * X ω)]) ^ 2 -
  (μ[fun ω ↦ rexp (t * X ω) * X ω]) ^ 2 / (μ[fun ω ↦ rexp (t * X ω)]) ^ 2) =
  ((μ[fun ω ↦ exp (t * (X ω)) * (X ω) ^ 2] *
    mgf X μ t) -
    (μ[fun ω ↦ exp (t * (X ω)) * X ω] * μ[fun ω ↦ exp (t * (X ω)) * X ω])) /
    (mgf X μ t ^ 2) := by
    rw [Eq.symm (pow_two (∫ ω, (fun ω ↦ rexp (t * X ω) * X ω) ω ∂μ))]
    exact
      div_sub_div_same ((μ[fun ω ↦ rexp (t * X ω) * X ω ^ 2]) * μ[fun ω ↦ rexp (t * X ω)])
        ((μ[fun ω ↦ rexp (t * X ω) * X ω]) ^ 2) ((μ[fun ω ↦ rexp (t * X ω)]) ^ 2)
  rw [p'']
  apply HasDerivAt.div
  · set c := max ‖a‖ ‖b‖
    apply tilt_second_deriv _ _ _ hX h
    apply MeasureTheory.Integrable.bdd_mul'
    · rw [(by ext ω; ring : (fun ω ↦ X ω ^ 2) = (fun ω ↦ X ω * X ω))]
      apply MeasureTheory.Integrable.bdd_mul'
        (integrable_bounded a b hX h) (aestronglyMeasurable_iff_aemeasurable.mpr hX)
      · filter_upwards [ha, hb] with x ha hb
        exact (by simp only [norm_eq_abs];
                  exact le_trans' (le_abs_self (max ‖a‖ ‖b‖)) (abs_le_max_abs_abs ha hb) :
              ‖X x‖ ≤ |c|)
    · exact aemeasurable_expt t hX
    · simp only [norm_eq_abs, abs_exp]
      filter_upwards [ha, hb] with ω ha hb
      change rexp (t * X ω) ≤ rexp (|t| * |c|)
      simp only [exp_le_exp]
      calc
      _ ≤ |t * X ω| := le_abs_self (t * X ω)
      _ = |t| * |X ω| := abs_mul t (X ω)
      _ ≤ |t| * |c| := mul_le_mul_of_nonneg_left (le_trans' (le_abs_self (max ‖a‖ ‖b‖))
                      (abs_le_max_abs_abs ha hb)) (abs_nonneg t)
  · apply (tilt_first_deriv _ _ _ hX h)
          (integrable_deriv_expt t a b hX h)
  · exact (mgf_pos' (NeZero.ne μ) (integrable_expt_bound hX h)).ne'

end GeneratingFunctionDerivatives

end ProbabilityTheory
