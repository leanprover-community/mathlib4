/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Variance

#align_import probability.moments from "leanprover-community/mathlib"@"85453a2a14be8da64caf15ca50930cf4c6e5d8de"

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

-/


open MeasureTheory Filter Finset Real

noncomputable section

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal

namespace ProbabilityTheory

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {X : Ω → ℝ} {p : ℕ} {μ : Measure Ω}

/-- Moment of a real random variable, `μ[X ^ p]`. -/
def moment (X : Ω → ℝ) (p : ℕ) (μ : Measure Ω) : ℝ :=
  μ[X ^ p]
#align probability_theory.moment ProbabilityTheory.moment

/-- Central moment of a real random variable, `μ[(X - μ[X]) ^ p]`. -/
def centralMoment (X : Ω → ℝ) (p : ℕ) (μ : Measure Ω) : ℝ := by
  have m := fun (x : Ω) => μ[X] -- Porting note: Lean deems `μ[(X - fun x => μ[X]) ^ p]` ambiguous
  exact μ[(X - m) ^ p]
#align probability_theory.central_moment ProbabilityTheory.centralMoment

@[simp]
theorem moment_zero (hp : p ≠ 0) : moment 0 p μ = 0 := by
  simp only [moment, hp, zero_pow, Ne, not_false_iff, Pi.zero_apply, integral_const,
    smul_eq_mul, mul_zero, integral_zero]
#align probability_theory.moment_zero ProbabilityTheory.moment_zero

@[simp]
theorem centralMoment_zero (hp : p ≠ 0) : centralMoment 0 p μ = 0 := by
  simp only [centralMoment, hp, Pi.zero_apply, integral_const, smul_eq_mul,
    mul_zero, zero_sub, Pi.pow_apply, Pi.neg_apply, neg_zero, zero_pow, Ne, not_false_iff]
#align probability_theory.central_moment_zero ProbabilityTheory.centralMoment_zero

theorem centralMoment_one' [IsFiniteMeasure μ] (h_int : Integrable X μ) :
    centralMoment X 1 μ = (1 - (μ Set.univ).toReal) * μ[X] := by
  simp only [centralMoment, Pi.sub_apply, pow_one]
  rw [integral_sub h_int (integrable_const _)]
  simp only [sub_mul, integral_const, smul_eq_mul, one_mul]
#align probability_theory.central_moment_one' ProbabilityTheory.centralMoment_one'

@[simp]
theorem centralMoment_one [IsProbabilityMeasure μ] : centralMoment X 1 μ = 0 := by
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
#align probability_theory.central_moment_one ProbabilityTheory.centralMoment_one

theorem centralMoment_two_eq_variance [IsFiniteMeasure μ] (hX : Memℒp X 2 μ) :
    centralMoment X 2 μ = variance X μ := by rw [hX.variance_eq]; rfl
#align probability_theory.central_moment_two_eq_variance ProbabilityTheory.centralMoment_two_eq_variance

section MomentGeneratingFunction

variable {t : ℝ}

/-- Moment generating function of a real random variable `X`: `fun t => μ[exp(t*X)]`. -/
def mgf (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) : ℝ :=
  μ[fun ω => exp (t * X ω)]
#align probability_theory.mgf ProbabilityTheory.mgf

/-- Cumulant generating function of a real random variable `X`: `fun t => log μ[exp(t*X)]`. -/
def cgf (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) : ℝ :=
  log (mgf X μ t)
#align probability_theory.cgf ProbabilityTheory.cgf

@[simp]
theorem mgf_zero_fun : mgf 0 μ t = (μ Set.univ).toReal := by
  simp only [mgf, Pi.zero_apply, mul_zero, exp_zero, integral_const, smul_eq_mul, mul_one]
#align probability_theory.mgf_zero_fun ProbabilityTheory.mgf_zero_fun

@[simp]
theorem cgf_zero_fun : cgf 0 μ t = log (μ Set.univ).toReal := by simp only [cgf, mgf_zero_fun]
#align probability_theory.cgf_zero_fun ProbabilityTheory.cgf_zero_fun

@[simp]
theorem mgf_zero_measure : mgf X (0 : Measure Ω) t = 0 := by simp only [mgf, integral_zero_measure]
#align probability_theory.mgf_zero_measure ProbabilityTheory.mgf_zero_measure

@[simp]
theorem cgf_zero_measure : cgf X (0 : Measure Ω) t = 0 := by
  simp only [cgf, log_zero, mgf_zero_measure]
#align probability_theory.cgf_zero_measure ProbabilityTheory.cgf_zero_measure

@[simp]
theorem mgf_const' (c : ℝ) : mgf (fun _ => c) μ t = (μ Set.univ).toReal * exp (t * c) := by
  simp only [mgf, integral_const, smul_eq_mul]
#align probability_theory.mgf_const' ProbabilityTheory.mgf_const'

-- @[simp] -- Porting note: `simp only` already proves this
theorem mgf_const (c : ℝ) [IsProbabilityMeasure μ] : mgf (fun _ => c) μ t = exp (t * c) := by
  simp only [mgf_const', measure_univ, ENNReal.one_toReal, one_mul]
#align probability_theory.mgf_const ProbabilityTheory.mgf_const

@[simp]
theorem cgf_const' [IsFiniteMeasure μ] (hμ : μ ≠ 0) (c : ℝ) :
    cgf (fun _ => c) μ t = log (μ Set.univ).toReal + t * c := by
  simp only [cgf, mgf_const']
  rw [log_mul _ (exp_pos _).ne']
  · rw [log_exp _]
  · rw [Ne, ENNReal.toReal_eq_zero_iff, Measure.measure_univ_eq_zero]
    simp only [hμ, measure_ne_top μ Set.univ, or_self_iff, not_false_iff]
#align probability_theory.cgf_const' ProbabilityTheory.cgf_const'

@[simp]
theorem cgf_const [IsProbabilityMeasure μ] (c : ℝ) : cgf (fun _ => c) μ t = t * c := by
  simp only [cgf, mgf_const, log_exp]
#align probability_theory.cgf_const ProbabilityTheory.cgf_const

@[simp]
theorem mgf_zero' : mgf X μ 0 = (μ Set.univ).toReal := by
  simp only [mgf, zero_mul, exp_zero, integral_const, smul_eq_mul, mul_one]
#align probability_theory.mgf_zero' ProbabilityTheory.mgf_zero'

-- @[simp] -- Porting note: `simp only` already proves this
theorem mgf_zero [IsProbabilityMeasure μ] : mgf X μ 0 = 1 := by
  simp only [mgf_zero', measure_univ, ENNReal.one_toReal]
#align probability_theory.mgf_zero ProbabilityTheory.mgf_zero

@[simp]
theorem cgf_zero' : cgf X μ 0 = log (μ Set.univ).toReal := by simp only [cgf, mgf_zero']
#align probability_theory.cgf_zero' ProbabilityTheory.cgf_zero'

-- @[simp] -- Porting note: `simp only` already proves this
theorem cgf_zero [IsProbabilityMeasure μ] : cgf X μ 0 = 0 := by
  simp only [cgf_zero', measure_univ, ENNReal.one_toReal, log_one]
#align probability_theory.cgf_zero ProbabilityTheory.cgf_zero

theorem mgf_undef (hX : ¬Integrable (fun ω => exp (t * X ω)) μ) : mgf X μ t = 0 := by
  simp only [mgf, integral_undef hX]
#align probability_theory.mgf_undef ProbabilityTheory.mgf_undef

theorem cgf_undef (hX : ¬Integrable (fun ω => exp (t * X ω)) μ) : cgf X μ t = 0 := by
  simp only [cgf, mgf_undef hX, log_zero]
#align probability_theory.cgf_undef ProbabilityTheory.cgf_undef

theorem mgf_nonneg : 0 ≤ mgf X μ t := by
  unfold mgf; positivity
#align probability_theory.mgf_nonneg ProbabilityTheory.mgf_nonneg

theorem mgf_pos' (hμ : μ ≠ 0) (h_int_X : Integrable (fun ω => exp (t * X ω)) μ) :
    0 < mgf X μ t := by
  simp_rw [mgf]
  have : ∫ x : Ω, exp (t * X x) ∂μ = ∫ x : Ω in Set.univ, exp (t * X x) ∂μ := by
    simp only [Measure.restrict_univ]
  rw [this, setIntegral_pos_iff_support_of_nonneg_ae _ _]
  · have h_eq_univ : (Function.support fun x : Ω => exp (t * X x)) = Set.univ := by
      ext1 x
      simp only [Function.mem_support, Set.mem_univ, iff_true_iff]
      exact (exp_pos _).ne'
    rw [h_eq_univ, Set.inter_univ _]
    refine Ne.bot_lt ?_
    simp only [hμ, ENNReal.bot_eq_zero, Ne, Measure.measure_univ_eq_zero, not_false_iff]
  · filter_upwards with x
    rw [Pi.zero_apply]
    exact (exp_pos _).le
  · rwa [integrableOn_univ]
#align probability_theory.mgf_pos' ProbabilityTheory.mgf_pos'

theorem mgf_pos [IsProbabilityMeasure μ] (h_int_X : Integrable (fun ω => exp (t * X ω)) μ) :
    0 < mgf X μ t :=
  mgf_pos' (IsProbabilityMeasure.ne_zero μ) h_int_X
#align probability_theory.mgf_pos ProbabilityTheory.mgf_pos

theorem mgf_neg : mgf (-X) μ t = mgf X μ (-t) := by simp_rw [mgf, Pi.neg_apply, mul_neg, neg_mul]
#align probability_theory.mgf_neg ProbabilityTheory.mgf_neg

theorem cgf_neg : cgf (-X) μ t = cgf X μ (-t) := by simp_rw [cgf, mgf_neg]
#align probability_theory.cgf_neg ProbabilityTheory.cgf_neg

/-- This is a trivial application of `IndepFun.comp` but it will come up frequently. -/
theorem IndepFun.exp_mul {X Y : Ω → ℝ} (h_indep : IndepFun X Y μ) (s t : ℝ) :
    IndepFun (fun ω => exp (s * X ω)) (fun ω => exp (t * Y ω)) μ := by
  have h_meas : ∀ t, Measurable fun x => exp (t * x) := fun t => (measurable_id'.const_mul t).exp
  change IndepFun ((fun x => exp (s * x)) ∘ X) ((fun x => exp (t * x)) ∘ Y) μ
  exact IndepFun.comp h_indep (h_meas s) (h_meas t)
#align probability_theory.indep_fun.exp_mul ProbabilityTheory.IndepFun.exp_mul

theorem IndepFun.mgf_add {X Y : Ω → ℝ} (h_indep : IndepFun X Y μ)
    (hX : AEStronglyMeasurable (fun ω => exp (t * X ω)) μ)
    (hY : AEStronglyMeasurable (fun ω => exp (t * Y ω)) μ) :
    mgf (X + Y) μ t = mgf X μ t * mgf Y μ t := by
  simp_rw [mgf, Pi.add_apply, mul_add, exp_add]
  exact (h_indep.exp_mul t t).integral_mul hX hY
#align probability_theory.indep_fun.mgf_add ProbabilityTheory.IndepFun.mgf_add

theorem IndepFun.mgf_add' {X Y : Ω → ℝ} (h_indep : IndepFun X Y μ) (hX : AEStronglyMeasurable X μ)
    (hY : AEStronglyMeasurable Y μ) : mgf (X + Y) μ t = mgf X μ t * mgf Y μ t := by
  have A : Continuous fun x : ℝ => exp (t * x) := by continuity
  have h'X : AEStronglyMeasurable (fun ω => exp (t * X ω)) μ :=
    A.aestronglyMeasurable.comp_aemeasurable hX.aemeasurable
  have h'Y : AEStronglyMeasurable (fun ω => exp (t * Y ω)) μ :=
    A.aestronglyMeasurable.comp_aemeasurable hY.aemeasurable
  exact h_indep.mgf_add h'X h'Y
#align probability_theory.indep_fun.mgf_add' ProbabilityTheory.IndepFun.mgf_add'

theorem IndepFun.cgf_add {X Y : Ω → ℝ} (h_indep : IndepFun X Y μ)
    (h_int_X : Integrable (fun ω => exp (t * X ω)) μ)
    (h_int_Y : Integrable (fun ω => exp (t * Y ω)) μ) :
    cgf (X + Y) μ t = cgf X μ t + cgf Y μ t := by
  by_cases hμ : μ = 0
  · simp [hμ]
  simp only [cgf, h_indep.mgf_add h_int_X.aestronglyMeasurable h_int_Y.aestronglyMeasurable]
  exact log_mul (mgf_pos' hμ h_int_X).ne' (mgf_pos' hμ h_int_Y).ne'
#align probability_theory.indep_fun.cgf_add ProbabilityTheory.IndepFun.cgf_add

theorem aestronglyMeasurable_exp_mul_add {X Y : Ω → ℝ}
    (h_int_X : AEStronglyMeasurable (fun ω => exp (t * X ω)) μ)
    (h_int_Y : AEStronglyMeasurable (fun ω => exp (t * Y ω)) μ) :
    AEStronglyMeasurable (fun ω => exp (t * (X + Y) ω)) μ := by
  simp_rw [Pi.add_apply, mul_add, exp_add]
  exact AEStronglyMeasurable.mul h_int_X h_int_Y
#align probability_theory.ae_strongly_measurable_exp_mul_add ProbabilityTheory.aestronglyMeasurable_exp_mul_add

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
#align probability_theory.ae_strongly_measurable_exp_mul_sum ProbabilityTheory.aestronglyMeasurable_exp_mul_sum

theorem IndepFun.integrable_exp_mul_add {X Y : Ω → ℝ} (h_indep : IndepFun X Y μ)
    (h_int_X : Integrable (fun ω => exp (t * X ω)) μ)
    (h_int_Y : Integrable (fun ω => exp (t * Y ω)) μ) :
    Integrable (fun ω => exp (t * (X + Y) ω)) μ := by
  simp_rw [Pi.add_apply, mul_add, exp_add]
  exact (h_indep.exp_mul t t).integrable_mul h_int_X h_int_Y
#align probability_theory.indep_fun.integrable_exp_mul_add ProbabilityTheory.IndepFun.integrable_exp_mul_add

theorem iIndepFun.integrable_exp_mul_sum [IsProbabilityMeasure μ] {X : ι → Ω → ℝ}
    (h_indep : iIndepFun (fun i => inferInstance) X μ) (h_meas : ∀ i, Measurable (X i))
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
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_fun.integrable_exp_mul_sum ProbabilityTheory.iIndepFun.integrable_exp_mul_sum

theorem iIndepFun.mgf_sum [IsProbabilityMeasure μ] {X : ι → Ω → ℝ}
    (h_indep : iIndepFun (fun i => inferInstance) X μ) (h_meas : ∀ i, Measurable (X i))
    (s : Finset ι) : mgf (∑ i ∈ s, X i) μ t = ∏ i ∈ s, mgf (X i) μ t := by
  classical
  induction' s using Finset.induction_on with i s hi_notin_s h_rec h_int
  · simp only [sum_empty, mgf_zero_fun, measure_univ, ENNReal.one_toReal, prod_empty]
  · have h_int' : ∀ i : ι, AEStronglyMeasurable (fun ω : Ω => exp (t * X i ω)) μ := fun i =>
      ((h_meas i).const_mul t).exp.aestronglyMeasurable
    rw [sum_insert hi_notin_s,
      IndepFun.mgf_add (h_indep.indepFun_finset_sum_of_not_mem h_meas hi_notin_s).symm (h_int' i)
        (aestronglyMeasurable_exp_mul_sum fun i _ => h_int' i),
      h_rec, prod_insert hi_notin_s]
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_fun.mgf_sum ProbabilityTheory.iIndepFun.mgf_sum

theorem iIndepFun.cgf_sum [IsProbabilityMeasure μ] {X : ι → Ω → ℝ}
    (h_indep : iIndepFun (fun i => inferInstance) X μ) (h_meas : ∀ i, Measurable (X i))
    {s : Finset ι} (h_int : ∀ i ∈ s, Integrable (fun ω => exp (t * X i ω)) μ) :
    cgf (∑ i ∈ s, X i) μ t = ∑ i ∈ s, cgf (X i) μ t := by
  simp_rw [cgf]
  rw [← log_prod _ _ fun j hj => ?_]
  · rw [h_indep.mgf_sum h_meas]
  · exact (mgf_pos (h_int j hj)).ne'
set_option linter.uppercaseLean3 false in
#align probability_theory.Indep_fun.cgf_sum ProbabilityTheory.iIndepFun.cgf_sum

/-- **Chernoff bound** on the upper tail of a real random variable. -/
theorem measure_ge_le_exp_mul_mgf [IsFiniteMeasure μ] (ε : ℝ) (ht : 0 ≤ t)
    (h_int : Integrable (fun ω => exp (t * X ω)) μ) :
    (μ {ω | ε ≤ X ω}).toReal ≤ exp (-t * ε) * mgf X μ t := by
  rcases ht.eq_or_lt with ht_zero_eq | ht_pos
  · rw [ht_zero_eq.symm]
    simp only [neg_zero, zero_mul, exp_zero, mgf_zero', one_mul]
    rw [ENNReal.toReal_le_toReal (measure_ne_top μ _) (measure_ne_top μ _)]
    exact measure_mono (Set.subset_univ _)
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
      rwa [mul_comm (exp (t * ε))⁻¹, ← div_eq_mul_inv, le_div_iff' (exp_pos _)]
    _ = exp (-t * ε) * mgf X μ t := by rw [neg_mul, exp_neg]; rfl
#align probability_theory.measure_ge_le_exp_mul_mgf ProbabilityTheory.measure_ge_le_exp_mul_mgf

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
#align probability_theory.measure_le_le_exp_mul_mgf ProbabilityTheory.measure_le_le_exp_mul_mgf

/-- **Chernoff bound** on the upper tail of a real random variable. -/
theorem measure_ge_le_exp_cgf [IsFiniteMeasure μ] (ε : ℝ) (ht : 0 ≤ t)
    (h_int : Integrable (fun ω => exp (t * X ω)) μ) :
    (μ {ω | ε ≤ X ω}).toReal ≤ exp (-t * ε + cgf X μ t) := by
  refine (measure_ge_le_exp_mul_mgf ε ht h_int).trans ?_
  rw [exp_add]
  exact mul_le_mul le_rfl (le_exp_log _) mgf_nonneg (exp_pos _).le
#align probability_theory.measure_ge_le_exp_cgf ProbabilityTheory.measure_ge_le_exp_cgf

/-- **Chernoff bound** on the lower tail of a real random variable. -/
theorem measure_le_le_exp_cgf [IsFiniteMeasure μ] (ε : ℝ) (ht : t ≤ 0)
    (h_int : Integrable (fun ω => exp (t * X ω)) μ) :
    (μ {ω | X ω ≤ ε}).toReal ≤ exp (-t * ε + cgf X μ t) := by
  refine (measure_le_le_exp_mul_mgf ε ht h_int).trans ?_
  rw [exp_add]
  exact mul_le_mul le_rfl (le_exp_log _) mgf_nonneg (exp_pos _).le
#align probability_theory.measure_le_le_exp_cgf ProbabilityTheory.measure_le_le_exp_cgf

end MomentGeneratingFunction

end ProbabilityTheory
