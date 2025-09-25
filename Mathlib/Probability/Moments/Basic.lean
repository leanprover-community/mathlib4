/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.IdentDistrib

/-!
# Moments and moment-generating function

## Main definitions

* `ProbabilityTheory.moment X p μ`: `p`th moment of a real random variable `X` with respect to
  measure `μ`, `μ[X^p]`
* `ProbabilityTheory.centralMoment X p μ`:`p`th central moment of `X` with respect to measure `μ`,
  `μ[(X - μ[X])^p]`
* `ProbabilityTheory.mgf X μ t`: moment-generating function of `X` with respect to measure `μ`,
  `μ[exp(t*X)]`
* `ProbabilityTheory.cgf X μ t`: cumulant-generating function, logarithm of the moment-generating
  function

## Main results

* `ProbabilityTheory.IndepFun.mgf_add`: if two real random variables `X` and `Y` are independent
  and their moment-generating functions are defined at `t`, then
  `mgf (X + Y) μ t = mgf X μ t * mgf Y μ t`
* `ProbabilityTheory.IndepFun.cgf_add`: if two real random variables `X` and `Y` are independent
  and their cumulant-generating functions are defined at `t`, then
  `cgf (X + Y) μ t = cgf X μ t + cgf Y μ t`
* `ProbabilityTheory.measure_ge_le_exp_cgf` and `ProbabilityTheory.measure_le_le_exp_cgf`:
  Chernoff bound on the upper (resp. lower) tail of a random variable. For `t` nonnegative such that
  the cumulant-generating function exists, `ℙ(ε ≤ X) ≤ exp(- t*ε + cgf X ℙ t)`. See also
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

lemma moment_def (X : Ω → ℝ) (p : ℕ) (μ : Measure Ω) :
    moment X p μ = μ[X ^ p] := rfl

/-- Central moment of a real random variable, `μ[(X - μ[X]) ^ p]`. -/
def centralMoment (X : Ω → ℝ) (p : ℕ) (μ : Measure Ω) : ℝ :=
  μ[(X - fun (_ : Ω) => μ[X]) ^ p]

@[simp]
theorem moment_zero (hp : p ≠ 0) : moment 0 p μ = 0 := by
  simp only [moment, hp, zero_pow, Ne, not_false_iff, Pi.zero_apply, integral_const,
    smul_eq_mul, mul_zero]

@[simp]
lemma moment_zero_measure : moment X p (0 : Measure Ω) = 0 := by simp [moment]

@[simp]
theorem centralMoment_zero (hp : p ≠ 0) : centralMoment 0 p μ = 0 := by
  simp only [centralMoment, hp, Pi.zero_apply, integral_const, smul_eq_mul,
    mul_zero, zero_sub, Pi.pow_apply, Pi.neg_apply, neg_zero, zero_pow, Ne, not_false_iff]

lemma moment_one (X : Ω → ℝ) (μ : Measure Ω) :
    moment X 1 μ = μ[X] := by simp [moment]

@[simp]
lemma centralMoment_zero_measure : centralMoment X p (0 : Measure Ω) = 0 := by
  simp [centralMoment]

theorem centralMoment_one' [IsFiniteMeasure μ] (h_int : Integrable X μ) :
    centralMoment X 1 μ = (1 - μ.real Set.univ) * μ[X] := by
  simp only [centralMoment, Pi.sub_apply, pow_one]
  rw [integral_sub h_int (integrable_const _)]
  simp only [sub_mul, integral_const, smul_eq_mul, one_mul]

@[simp]
theorem centralMoment_one [IsZeroOrProbabilityMeasure μ] : centralMoment X 1 μ = 0 := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | h
  · simp [centralMoment]
  by_cases h_int : Integrable X μ
  · rw [centralMoment_one' h_int]
    simp
  · simp only [centralMoment, Pi.sub_apply, pow_one]
    have : ¬Integrable (fun x => X x - integral μ X) μ := by
      refine fun h_sub => h_int ?_
      have h_add : X = (fun x => X x - integral μ X) + fun _ => integral μ X := by ext1 x; simp
      rw [h_add]
      fun_prop
    rw [integral_undef this]

lemma centralMoment_two_eq_variance (hX : AEMeasurable X μ) : centralMoment X 2 μ = variance X μ :=
  (variance_eq_integral hX).symm

section MomentGeneratingFunction

variable {t : ℝ}

/-- Moment-generating function of a real random variable `X`: `fun t => μ[exp(t*X)]`. -/
def mgf (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) : ℝ :=
  μ[fun ω => exp (t * X ω)]

/-- Cumulant-generating function of a real random variable `X`: `fun t => log μ[exp(t*X)]`. -/
def cgf (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) : ℝ :=
  log (mgf X μ t)

@[simp]
theorem mgf_zero_fun : mgf 0 μ t = μ.real Set.univ := by
  simp only [mgf, Pi.zero_apply, mul_zero, exp_zero, integral_const, smul_eq_mul, mul_one]

@[simp]
theorem cgf_zero_fun : cgf 0 μ t = log (μ.real Set.univ) := by simp only [cgf, mgf_zero_fun]

@[simp]
theorem mgf_zero_measure : mgf X (0 : Measure Ω) = 0 := by ext; simp [mgf]

@[simp]
theorem cgf_zero_measure : cgf X (0 : Measure Ω) = 0 := by ext; simp [cgf]

@[simp]
theorem mgf_const' (c : ℝ) : mgf (fun _ => c) μ t = μ.real Set.univ * exp (t * c) := by
  simp only [mgf, integral_const, smul_eq_mul]

theorem mgf_const (c : ℝ) [IsProbabilityMeasure μ] : mgf (fun _ => c) μ t = exp (t * c) := by
  simp

@[simp]
theorem cgf_const' [IsFiniteMeasure μ] (hμ : μ ≠ 0) (c : ℝ) :
    cgf (fun _ => c) μ t = log (μ.real Set.univ) + t * c := by
  simp only [cgf, mgf_const']
  rw [log_mul _ (exp_pos _).ne']
  · rw [log_exp _]
  · rw [Ne, measureReal_eq_zero_iff, Measure.measure_univ_eq_zero]
    simp only [hμ, not_false_iff]

@[simp]
theorem cgf_const [IsProbabilityMeasure μ] (c : ℝ) : cgf (fun _ => c) μ t = t * c := by
  simp only [cgf, mgf_const, log_exp]

@[simp]
theorem mgf_zero' : mgf X μ 0 = μ.real Set.univ := by
  simp only [mgf, zero_mul, exp_zero, integral_const, smul_eq_mul, mul_one]

theorem mgf_zero [IsProbabilityMeasure μ] : mgf X μ 0 = 1 := by
  simp [mgf_zero']

theorem cgf_zero' : cgf X μ 0 = log (μ.real Set.univ) := by simp only [cgf, mgf_zero']

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

lemma mgf_pos_iff [hμ : NeZero μ] :
    0 < mgf X μ t ↔ Integrable (fun ω ↦ exp (t * X ω)) μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ mgf_pos' hμ.out h⟩
  contrapose! h with h
  simp [mgf_undef h]

lemma exp_cgf [hμ : NeZero μ] (hX : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    exp (cgf X μ t) = mgf X μ t := by rw [cgf, exp_log (mgf_pos' hμ.out hX)]

@[deprecated (since := "2025-03-08")]
alias exp_cgf_of_neZero := exp_cgf

lemma mgf_map {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} {Y : Ω' → Ω} {X : Ω → ℝ}
    (hY : AEMeasurable Y μ) {t : ℝ} (hX : AEStronglyMeasurable (fun ω ↦ exp (t * X ω)) (μ.map Y)) :
    mgf X (μ.map Y) t = mgf (X ∘ Y) μ t := by
  simp_rw [mgf, integral_map hY hX, Function.comp_apply]

lemma mgf_id_map (hX : AEMeasurable X μ) : mgf id (μ.map X) = mgf X μ := by
  ext t
  rw [mgf_map hX, Function.id_comp]
  exact (measurable_const_mul _).exp.aestronglyMeasurable

lemma mgf_congr {Y : Ω → ℝ} (h : X =ᵐ[μ] Y) : mgf X μ t = mgf Y μ t :=
  integral_congr_ae <| by filter_upwards [h] with ω hω using by rw [hω]

lemma mgf_congr_identDistrib {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'}
    {Y : Ω' → ℝ} (h : IdentDistrib X Y μ μ') :
    mgf X μ = mgf Y μ' := by
  rw [← mgf_id_map h.aemeasurable_fst, ← mgf_id_map h.aemeasurable_snd, h.map_eq]

theorem mgf_neg : mgf (-X) μ t = mgf X μ (-t) := by simp_rw [mgf, Pi.neg_apply, mul_neg, neg_mul]

theorem cgf_neg : cgf (-X) μ t = cgf X μ (-t) := by simp_rw [cgf, mgf_neg]

theorem mgf_smul_left (α : ℝ) : mgf (α • X) μ t = mgf X μ (α * t) := by
  simp_rw [mgf, Pi.smul_apply, smul_eq_mul, mul_comm α t, mul_assoc]

theorem mgf_const_add (α : ℝ) : mgf (fun ω => α + X ω) μ t = exp (t * α) * mgf X μ t := by
  rw [mgf, mgf, ← integral_const_mul]
  congr with x
  dsimp
  rw [mul_add, exp_add]

theorem mgf_add_const (α : ℝ) : mgf (fun ω => X ω + α) μ t = mgf X μ t *  exp (t * α) := by
  simp only [add_comm, mgf_const_add, mul_comm]

lemma mgf_add_measure {ν : Measure Ω}
    (hμ : Integrable (fun ω ↦ exp (t * X ω)) μ) (hν : Integrable (fun ω ↦ exp (t * X ω)) ν) :
    mgf X (μ + ν) t = mgf X μ t + mgf X ν t := by
  rw [mgf, integral_add_measure hμ hν, mgf, mgf]

lemma mgf_sum_measure {ι : Type*} {μ : ι → Measure Ω}
    (hμ : Integrable (fun ω ↦ exp (t * X ω)) (Measure.sum μ)) :
    mgf X (Measure.sum μ) t = ∑' i, mgf X (μ i) t := by
  simp_rw [mgf, integral_sum_measure hμ]

lemma mgf_smul_measure (c : ℝ≥0∞) : mgf X (c • μ) t = c.toReal * mgf X μ t := by
  rw [mgf, integral_smul_measure, mgf, smul_eq_mul]

/-- The moment-generating function is monotone in the random variable for `t ≥ 0`. -/
lemma mgf_mono_of_nonneg {Y : Ω → ℝ} (hXY : X ≤ᵐ[μ] Y) (ht : 0 ≤ t)
    (htY : Integrable (fun ω ↦ exp (t * Y ω)) μ) :
    mgf X μ t ≤ mgf Y μ t := by
  by_cases htX : Integrable (fun ω ↦ exp (t * X ω)) μ
  · refine integral_mono_ae htX htY ?_
    filter_upwards [hXY] with ω hω using by gcongr
  · rw [mgf_undef htX]
    exact mgf_nonneg

/-- The moment-generating function is antitone in the random variable for `t ≤ 0`. -/
lemma mgf_anti_of_nonpos {Y : Ω → ℝ} (hXY : X ≤ᵐ[μ] Y) (ht : t ≤ 0)
    (htX : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    mgf Y μ t ≤ mgf X μ t := by
  by_cases htY : Integrable (fun ω ↦ exp (t * Y ω)) μ
  · refine integral_mono_ae htY htX ?_
    filter_upwards [hXY] with ω hω using exp_monotone <| mul_le_mul_of_nonpos_left hω ht
  · rw [mgf_undef htY]
    exact mgf_nonneg

section IndepFun

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
  exact (h_indep.exp_mul t t).integral_mul_eq_mul_integral hX hY

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
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_apply, sum_empty, mul_zero, exp_zero]
    exact aestronglyMeasurable_const
  | insert i s hi_notin_s h_rec =>
    have : ∀ i : ι, i ∈ s → AEStronglyMeasurable (fun ω : Ω => exp (t * X i ω)) μ := fun i hi =>
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
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
    {s : Finset ι} (h_int : ∀ i ∈ s, Integrable (fun ω => exp (t * X i ω)) μ) :
    Integrable (fun ω => exp (t * (∑ i ∈ s, X i) ω)) μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_apply, sum_empty, mul_zero, exp_zero]
    exact integrable_const _
  | insert i s hi_notin_s h_rec =>
    have : ∀ i : ι, i ∈ s → Integrable (fun ω : Ω => exp (t * X i ω)) μ := fun i hi =>
      h_int i (mem_insert_of_mem hi)
    specialize h_rec this
    rw [sum_insert hi_notin_s]
    refine IndepFun.integrable_exp_mul_add ?_ (h_int i (mem_insert_self _ _)) h_rec
    exact (h_indep.indepFun_finset_sum_of_notMem h_meas hi_notin_s).symm

-- TODO(vilin97): weaken `h_meas` to `AEMeasurable (X i)` or `AEStronglyMeasurable (X i)` throughout
-- https://github.com/leanprover-community/mathlib4/issues/20367
theorem iIndepFun.mgf_sum {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
    (s : Finset ι) : mgf (∑ i ∈ s, X i) μ t = ∏ i ∈ s, mgf (X i) μ t := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi_notin_s h_rec =>
    have h_int' : ∀ i : ι, AEStronglyMeasurable (fun ω : Ω => exp (t * X i ω)) μ := fun i =>
      ((h_meas i).const_mul t).exp.aestronglyMeasurable
    rw [sum_insert hi_notin_s,
      IndepFun.mgf_add (h_indep.indepFun_finset_sum_of_notMem h_meas hi_notin_s).symm (h_int' i)
        (aestronglyMeasurable_exp_mul_sum fun i _ => h_int' i),
      h_rec, prod_insert hi_notin_s]

theorem iIndepFun.cgf_sum {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
    {s : Finset ι} (h_int : ∀ i ∈ s, Integrable (fun ω => exp (t * X i ω)) μ) :
    cgf (∑ i ∈ s, X i) μ t = ∑ i ∈ s, cgf (X i) μ t := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  simp_rw [cgf]
  rw [← log_prod _ _ fun j hj => ?_]
  · rw [h_indep.mgf_sum h_meas]
  · exact (mgf_pos (h_int j hj)).ne'

end IndepFun

theorem mgf_congr_of_identDistrib
    (X : Ω → ℝ) {Ω' : Type*} {m' : MeasurableSpace Ω'} {μ' : Measure Ω'} (X' : Ω' → ℝ)
    (hident : IdentDistrib X X' μ μ') (t : ℝ) :
    mgf X μ t = mgf X' μ' t := hident.comp (measurable_const_mul t).exp |>.integral_eq

theorem mgf_sum_of_identDistrib
    {X : ι → Ω → ℝ}
    {s : Finset ι} {j : ι}
    (h_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X μ)
    (hident : ∀ i ∈ s, ∀ j ∈ s, IdentDistrib (X i) (X j) μ μ)
    (hj : j ∈ s) (t : ℝ) : mgf (∑ i ∈ s, X i) μ t = mgf (X j) μ t ^ #s := by
  rw [h_indep.mgf_sum h_meas]
  exact Finset.prod_eq_pow_card fun i hi =>
    mgf_congr_of_identDistrib (X i) (X j) (hident i hi j hj) t

section Chernoff

/-- **Chernoff bound** on the upper tail of a real random variable. -/
theorem measure_ge_le_exp_mul_mgf [IsFiniteMeasure μ] (ε : ℝ) (ht : 0 ≤ t)
    (h_int : Integrable (fun ω => exp (t * X ω)) μ) :
    μ.real {ω | ε ≤ X ω} ≤ exp (-t * ε) * mgf X μ t := by
  rcases ht.eq_or_lt with ht_zero_eq | ht_pos
  · rw [ht_zero_eq.symm]
    simp only [neg_zero, zero_mul, exp_zero, mgf_zero', one_mul]
    gcongr
    exacts [measure_ne_top _ _, Set.subset_univ _]
  calc
    μ.real {ω | ε ≤ X ω} = μ.real {ω | exp (t * ε) ≤ exp (t * X ω)} := by
      congr 1 with ω
      simp only [Set.mem_setOf_eq, exp_le_exp]
      exact ⟨fun h => mul_le_mul_of_nonneg_left h ht_pos.le,
        fun h => le_of_mul_le_mul_left h ht_pos⟩
    _ ≤ (exp (t * ε))⁻¹ * μ[fun ω => exp (t * X ω)] := by
      have : exp (t * ε) * μ.real {ω | exp (t * ε) ≤ exp (t * X ω)} ≤
          μ[fun ω => exp (t * X ω)] :=
        mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun x => (exp_pos _).le) h_int _
      rwa [mul_comm (exp (t * ε))⁻¹, ← div_eq_mul_inv, le_div_iff₀' (exp_pos _)]
    _ = exp (-t * ε) * mgf X μ t := by rw [neg_mul, exp_neg]; rfl

/-- **Chernoff bound** on the lower tail of a real random variable. -/
theorem measure_le_le_exp_mul_mgf [IsFiniteMeasure μ] (ε : ℝ) (ht : t ≤ 0)
    (h_int : Integrable (fun ω => exp (t * X ω)) μ) :
    μ.real {ω | X ω ≤ ε} ≤ exp (-t * ε) * mgf X μ t := by
  rw [← neg_neg t, ← mgf_neg, neg_neg, ← neg_mul_neg (-t)]
  refine Eq.trans_le ?_ (measure_ge_le_exp_mul_mgf (-ε) (neg_nonneg.mpr ht) ?_)
  · simp only [Pi.neg_apply, neg_le_neg_iff]
  · simp_rw [Pi.neg_apply, neg_mul_neg]
    exact h_int

/-- **Chernoff bound** on the upper tail of a real random variable. -/
theorem measure_ge_le_exp_cgf [IsFiniteMeasure μ] (ε : ℝ) (ht : 0 ≤ t)
    (h_int : Integrable (fun ω => exp (t * X ω)) μ) :
    μ.real {ω | ε ≤ X ω} ≤ exp (-t * ε + cgf X μ t) := by
  refine (measure_ge_le_exp_mul_mgf ε ht h_int).trans ?_
  rw [exp_add]
  exact mul_le_mul le_rfl (le_exp_log _) mgf_nonneg (exp_pos _).le

/-- **Chernoff bound** on the lower tail of a real random variable. -/
theorem measure_le_le_exp_cgf [IsFiniteMeasure μ] (ε : ℝ) (ht : t ≤ 0)
    (h_int : Integrable (fun ω => exp (t * X ω)) μ) :
    μ.real {ω | X ω ≤ ε} ≤ exp (-t * ε + cgf X μ t) := by
  refine (measure_le_le_exp_mul_mgf ε ht h_int).trans ?_
  rw [exp_add]
  exact mul_le_mul le_rfl (le_exp_log _) mgf_nonneg (exp_pos _).le

end Chernoff

lemma mgf_dirac {x : ℝ} (hX : μ.map X = .dirac x) (t : ℝ) : mgf X μ t = exp (x * t) := by
  have : IsProbabilityMeasure (μ.map X) := by rw [hX]; infer_instance
  rw [← mgf_id_map (.of_map_ne_zero <| IsProbabilityMeasure.ne_zero _), mgf, hX, integral_dirac,
    mul_comm, id_def]

lemma mgf_dirac' [MeasurableSingletonClass Ω] {ω : Ω} :
    mgf X (Measure.dirac ω) t = exp (t * X ω) := by
  rw [mgf, integral_dirac]

end MomentGeneratingFunction

lemma aemeasurable_exp_mul {X : Ω → ℝ} (t : ℝ) (hX : AEMeasurable X μ) :
    AEStronglyMeasurable (fun ω ↦ rexp (t * X ω)) μ :=
  (measurable_exp.comp_aemeasurable (hX.const_mul t)).aestronglyMeasurable

lemma integrable_exp_mul_of_le [IsFiniteMeasure μ] {X : Ω → ℝ} (t b : ℝ) (ht : 0 ≤ t)
    (hX : AEMeasurable X μ) (hb : ∀ᵐ ω ∂μ, X ω ≤ b) :
    Integrable (fun ω ↦ exp (t * X ω)) μ := by
  refine .of_mem_Icc 0 (rexp (t * b)) (measurable_exp.comp_aemeasurable (hX.const_mul t)) ?_
  filter_upwards [hb] with ω hb
  exact ⟨by positivity, by gcongr⟩

lemma integrable_exp_mul_of_mem_Icc [IsFiniteMeasure μ] {X : Ω → ℝ} {a b t : ℝ}
    (hm : AEMeasurable X μ) (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    Integrable (fun ω ↦ exp (t * X ω)) μ := by
  apply Integrable.of_mem_Icc (exp (min (a * t) (b * t))) (exp (max (a * t) (b * t)))
  · exact (measurable_exp.comp_aemeasurable (hm.const_mul t))
  filter_upwards [hb] with ω ⟨hl, hr⟩
  simp only [Set.mem_Icc, exp_le_exp, inf_le_iff, le_sup_iff]
  by_cases ht : 0 ≤ t
  · exact ⟨Or.inl (by nlinarith), Or.inr (by nlinarith)⟩
  · exact ⟨Or.inr (by nlinarith), Or.inl (by nlinarith)⟩

end ProbabilityTheory
