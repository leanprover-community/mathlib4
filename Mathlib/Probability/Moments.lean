/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Variance
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Analytic.OfScalars

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

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal Topology

-- found on zulip
theorem Real.exp_eq_tsum (x : ℝ) :
    Real.exp x = ∑' n, x^n / n.factorial := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

lemma _root_.Summable.mono {β E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f g : β → E} (hg : Summable g)
    (hfg : ∀ b, ‖f b‖ ≤ ‖g b‖) :
    Summable f := by
  rw [← summable_norm_iff] at hg ⊢
  refine summable_of_sum_le (c := ∑' x, ‖g x‖) (fun _ ↦ by positivity) (fun s ↦ ?_)
  exact (sum_le_sum fun i _ ↦ hfg i).trans (sum_le_tsum s (fun _ _ ↦ by positivity) hg)

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

variable {t u v : ℝ}

lemma _root_.AEMeasurable.abs (hX : AEMeasurable X μ) : AEMeasurable (fun ω ↦ |X ω|) μ :=
  hX.max (aemeasurable_neg_iff.mpr hX)

lemma aemeasurable_of_aemeasurable_exp_mul (ht : t ≠ 0)
    (hX : AEMeasurable (fun ω ↦ exp (t * X ω)) μ) :
    AEMeasurable X μ := by
  suffices AEMeasurable (fun ω ↦ t * X ω) μ by
    have h_eq : X = fun ω ↦ (t * X ω) / t := by ext ω; field_simp
    rw [h_eq]
    exact this.div aemeasurable_const
  exact aemeasurable_of_aemeasurable_exp hX

section Integrable

/-- Auxiliary lemma for `integrable_exp_mul_of_le`. -/
lemma integrable_exp_mul_of_le_of_measurable [IsFiniteMeasure μ] (hX : Measurable X)
    (hu : Integrable (fun ω ↦ exp (u * X ω)) μ) (h_nonneg : 0 ≤ t) (htu : t ≤ u) :
    Integrable (fun ω ↦ exp (t * X ω)) μ := by
  by_cases ht : t = 0
  · simp [ht]
  have h_pos : 0 < t := lt_of_le_of_ne' h_nonneg ht
  have hu' : Integrable (1 + {w | 0 ≤ X w}.indicator (fun ω ↦ exp (u * X ω))) μ :=
    (integrable_const _).add (hu.indicator (hX measurableSet_Ici))
  refine hu'.mono ?_ (ae_of_all _ fun ω ↦ ?_)
  · have hX : AEMeasurable X μ := aemeasurable_of_aemeasurable_exp_mul (h_pos.trans_le htu).ne'
      hu.aemeasurable
    exact (measurable_exp.comp_aemeasurable (hX.const_mul _)).aestronglyMeasurable
  · simp only [norm_eq_abs, abs_exp, Pi.add_apply, Pi.one_apply]
    rw [abs_of_nonneg]
    swap; · exact add_nonneg zero_le_one (Set.indicator_nonneg (fun ω _ ↦ by positivity) _)
    rcases le_or_lt 0 (X ω) with h_nonneg | h_neg
    · simp only [Set.mem_setOf_eq, h_nonneg, Set.indicator_of_mem]
      calc rexp (t * X ω) ≤ 1 + rexp (t * X ω) := (le_add_iff_nonneg_left _).mpr zero_le_one
      _ ≤ 1 + exp (u * X ω) := by gcongr
    · simp only [Set.mem_setOf_eq, not_le.mpr h_neg, not_false_eq_true, Set.indicator_of_not_mem,
        add_zero, exp_le_one_iff]
      exact mul_nonpos_of_nonneg_of_nonpos h_pos.le h_neg.le

/-- If `ω ↦ exp (u * X ω)` is integrable at `u ≥ 0`, then it is integrable on `[0, u]`. -/
lemma integrable_exp_mul_of_le [IsFiniteMeasure μ]
    (hu : Integrable (fun ω ↦ exp (u * X ω)) μ) (h_nonneg : 0 ≤ t) (htu : t ≤ u) :
    Integrable (fun ω ↦ exp (t * X ω)) μ := by
  by_cases ht : t = 0
  · simp [ht]
  have hX : AEMeasurable X μ := by
    refine aemeasurable_of_aemeasurable_exp_mul ?_ hu.1.aemeasurable
    exact ((lt_of_le_of_ne' h_nonneg ht).trans_le htu).ne'
  have h_eq t : (fun ω ↦ exp (t * X ω)) =ᵐ[μ] fun ω ↦ exp (t * hX.mk X ω) := by
    filter_upwards [hX.ae_eq_mk] with ω hω using by rw [hω]
  rw [integrable_congr (h_eq t)]
  rw [integrable_congr (h_eq u)] at hu
  exact integrable_exp_mul_of_le_of_measurable hX.measurable_mk hu h_nonneg htu

/-- Auxiliary lemma for `integrable_exp_mul_of_ge`. -/
lemma integrable_exp_mul_of_ge_of_measurable [IsFiniteMeasure μ] (hX : Measurable X)
    (hu : Integrable (fun ω ↦ exp (u * X ω)) μ) (h_nonpos : t ≤ 0) (htu : u ≤ t) :
    Integrable (fun ω ↦ exp (t * X ω)) μ := by
  by_cases ht : t = 0
  · simp [ht]
  have h_neg : t < 0 := lt_of_le_of_ne h_nonpos ht
  have hu' : Integrable (1 + {w | X w ≤ 0}.indicator (fun ω ↦ exp (u * X ω))) μ :=
    (integrable_const _).add (hu.indicator (hX measurableSet_Iic))
  refine hu'.mono ?_ (ae_of_all _ fun ω ↦ ?_)
  · have hX : AEMeasurable X μ := aemeasurable_of_aemeasurable_exp_mul (htu.trans_lt h_neg).ne
      hu.aemeasurable
    exact (measurable_exp.comp_aemeasurable (hX.const_mul _)).aestronglyMeasurable
  · simp only [norm_eq_abs, abs_exp, Pi.add_apply, Pi.one_apply]
    rw [abs_of_nonneg]
    swap; · exact add_nonneg zero_le_one (Set.indicator_nonneg (fun ω _ ↦ by positivity) _)
    rcases lt_or_le 0 (X ω) with h_pos | h_nonpos
    · simp only [Set.mem_setOf_eq, not_le, h_pos, Set.indicator_of_not_mem, add_zero,
        exp_le_one_iff]
      exact mul_nonpos_of_nonpos_of_nonneg h_neg.le h_pos.le
    · simp only [Set.mem_setOf_eq, h_nonpos, Set.indicator_of_mem]
      calc rexp (t * X ω) ≤ 1 + rexp (t * X ω) := (le_add_iff_nonneg_left _).mpr zero_le_one
      _ ≤ 1 + exp (u * X ω) := by
        refine add_le_add le_rfl (exp_monotone ?_)
        exact mul_le_mul_of_nonpos_of_nonpos htu le_rfl (htu.trans h_neg.le) h_nonpos

/-- If `ω ↦ exp (u * X ω)` is integrable at `u ≤ 0`, then it is integrable on `[u, 0]`. -/
lemma integrable_exp_mul_of_ge [IsFiniteMeasure μ]
    (hu : Integrable (fun ω ↦ exp (u * X ω)) μ) (h_nonpos : t ≤ 0) (htu : u ≤ t) :
    Integrable (fun ω ↦ exp (t * X ω)) μ := by
  by_cases ht : t = 0
  · simp [ht]
  have hX : AEMeasurable X μ := by
    refine aemeasurable_of_aemeasurable_exp_mul ?_ hu.1.aemeasurable
    refine (htu.trans_lt ?_).ne
    exact lt_of_le_of_ne h_nonpos ht
  have h_eq t : (fun ω ↦ exp (t * X ω)) =ᵐ[μ] fun ω ↦ exp (t * hX.mk X ω) := by
    filter_upwards [hX.ae_eq_mk] with ω hω using by rw [hω]
  rw [integrable_congr (h_eq t)]
  rw [integrable_congr (h_eq u)] at hu
  exact integrable_exp_mul_of_ge_of_measurable hX.measurable_mk hu h_nonpos htu

/-- If `ω ↦ exp (u * X ω)` is integrable at `u` and `-u`, then it is integrable on `[-u, u]`. -/
lemma integrable_exp_mul_of_abs_le [IsFiniteMeasure μ]
    (hu_int_pos : Integrable (fun ω ↦ exp (u * X ω)) μ)
    (hu_int_neg : Integrable (fun ω ↦ exp (- u * X ω)) μ)
    (htu : |t| ≤ |u|) :
    Integrable (fun ω ↦ exp (t * X ω)) μ := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht] at htu
    refine integrable_exp_mul_of_le ?_ ht htu
    rcases le_total 0 u with hu | hu
    · rwa [abs_of_nonneg hu]
    · rwa [abs_of_nonpos hu]
  · rw [abs_of_nonpos ht, neg_le] at htu
    refine integrable_exp_mul_of_ge ?_ ht htu
    rcases le_total 0 u with hu | hu
    · rwa [abs_of_nonneg hu]
    · rwa [abs_of_nonpos hu, neg_neg]

lemma integrable_exp_mul_of_le_of_le [IsFiniteMeasure μ] {a b : ℝ}
    (ha : Integrable (fun ω ↦ exp (a * X ω)) μ)
    (hb : Integrable (fun ω ↦ exp (b * X ω)) μ)
    (hat : a ≤ t) (htb : t ≤ b) :
    Integrable (fun ω ↦ exp (t * X ω)) μ := by
  rcases le_total 0 t with ht | ht
  · exact integrable_exp_mul_of_le hb ht htb
  · exact integrable_exp_mul_of_ge ha ht hat

lemma exp_mul_abs_add_le_add : exp (t * |u| + v * u) ≤ rexp ((v + t) * u) + rexp ((v - t) * u) := by
  rcases le_total 0 u with h_nonneg | h_nonpos
  · rw [abs_of_nonneg h_nonneg, ← add_mul, add_comm, le_add_iff_nonneg_right]
    positivity
  · rw [abs_of_nonpos h_nonpos, mul_neg, mul_comm, ← mul_neg, mul_comm, ← add_mul, add_comm,
      ← sub_eq_add_neg, le_add_iff_nonneg_left]
    positivity

lemma exp_mul_abs_le_add : exp (t * |u|) ≤ rexp (t * u) + rexp (-(t * u)) := by
  have h := exp_mul_abs_add_le_add (t := t) (u := u) (v := 0)
  simpa using h

lemma integrable_exp_mul_abs_add (ht_int_pos : Integrable (fun ω ↦ rexp ((v + t) * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ rexp ((v - t) * X ω)) μ) :
    Integrable (fun ω ↦ rexp (t * |X ω| + v * X ω)) μ := by
  have h_int_add : Integrable (fun a ↦ rexp ((v + t) * X a) + rexp ((v - t) * X a)) μ :=
    ht_int_pos.add <| by simpa using ht_int_neg
  refine Integrable.mono h_int_add ?_ (ae_of_all _ fun ω ↦ ?_)
  · by_cases ht : t = 0
    · simp only [ht, zero_mul, zero_add]
      simp only [ht, add_zero] at ht_int_pos
      exact ht_int_pos.1
    have hX : AEMeasurable X μ := by
      by_cases hvt : v + t = 0
      · have hvt' : v - t ≠ 0 := by
          rw [sub_ne_zero]
          refine fun h_eq ↦ ht ?_
          simpa [h_eq] using hvt
        exact aemeasurable_of_aemeasurable_exp_mul hvt' ht_int_neg.1.aemeasurable
      · exact aemeasurable_of_aemeasurable_exp_mul hvt ht_int_pos.1.aemeasurable
    refine AEMeasurable.aestronglyMeasurable ?_
    exact measurable_exp.comp_aemeasurable ((hX.abs.const_mul _).add (hX.const_mul _))
  · simp only [norm_eq_abs, abs_exp]
    conv_rhs => rw [abs_of_nonneg (by positivity)]
    exact exp_mul_abs_add_le_add

/-- If `ω ↦ rexp (t * X ω)` is integrable at `t` and `-t`, then `ω ↦ rexp (t * |X ω|)` is
integrable. -/
lemma integrable_exp_mul_abs (ht_int_pos : Integrable (fun ω ↦ rexp (t * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ rexp (- t * X ω)) μ) :
    Integrable (fun ω ↦ rexp (t * |X ω|)) μ := by
  have h := integrable_exp_mul_abs_add (t := t) (μ := μ) (X := X) (v := 0) ?_ ?_
  · simpa using h
  · simpa using ht_int_pos
  · simpa using ht_int_neg

lemma integrable_exp_abs_mul_abs_add (ht_int_pos : Integrable (fun ω ↦ rexp ((v + t) * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ rexp ((v - t) * X ω)) μ) :
    Integrable (fun ω ↦ rexp (|t| * |X ω| + v * X ω)) μ := by
  rcases le_total 0 t with ht_nonneg | ht_nonpos
  · simp_rw [abs_of_nonneg ht_nonneg]
    exact integrable_exp_mul_abs_add ht_int_pos ht_int_neg
  · simp_rw [abs_of_nonpos ht_nonpos]
    exact integrable_exp_mul_abs_add ht_int_neg (by simpa using ht_int_pos)

/-- If `ω ↦ rexp (t * X ω)` is integrable at `t` and `-t`, then `ω ↦ rexp (|t| * |X ω|)` is
integrable. -/
lemma integrable_exp_abs_mul_abs (ht_int_pos : Integrable (fun ω ↦ rexp (t * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ rexp (- t * X ω)) μ) :
    Integrable (fun ω ↦ rexp (|t| * |X ω|)) μ := by
  rcases le_total 0 t with ht_nonneg | ht_nonpos
  · simp_rw [abs_of_nonneg ht_nonneg]
    exact integrable_exp_mul_abs ht_int_pos ht_int_neg
  · simp_rw [abs_of_nonpos ht_nonpos]
    exact integrable_exp_mul_abs ht_int_neg (by simpa using ht_int_pos)

lemma integrable_pow_abs_mul_exp_of_integrable_exp_mul (ht : t ≠ 0)
    (ht_int_pos : Integrable (fun x ↦ rexp ((v + t) * X x)) μ)
    (ht_int_neg : Integrable (fun x ↦ rexp ((v - t) * X x)) μ) (n : ℕ) :
    Integrable (fun ω ↦ |X ω| ^ n * exp (v * X ω)) μ := by
  suffices Integrable (fun ω ↦ (t * |X ω|) ^ n / n.factorial * exp (v * X ω)) μ by
    have h_eq ω : |X ω| ^ n * exp (v * X ω)
        = ((t * |X ω|) ^ n / n.factorial * exp (v * X ω)) * n.factorial / t ^ n := by
      rw [mul_pow]
      field_simp
      ring
    simp_rw [h_eq]
    exact (this.mul_const _).div_const _
  have h_le ω : (|t| * |X ω|) ^ n / n.factorial ≤ exp (|t| * |X ω|) :=
    pow_div_factorial_le_exp _ (by positivity) _
  have h_int := integrable_exp_abs_mul_abs_add ht_int_pos ht_int_neg
  refine Integrable.mono h_int ?_ (ae_of_all _ fun ω ↦ ?_)
  · have hX : AEMeasurable X μ := by
      by_cases hvt : v + t = 0
      · have hvt' : v - t ≠ 0 := by
          rw [sub_ne_zero]
          refine fun h_eq ↦ ht ?_
          simpa [h_eq] using hvt
        exact aemeasurable_of_aemeasurable_exp_mul hvt' ht_int_neg.1.aemeasurable
      · exact aemeasurable_of_aemeasurable_exp_mul hvt ht_int_pos.1.aemeasurable
    simp_rw [mul_pow]
    refine AEMeasurable.aestronglyMeasurable ?_
    exact (((hX.abs.pow_const _).const_mul _).div_const _).mul
      (measurable_exp.comp_aemeasurable (hX.const_mul _))
  · simp only [norm_div, norm_pow, norm_mul, norm_eq_abs, abs_abs, norm_natCast, abs_exp,
      Nat.abs_cast]
    rw [exp_add]
    gcongr
    exact h_le _

/-- If `ω ↦ rexp (t * X ω)` is integrable at `t` and `-t` for `t ≠ 0`, then `ω ↦ |X ω| ^ n` is
integrable for all `n : ℕ`. That is, all moments of `X` are finite. -/
lemma integrable_pow_abs_of_integrable_exp_mul (ht : t ≠ 0)
    (ht_int_pos : Integrable (fun x ↦ rexp (t * X x)) μ)
    (ht_int_neg : Integrable (fun x ↦ rexp (- t * X x)) μ) (n : ℕ) :
    Integrable (fun ω ↦ |X ω| ^ n) μ := by
  have h := integrable_pow_abs_mul_exp_of_integrable_exp_mul (μ := μ) (X := X) ht (v := 0) ?_ ?_ n
  · simpa using h
  · simpa using ht_int_pos
  · simpa using ht_int_neg

lemma integrable_pow_mul_exp_of_integrable_exp_mul (ht : t ≠ 0)
    (ht_int_pos : Integrable (fun x ↦ rexp ((v + t) * X x)) μ)
    (ht_int_neg : Integrable (fun x ↦ rexp ((v - t) * X x)) μ) (n : ℕ) :
    Integrable (fun ω ↦ X ω ^ n * exp (v * X ω)) μ := by
  rw [← integrable_norm_iff]
  · simp_rw [norm_eq_abs, abs_mul, abs_pow, abs_exp]
    exact integrable_pow_abs_mul_exp_of_integrable_exp_mul ht ht_int_pos ht_int_neg n
  · have hX : AEMeasurable X μ := by
      by_cases hvt : v + t = 0
      · have hvt' : v - t ≠ 0 := by
          rw [sub_ne_zero]
          refine fun h_eq ↦ ht ?_
          simpa [h_eq] using hvt
        exact aemeasurable_of_aemeasurable_exp_mul hvt' ht_int_neg.1.aemeasurable
      · exact aemeasurable_of_aemeasurable_exp_mul hvt ht_int_pos.1.aemeasurable
    exact ((hX.pow_const _).mul
      (measurable_exp.comp_aemeasurable (hX.const_mul _))).aestronglyMeasurable

/-- If `ω ↦ rexp (t * X ω)` is integrable at `t` and `-t` for `t ≠ 0`, then `ω ↦ X ω ^ n` is
integrable for all `n : ℕ`. -/
lemma integrable_pow_of_integrable_exp_mul (ht : t ≠ 0)
    (ht_int_pos : Integrable (fun x ↦ rexp (t * X x)) μ)
    (ht_int_neg : Integrable (fun x ↦ rexp (- t * X x)) μ) (n : ℕ) :
    Integrable (fun ω ↦ X ω ^ n) μ := by
  have h := integrable_pow_mul_exp_of_integrable_exp_mul (μ := μ) (X := X) ht (v := 0) ?_ ?_ n
  · simpa using h
  · simpa using ht_int_pos
  · simpa using ht_int_neg

end Integrable

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

/-- `exp cgf = mgf`.
For a version for probability measures, without the hypothesis `hμ : μ ≠ 0`, see `exp_cgf`. -/
lemma exp_cgf' (hμ : μ ≠ 0) (h_int_X : Integrable (fun ω => exp (t * X ω)) μ) :
    exp (cgf X μ t) = mgf X μ t := by rw [cgf, exp_log (mgf_pos' hμ h_int_X)]

/-- `exp cgf = mgf`.
For a version that works more generally than probability measures, with a hypothesis `hμ : μ ≠ 0`,
see `exp_cgf'`. -/
lemma exp_cgf [IsProbabilityMeasure μ] (h_int_X : Integrable (fun ω => exp (t * X ω)) μ) :
    exp (cgf X μ t) = mgf X μ t := by rw [cgf, exp_log (mgf_pos h_int_X)]

theorem mgf_neg : mgf (-X) μ t = mgf X μ (-t) := by simp_rw [mgf, Pi.neg_apply, mul_neg, neg_mul]

theorem cgf_neg : cgf (-X) μ t = cgf X μ (-t) := by simp_rw [cgf, mgf_neg]

theorem mgf_smul_left (α : ℝ) : mgf (α • X) μ t = mgf X μ (α * t) := by
  simp_rw [mgf, Pi.smul_apply, smul_eq_mul, mul_comm α t, mul_assoc]

/-- The moment generating function is monotone in the random variable for `t ≥ 0`. -/
lemma mgf_mono_of_nonneg {Y : Ω → ℝ} (hXY : X ≤ᵐ[μ] Y) (ht : 0 ≤ t)
    (htY : Integrable (fun ω ↦ exp (t * Y ω)) μ) :
    mgf X μ t ≤ mgf Y μ t := by
  by_cases htX : Integrable (fun ω ↦ exp (t * X ω)) μ
  · refine integral_mono_ae htX htY ?_
    filter_upwards [hXY] with ω hω using by gcongr
  · rw [mgf_undef htX]
    exact mgf_nonneg

/-- The moment generating function is antitone in the random variable for `t ≤ 0`. -/
lemma mgf_anti_of_nonpos {Y : Ω → ℝ} (hXY : X ≤ᵐ[μ] Y) (ht : t ≤ 0)
    (htX : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    mgf Y μ t ≤ mgf X μ t := by
  by_cases htY : Integrable (fun ω ↦ exp (t * Y ω)) μ
  · refine integral_mono_ae htY htX ?_
    filter_upwards [hXY] with ω hω using exp_monotone <| mul_le_mul_of_nonpos_left hω ht
  · rw [mgf_undef htY]
    exact mgf_nonneg

lemma mgf_abs_le_add (ht_int_pos : Integrable (fun ω ↦ rexp (t * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ rexp (- t * X ω)) μ) :
    mgf (fun ω ↦ |X ω|) μ t ≤ mgf X μ t + mgf (-X) μ t := by
  simp_rw [mgf]
  rw [← integral_add ht_int_pos (by simpa using ht_int_neg)]
  have h_int_add : Integrable (fun a ↦ rexp (t * X a) + rexp (-(t * X a))) μ :=
    ht_int_pos.add <| by simpa using ht_int_neg
  simp only [Pi.neg_apply, mul_neg, ge_iff_le]
  refine integral_mono_ae ?_ h_int_add
    (ae_of_all _ (fun ω ↦ exp_mul_abs_le_add (t := t) (u := X ω)))
  exact integrable_exp_mul_abs ht_int_pos ht_int_neg

lemma summable_integral_abs_mul_exp_of_todo
    (ht_int_pos : Integrable (fun ω ↦ rexp ((v + t) * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ rexp ((v - t) * X ω)) μ) :
    Summable fun (i : ℕ) ↦ μ[fun ω ↦ |X ω| ^ i / i.factorial * |t| ^ i * exp (v * X ω)] := by
  by_cases ht : t = 0
  · simp only [ht, abs_zero]
    refine summable_of_ne_finset_zero (s := {0}) (fun n hn ↦ ?_)
    rw [zero_pow]
    · simp
    · simpa using hn
  suffices Summable fun i ↦ ∫ ω, (|t| * |X ω|) ^ i / i.factorial * exp (v * X ω) ∂μ by
    simp_rw [mul_pow] at this
    convert this using 4 with i ω
    ring
  have h_int (u : ℝ) (i : ℕ) :
      Integrable (fun ω ↦ (u * |X ω|) ^ i / i.factorial * exp (v * X ω)) μ := by
    simp_rw [mul_pow]
    simp_rw [mul_comm _ (exp (v * _)), mul_div]
    refine Integrable.div_const ?_ _
    simp_rw [mul_comm (exp _), mul_assoc]
    refine Integrable.const_mul ?_ _
    exact integrable_pow_abs_mul_exp_of_integrable_exp_mul ht ht_int_pos ht_int_neg i
  refine summable_of_sum_range_le (c := μ[fun ω ↦ exp (|t| * |X ω| + v * X ω)])
    (fun _ ↦ integral_nonneg fun ω ↦ by positivity) fun n ↦ ?_
  rw [← integral_finset_sum]
  · refine integral_mono ?_ ?_ ?_
    · exact integrable_finset_sum (range n) fun i a ↦ h_int |t| i
    · exact integrable_exp_abs_mul_abs_add ht_int_pos ht_int_neg
    · intro ω
      simp only
      rw [← sum_mul, exp_add]
      gcongr
      exact sum_le_exp_of_nonneg (by positivity) _
  · exact fun i _ ↦ h_int _ i

lemma summable_integral_abs_of_todo (ht_int_pos : Integrable (fun ω ↦ rexp (t * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ rexp (- t * X ω)) μ) :
    Summable fun (i : ℕ) ↦ μ[fun ω ↦ |X ω| ^ i / i.factorial * |t| ^ i] := by
  have h := summable_integral_abs_mul_exp_of_todo (μ := μ) (X := X) (v := 0) (t := t) ?_ ?_
  · simpa using h
  · simpa using ht_int_pos
  · simpa using ht_int_neg

lemma summable_integral_pow_abs_mul_exp_mul_abs
    (ht_int_pos : Integrable (fun ω ↦ rexp ((v + t) * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ rexp ((v - t) * X ω)) μ) :
    Summable fun (i : ℕ) ↦ μ[fun ω ↦ |X ω| ^ i * exp (v * X ω)] / i.factorial * |t| ^ i := by
  simp_rw [← integral_div, ← integral_mul_right]
  have h_eq i ω : |X ω| ^ i * rexp (v * X ω) / i.factorial * |t| ^ i
      = |X ω| ^ i / i.factorial * |t| ^ i * rexp (v * X ω) := by ring
  simp_rw [h_eq]
  exact summable_integral_abs_mul_exp_of_todo ht_int_pos ht_int_neg

lemma summable_integral_pow_abs_mul_abs (ht_int_pos : Integrable (fun ω ↦ rexp (t * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ rexp (- t * X ω)) μ) :
    Summable fun (i : ℕ) ↦ μ[fun ω ↦ |X ω| ^ i] / i.factorial * |t| ^ i := by
  simp_rw [← integral_div, ← integral_mul_right]
  exact summable_integral_abs_of_todo ht_int_pos ht_int_neg

lemma summable_integral_pow_mul_exp_mul
    (ht_int_pos : Integrable (fun ω ↦ rexp ((v + t) * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ rexp ((v - t) * X ω)) μ) :
    Summable fun (i : ℕ) ↦ μ[fun ω ↦ X ω ^ i * rexp (v * X ω)] / i.factorial * t ^ i := by
  refine (summable_integral_pow_abs_mul_exp_mul_abs ht_int_pos ht_int_neg).mono fun i ↦ ?_
  simp only [Pi.pow_apply, norm_mul, norm_div, norm_eq_abs, norm_natCast, norm_pow, abs_abs,
    Nat.abs_cast]
  refine mul_le_mul ?_ le_rfl (by positivity) (by positivity)
  rw [div_le_div_iff_of_pos_right (by positivity)]
  conv_rhs => rw [abs_of_nonneg (integral_nonneg (fun _ ↦ by positivity))]
  simp_rw [← norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  simp

lemma summable_integral_pow_mul (ht_int_pos : Integrable (fun ω ↦ rexp (t * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ rexp (- t * X ω)) μ) :
    Summable fun (i : ℕ) ↦ μ[X ^ i] / i.factorial * t ^ i := by
  have h := summable_integral_pow_mul_exp_mul (μ := μ) (X := X) (v := 0) (t := t) ?_ ?_
  · simpa using h
  · simpa using ht_int_pos
  · simpa using ht_int_neg

lemma mgf_abs_eq_tsum (ht_int_pos : Integrable (fun ω ↦ rexp (t * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ rexp (- t * X ω)) μ) :
    mgf (fun ω ↦ |X ω|) μ t = ∑' n, (μ[fun ω ↦ |X ω| ^ n]) / n.factorial * t ^ n := by
  by_cases ht : t = 0
  · rw [tsum_eq_single 0]
    · simp [ht]
    · intro n hn
      simp [zero_pow hn, ht]
  simp_rw [mgf, exp_eq_tsum]
  have h_int (u : ℝ) (i : ℕ) : Integrable (fun ω ↦ (u * |X ω|) ^ i / i.factorial) μ := by
    refine Integrable.div_const ?_ _
    simp_rw [mul_pow]
    refine Integrable.const_mul ?_ _
    exact integrable_pow_abs_of_integrable_exp_mul ht ht_int_pos ht_int_neg i
  rw [← integral_tsum_of_summable_integral_norm (h_int _)]
  · congr with n
    simp_rw [integral_div, mul_pow, integral_mul_left]
    ring
  · simp only [norm_div, norm_pow, norm_mul, norm_eq_abs, abs_abs, norm_natCast, Nat.abs_cast]
    convert summable_integral_abs_of_todo ht_int_pos ht_int_neg with i ω
    ring

lemma mgf_add_eq_tsum (ht_int_pos : Integrable (fun ω ↦ rexp ((v + t) * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ rexp ((v - t) * X ω)) μ) :
    mgf X μ (v + t) = ∑' n, μ[fun ω ↦ X ω ^ n * exp (v * X ω)] / n.factorial * t ^ n := by
  by_cases ht : t = 0
  · rw [tsum_eq_single 0]
    · simp [ht, mgf]
    · intro n hn
      simp [zero_pow hn, ht]
  have h_int_pow i : Integrable (fun ω ↦ X ω ^ i / i.factorial * t ^ i * exp (v * X ω)) μ := by
    simp_rw [mul_comm _ (exp _), ← mul_assoc, ← mul_div_assoc, mul_comm (exp _)]
    refine (Integrable.div_const ?_ _).mul_const _
    exact integrable_pow_mul_exp_of_integrable_exp_mul ht ht_int_pos ht_int_neg i
  suffices Tendsto (fun n ↦ |mgf X μ (v + t)
        - μ[fun ω ↦ ∑ i in range n, X ω ^ i / i.factorial * t ^ i * exp (v * X ω)]|)
      atTop (𝓝 0) by
    change Tendsto (abs ∘ _) _ _ at this
    rw [← tendsto_zero_iff_abs_tendsto_zero] at this
    have h_eq n : μ[fun ω ↦ ∑ i ∈ range n, X ω ^ i / i.factorial * t ^ i * exp (v * X ω)]
        = ∑ i ∈ range n, μ[fun ω ↦ X ω ^ i * exp (v * X ω)] / i.factorial * t ^ i := by
      rw [integral_finset_sum]
      · congr with n
        rw [← integral_div, ← integral_mul_right]
        congr with ω
        ring
      · exact fun i _ ↦ h_int_pow i
    simp_rw [h_eq] at this
    suffices Tendsto (fun n ↦
          ∑ i ∈ range n, μ[fun ω ↦ X ω ^ i * exp (v * X ω)] / i.factorial * t ^ i)
        atTop (𝓝 (mgf X μ (v + t))) by
      refine tendsto_nhds_unique this ?_
      refine HasSum.Multipliable.tendsto_sum_tsum_nat ?_
      exact summable_integral_pow_mul_exp_mul ht_int_pos ht_int_neg
    rwa [← tendsto_const_sub_iff (b := mgf X μ (v + t)), sub_self]
  have h_le n : |mgf X μ (v + t)
        - μ[fun ω ↦ ∑ i ∈ range n, X ω ^ i / ↑i.factorial * t ^ i * exp (v * X ω)]|
      ≤ ∑' i : {j // j ∉ range n},
        μ[fun ω ↦ |X ω| ^ (i : ℕ) * exp (v * X ω)] / (i : ℕ).factorial * |t| ^ (i : ℕ) := by
    calc |mgf X μ (v + t)
        - μ[fun ω ↦ ∑ i ∈ range n, X ω ^ i / ↑i.factorial * t ^ i * exp (v * X ω)]|
    _ = |μ[fun ω ↦ ∑' i : {j // j ∉ range n},
        X ω ^ (i : ℕ) / (i : ℕ).factorial * t ^ (i : ℕ) * exp (v * X ω)]| := by
      simp_rw [mgf]
      rw [← integral_sub ht_int_pos (integrable_finset_sum _ (fun i _ ↦ h_int_pow i))]
      congr with ω
      rw [add_mul, add_comm, exp_add]
      rw [exp_eq_tsum, sub_eq_iff_eq_add']
      have : ∑' n, (t * X ω) ^ n / n.factorial
          = ∑' n, X ω ^ n / n.factorial * t ^ n := by
        simp_rw [mul_pow]
        congr with n
        ring
      rw [this, ← tsum_mul_right]
      symm
      refine sum_add_tsum_compl ?_
      suffices Summable fun i ↦ (t * X ω) ^ i / i.factorial * exp (v * X ω) by
        convert this using 2 with i
        ring
      refine Summable.mul_right _ ?_
      exact summable_pow_div_factorial _
    _ = |∑' i : {j // j ∉ range n},
        μ[fun ω ↦ X ω ^ (i : ℕ) * exp (v * X ω)] / (i : ℕ).factorial * t ^ (i : ℕ)| := by
      have h_eq i ω : X ω ^ i / ↑i.factorial * t ^ i * exp (v * X ω)
          = X ω ^ i * exp (v * X ω) / ↑i.factorial * t ^ i := by ring
      simp_rw [h_eq]
      rw [← integral_tsum_of_summable_integral_norm]
      · congr with i
        rw [← integral_div, ← integral_mul_right]
      · refine fun i ↦ (Integrable.div_const ?_ _).mul_const _
        exact integrable_pow_mul_exp_of_integrable_exp_mul ht ht_int_pos ht_int_neg _
      · simp only [norm_mul, norm_div, norm_pow, norm_eq_abs, norm_natCast, Nat.abs_cast]
        simp_rw [integral_mul_right, integral_div, abs_exp]
        exact (summable_integral_pow_abs_mul_exp_mul_abs ht_int_pos ht_int_neg).subtype (range n)ᶜ
    _ ≤ ∑' i : {j // j ∉ range n},
        |μ[fun ω ↦ X ω ^ (i : ℕ) * exp (v * X ω)] / (i : ℕ).factorial * t ^ (i : ℕ)| := by
      simp_rw [← norm_eq_abs]
      refine norm_tsum_le_tsum_norm ?_
      rw [summable_norm_iff]
      exact (summable_integral_pow_mul_exp_mul ht_int_pos ht_int_neg).subtype (range n)ᶜ
    _ ≤ ∑' i : {j // j ∉ range n},
          μ[fun ω ↦ |X ω| ^ (i : ℕ) * exp (v * X ω)] / (i : ℕ).factorial * |t| ^ (i : ℕ) := by
      simp only [Pi.pow_apply]
      refine tsum_mono ?_ ?_ fun n ↦ ?_
      · rw [summable_abs_iff]
        exact (summable_integral_pow_mul_exp_mul ht_int_pos ht_int_neg).subtype (range n)ᶜ
      · exact (summable_integral_pow_abs_mul_exp_mul_abs ht_int_pos ht_int_neg).subtype (range n)ᶜ
      · simp only
        rw [abs_mul, abs_div, Nat.abs_cast, abs_pow]
        gcongr
        simp_rw [← norm_eq_abs]
        refine (norm_integral_le_integral_norm _).trans ?_
        simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds) ?_ ?_ h_le
  · refine (tendsto_tsum_compl_atTop_zero
      (fun i ↦ μ[fun ω ↦ |X ω| ^ (i : ℕ) * exp (v * X ω)]
        / (i : ℕ).factorial * |t| ^ (i : ℕ))).comp ?_
    exact tendsto_finset_range
  · intro n
    positivity

lemma mgf_eq_tsum (ht_int_pos : Integrable (fun ω ↦ rexp (t * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ rexp (- t * X ω)) μ) :
    mgf X μ t = ∑' n, μ[X ^ n] / n.factorial * t ^ n := by
  have h := mgf_add_eq_tsum (μ := μ) (X := X) (v := 0) (t := t) ?_ ?_
  · simpa using h
  · simpa using ht_int_pos
  · simpa using ht_int_neg

lemma hasFPowerSeriesOnBall_mgf' [IsFiniteMeasure μ] (ht : t ≠ 0)
    (ht_int_pos : Integrable (fun ω ↦ rexp ((v + t) * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ rexp ((v - t) * X ω)) μ) :
    HasFPowerSeriesOnBall (mgf X μ)
      (FormalMultilinearSeries.ofScalars ℝ
        (fun n ↦ (μ[fun ω ↦ X ω ^ n * exp (v * X ω)] : ℝ) / n.factorial)) v ‖t‖₊ := by
  constructor
  · refine FormalMultilinearSeries.le_radius_of_summable _ ?_
    simp only [Pi.pow_apply, FormalMultilinearSeries.ofScalars_norm, norm_eq_abs,
      coe_nnnorm, abs_div, Nat.abs_cast]
    have h := summable_integral_pow_mul_exp_mul ht_int_pos ht_int_neg
    rw [← summable_abs_iff] at h
    simp_rw [abs_mul, abs_div, abs_pow, Nat.abs_cast] at h
    exact h
  · simp [ht]
  · intro y hy
    simp_rw [FormalMultilinearSeries.ofScalars_apply_eq]
    simp only [Pi.pow_apply, smul_eq_mul, zero_add]
    simp only [Metric.emetric_ball_nnreal, coe_nnnorm, norm_eq_abs, Metric.mem_ball,
      dist_zero_right] at hy
    have hy_int_pos : Integrable (fun ω ↦ rexp ((v + y) * X ω)) μ := by
      rcases le_total 0 t with ht | ht
      · refine integrable_exp_mul_of_le_of_le ht_int_neg ht_int_pos ?_ ?_
        · rw [sub_eq_add_neg]
          gcongr
          sorry
        · gcongr
          sorry
      · refine integrable_exp_mul_of_le_of_le ht_int_pos ht_int_neg ?_ ?_
        · gcongr
          sorry
        · rw [sub_eq_add_neg]
          gcongr
          sorry
    have hy_int_neg : Integrable (fun ω ↦ rexp ((v - y) * X ω)) μ := by
      sorry
    rw [Summable.hasSum_iff]
    · exact (mgf_add_eq_tsum hy_int_pos hy_int_neg).symm
    · exact summable_integral_pow_mul_exp_mul hy_int_pos hy_int_neg

lemma hasFPowerSeriesOnBall_mgf [IsFiniteMeasure μ] (ht : t ≠ 0)
    (ht_int_pos : Integrable (fun ω ↦ rexp (t * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ rexp (-t * X ω)) μ) :
    HasFPowerSeriesOnBall (mgf X μ)
      (FormalMultilinearSeries.ofScalars ℝ (fun n ↦ (μ[X ^ n] : ℝ) / n.factorial)) 0 ‖t‖₊ := by
  constructor
  · refine FormalMultilinearSeries.le_radius_of_summable _ ?_
    simp only [Pi.pow_apply, FormalMultilinearSeries.ofScalars_norm, norm_eq_abs,
      coe_nnnorm, abs_div, Nat.abs_cast]
    have h := summable_integral_pow_mul ht_int_pos ht_int_neg
    rw [← summable_abs_iff] at h
    simp_rw [abs_mul, abs_div, abs_pow, Nat.abs_cast, Pi.pow_apply] at h
    exact h
  · simp [ht]
  · intro y hy
    simp_rw [FormalMultilinearSeries.ofScalars_apply_eq]
    simp only [Pi.pow_apply, smul_eq_mul, zero_add]
    simp only [Metric.emetric_ball_nnreal, coe_nnnorm, norm_eq_abs, Metric.mem_ball,
      dist_zero_right] at hy
    have hy_int_pos : Integrable (fun ω ↦ rexp (y * X ω)) μ :=
      integrable_exp_mul_of_abs_le ht_int_pos ht_int_neg hy.le
    have hy_int_neg : Integrable (fun ω ↦ rexp (- y * X ω)) μ := by
      refine integrable_exp_mul_of_abs_le ht_int_pos ht_int_neg ?_
      simp only [abs_neg]
      exact hy.le
    rw [Summable.hasSum_iff]
    · exact (mgf_eq_tsum hy_int_pos hy_int_neg).symm
    · exact summable_integral_pow_mul hy_int_pos hy_int_neg

lemma hasFPowerSeriesAt_mgf' [IsFiniteMeasure μ] (ht : t ≠ 0)
    (ht_int_pos : Integrable (fun ω ↦ rexp ((v + t) * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ rexp ((v - t) * X ω)) μ) :
    HasFPowerSeriesAt (mgf X μ)
      (FormalMultilinearSeries.ofScalars ℝ
        (fun n ↦ (μ[fun ω ↦ X ω ^ n * exp (v * X ω)] : ℝ) / n.factorial)) v :=
  ⟨‖t‖₊, hasFPowerSeriesOnBall_mgf' ht ht_int_pos ht_int_neg⟩

lemma hasFPowerSeriesAt_mgf [IsFiniteMeasure μ] (ht : t ≠ 0)
    (ht_int_pos : Integrable (fun ω ↦ rexp (t * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ rexp (-t * X ω)) μ) :
    HasFPowerSeriesAt (mgf X μ)
      (FormalMultilinearSeries.ofScalars ℝ (fun n ↦ (μ[X ^ n] : ℝ) / n.factorial)) 0 :=
  ⟨‖t‖₊, hasFPowerSeriesOnBall_mgf ht ht_int_pos ht_int_neg⟩

lemma analyticAt_mgf' [IsFiniteMeasure μ] (ht : t ≠ 0)
    (ht_int_pos : Integrable (fun ω ↦ rexp ((v + t) * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ rexp ((v - t) * X ω)) μ) :
    AnalyticAt ℝ (mgf X μ) v :=
  ⟨_, hasFPowerSeriesAt_mgf' ht ht_int_pos ht_int_neg⟩

lemma analyticAt_mgf [IsFiniteMeasure μ] (ht : t ≠ 0)
    (ht_int_pos : Integrable (fun ω ↦ rexp (t * X ω)) μ)
    (ht_int_neg : Integrable (fun ω ↦ rexp (-t * X ω)) μ) :
    AnalyticAt ℝ (mgf X μ) 0 :=
  ⟨_, hasFPowerSeriesAt_mgf ht ht_int_pos ht_int_neg⟩

lemma analyticOnNhd_mgf [IsFiniteMeasure μ] :
    AnalyticOnNhd ℝ (mgf X μ) (interior {x | Integrable (fun ω ↦ exp (x * X ω)) μ}) := by
  intro x hx
  rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hx
  obtain ⟨l, u, hxlu, h_subset⟩ := hx
  sorry

lemma iteratedDeriv_mgf_zero [IsFiniteMeasure μ]
    (hu_int_pos : Integrable (fun ω ↦ rexp (u * X ω)) μ)
    (hu_int_neg : Integrable (fun ω ↦ rexp (- u * X ω)) μ) (n : ℕ) :
    iteratedDeriv n (mgf X μ) 0 = μ[X ^ n] := by
  sorry

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

end IndepFun

section Chernoff

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

end Chernoff

end MomentGeneratingFunction

end ProbabilityTheory
