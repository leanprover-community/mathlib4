/-
Copyright (c) 2022 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals

#align_import measure_theory.integral.layercake from "leanprover-community/mathlib"@"08a4542bec7242a5c60f179e4e49de8c0d677b1b"

/-!
# The layer cake formula / Cavalieri's principle / tail probability formula

In this file we prove the following layer cake formula.

Consider a non-negative measurable function `f` on a sigma-finite measure space. Apply pointwise
to it an increasing absolutely continuous function `G : ℝ≥0 → ℝ≥0` vanishing at the origin, with
derivative `G' = g` on the positive real line (in other words, `G` a primitive of a non-negative
locally integrable function `g` on the positive real line). Then the integral of the result,
`∫ G ∘ f`, can be written as the integral over the positive real line of the "tail measures" of `f`
(i.e., a function giving the measures of the sets on which `f` exceeds different positive real
values) weighted by `g`. In probability theory contexts, the "tail measures" could be referred to
as "tail probabilities" of the random variable `f`, or as values of the "complementary cumulative
distribution function" of the random variable `f`. The terminology "tail probability formula" is
therefore occasionally used for the layer cake formula (or a standard application of it).

The essence of the (mathematical) proof is Fubini's theorem.

We also give the two most common applications of the layer cake formula
 * a representation of the integral of a nonnegative function f:
   ∫ f(ω) ∂μ(ω) = ∫ μ {ω | f(ω) ≥ t} dt
 * a representation of the integral of the p:th power of a nonnegative function f:
   ∫ f(ω)^p ∂μ(ω) = p * ∫ t^(p-1) * μ {ω | f(ω) ≥ t} dt .

Variants of the formulas with measures of sets of the form {ω | f(ω) > t} instead of {ω | f(ω) ≥ t}
are also included.

## Main results

 * `lintegral_comp_eq_lintegral_meas_le_mul` and `lintegral_comp_eq_lintegral_meas_lt_mul`:
   The general layer cake formulas with Lebesgue integrals, written in terms of measures of
   sets of the forms {ω | t ≤ f(ω)} and {ω | t < f(ω)}, respectively.
 * `lintegral_eq_lintegral_meas_le` and `lintegral_eq_lintegral_meas_lt`:
   The most common special cases of the layer cake formulas, stating that for a nonnegative
   function f we have ∫ f(ω) ∂μ(ω) = ∫ μ {ω | f(ω) ≥ t} dt and
   ∫ f(ω) ∂μ(ω) = ∫ μ {ω | f(ω) > t} dt, respectively.
 * `lintegral_rpow_eq_lintegral_meas_le_mul` and `lintegral_rpow_eq_lintegral_meas_lt_mul`:
   Other common special cases of the layer cake formulas, stating that for a nonnegative function f
   and p > 0, we have ∫ f(ω)^p ∂μ(ω) = p * ∫ μ {ω | f(ω) ≥ t} * t^(p-1) dt and
   ∫ f(ω)^p ∂μ(ω) = p * ∫ μ {ω | f(ω) > t} * t^(p-1) dt, respectively.

## Tags

layer cake representation, Cavalieri's principle, tail probability formula
-/


noncomputable section

open scoped ENNReal MeasureTheory

open Set MeasureTheory Filter

/-! ### Layercake formula -/


section Layercake

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {f : α → ℝ} {g : ℝ → ℝ} {s : Set α}

/-- An auxiliary version of the layer cake formula (Cavalieri's principle, tail probability
formula), with a measurability assumption that would also essentially follow from the
integrability assumptions.

See `MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul` and
`lintegral_comp_eq_lintegral_meas_lt_mul` for the main formulations of the layer
cake formula. -/
theorem lintegral_comp_eq_lintegral_meas_le_mul_of_measurable (μ : Measure α) [SigmaFinite μ]
    (f_nn : 0 ≤ f) (f_mble : Measurable f) (g_intble : ∀ t > 0, IntervalIntegrable g volume 0 t)
    (g_mble : Measurable g) (g_nn : ∀ t > 0, 0 ≤ g t) :
    (∫⁻ ω, ENNReal.ofReal (∫ t in (0)..f ω, g t) ∂μ) =
      ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} * ENNReal.ofReal (g t) := by
  have g_intble' : ∀ t : ℝ, 0 ≤ t → IntervalIntegrable g volume 0 t := by
    intro t ht
    cases' eq_or_lt_of_le ht with h h
    · simp [← h]
    · exact g_intble t h
  have integrand_eq :
    ∀ ω, ENNReal.ofReal (∫ t in (0)..f ω, g t) = ∫⁻ t in Ioc 0 (f ω), ENNReal.ofReal (g t) := by
    intro ω
    have g_ae_nn : 0 ≤ᵐ[volume.restrict (Ioc 0 (f ω))] g := by
      filter_upwards [self_mem_ae_restrict (measurableSet_Ioc : MeasurableSet (Ioc 0 (f ω)))] with x
        hx using g_nn x hx.1
    rw [← ofReal_integral_eq_lintegral_ofReal (g_intble' (f ω) (f_nn ω)).1 g_ae_nn]
    congr
    exact intervalIntegral.integral_of_le (f_nn ω)
  simp_rw [integrand_eq, ← lintegral_indicator (fun t => ENNReal.ofReal (g t)) measurableSet_Ioc]
  -- Porting note: was part of `simp_rw` on the previous line, but didn't trigger.
  rw [← lintegral_indicator _ measurableSet_Ioi]
  rw [lintegral_lintegral_swap]
  · apply congr_arg
    funext s
    have aux₁ :
      (fun x => (Ioc 0 (f x)).indicator (fun t : ℝ => ENNReal.ofReal (g t)) s) = fun x =>
        ENNReal.ofReal (g s) * (Ioi (0 : ℝ)).indicator (fun _ => 1) s *
          (Ici s).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) (f x) := by
      funext a
      by_cases s ∈ Ioc (0 : ℝ) (f a)
      · simp only [h, show s ∈ Ioi (0 : ℝ) from h.1, show f a ∈ Ici s from h.2, indicator_of_mem,
          mul_one]
      · have h_copy := h
        simp only [mem_Ioc, not_and, not_le] at h
        by_cases h' : 0 < s
        · simp only [h_copy, h h', indicator_of_not_mem, not_false_iff, mem_Ici, not_le,
            MulZeroClass.mul_zero]
        · have : s ∉ Ioi (0 : ℝ) := h'
          simp only [this, h', indicator_of_not_mem, not_false_iff, MulZeroClass.mul_zero,
            MulZeroClass.zero_mul, mem_Ioc, false_and_iff]
    simp_rw [aux₁]
    rw [lintegral_const_mul']
    swap;
    · apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      -- Porting note: was
      -- by_cases s ∈ Ioi (0 : ℝ) <;> · simp [h]
      by_cases h : (0 : ℝ) < s <;> · simp [indicator_apply, h]
    simp_rw [show
        (fun a => (Ici s).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) (f a)) = fun a =>
          {a : α | s ≤ f a}.indicator (fun _ => 1) a
        by funext a; by_cases s ≤ f a <;> simp [h]]
    rw [lintegral_indicator]
    swap; · exact f_mble measurableSet_Ici
    rw [lintegral_one, Measure.restrict_apply MeasurableSet.univ, univ_inter, indicator_mul_left,
      mul_assoc,
      show
        (Ioi 0).indicator (fun _x : ℝ => (1 : ℝ≥0∞)) s * μ {a : α | s ≤ f a} =
          (Ioi 0).indicator (fun _x : ℝ => 1 * μ {a : α | s ≤ f a}) s
        by by_cases 0 < s <;> simp [h]]
    simp_rw [mul_comm _ (ENNReal.ofReal _), one_mul]
    rfl
  have aux₂ :
    (Function.uncurry fun (x : α) (y : ℝ) =>
        (Ioc 0 (f x)).indicator (fun t : ℝ => ENNReal.ofReal (g t)) y) =
      {p : α × ℝ | p.2 ∈ Ioc 0 (f p.1)}.indicator fun p => ENNReal.ofReal (g p.2) := by
    funext p
    cases p with | mk p_fst p_snd => ?_
    rw [Function.uncurry_apply_pair]
    by_cases p_snd ∈ Ioc 0 (f p_fst)
    · have h' : (p_fst, p_snd) ∈ {p : α × ℝ | p.snd ∈ Ioc 0 (f p.fst)} := h
      rw [Set.indicator_of_mem h', Set.indicator_of_mem h]
    · have h' : (p_fst, p_snd) ∉ {p : α × ℝ | p.snd ∈ Ioc 0 (f p.fst)} := h
      rw [Set.indicator_of_not_mem h', Set.indicator_of_not_mem h]
  rw [aux₂]
  have mble := measurableSet_region_between_oc measurable_zero f_mble MeasurableSet.univ
  simp_rw [mem_univ, Pi.zero_apply, true_and_iff] at mble
  exact (ENNReal.measurable_ofReal.comp (g_mble.comp measurable_snd)).aemeasurable.indicator mble
#align measure_theory.lintegral_comp_eq_lintegral_meas_le_mul_of_measurable MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul_of_measurable

/-- The layer cake formula / Cavalieri's principle / tail probability formula:

Let `f` be a non-negative measurable function on a sigma-finite measure space. Let `G` be an
increasing absolutely continuous function on the positive real line, vanishing at the origin,
with derivative `G' = g`. Then the integral of the composition `G ∘ f` can be written as
the integral over the positive real line of the "tail measures" `μ {ω | f(ω) ≥ t}` of `f`
weighted by `g`.

Roughly speaking, the statement is: `∫⁻ (G ∘ f) ∂μ = ∫⁻ t in (0).. ∞, g(t) * μ {ω | f(ω) ≥ t}`.

See `lintegral_comp_eq_lintegral_meas_lt_mul` for a version with sets of the form `{ω | f(ω) > t}`
instead. -/
theorem lintegral_comp_eq_lintegral_meas_le_mul (μ : Measure α) [SigmaFinite μ] (f_nn : 0 ≤ f)
    (f_mble : Measurable f) (g_intble : ∀ t > 0, IntervalIntegrable g volume 0 t)
    (g_nn : ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ g t) :
    (∫⁻ ω, ENNReal.ofReal (∫ t in (0)..f ω, g t) ∂μ) =
      ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} * ENNReal.ofReal (g t) := by
  have ex_G : ∃ G : ℝ → ℝ, Measurable G ∧ 0 ≤ G ∧ g =ᵐ[volume.restrict (Ioi 0)] G := by
    refine' AEMeasurable.exists_measurable_nonneg _ g_nn
    exact aemeasurable_Ioi_of_forall_Ioc fun t ht => (g_intble t ht).1.1.aemeasurable
  rcases ex_G with ⟨G, G_mble, G_nn, g_eq_G⟩
  have g_eq_G_on : ∀ t, g =ᵐ[volume.restrict (Ioc 0 t)] G := fun t =>
    ae_mono (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl) g_eq_G
  have G_intble : ∀ t > 0, IntervalIntegrable G volume 0 t := by
    refine' fun t t_pos => ⟨(g_intble t t_pos).1.congr_fun_ae (g_eq_G_on t), _⟩
    rw [Ioc_eq_empty_of_le t_pos.lt.le]
    exact integrableOn_empty
  have eq₁ :
    (∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} * ENNReal.ofReal (g t)) =
      ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} * ENNReal.ofReal (G t) := by
    apply lintegral_congr_ae
    filter_upwards [g_eq_G] with a ha
    rw [ha]
  have eq₂ : ∀ ω, (∫ t in (0)..f ω, g t) = ∫ t in (0)..f ω, G t := by
    refine' fun ω => intervalIntegral.integral_congr_ae _
    have fω_nn : 0 ≤ f ω := f_nn ω
    rw [uIoc_of_le fω_nn, ←
      ae_restrict_iff' (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) (f ω)))]
    exact g_eq_G_on (f ω)
  simp_rw [eq₁, eq₂]
  exact
    lintegral_comp_eq_lintegral_meas_le_mul_of_measurable μ f_nn f_mble G_intble G_mble
      fun t _ => G_nn t
#align measure_theory.lintegral_comp_eq_lintegral_meas_le_mul MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul

/-- The standard case of the layer cake formula / Cavalieri's principle / tail probability formula:

For a nonnegative function `f` on a sigma-finite measure space, the Lebesgue integral of `f` can
be written (roughly speaking) as: `∫⁻ f ∂μ = ∫⁻ t in (0).. ∞, μ {ω | f(ω) ≥ t}`.

See `lintegral_eq_lintegral_meas_lt` for a version with sets of the form `{ω | f(ω) > t}`
instead. -/
theorem lintegral_eq_lintegral_meas_le (μ : Measure α) [SigmaFinite μ] (f_nn : 0 ≤ f)
    (f_mble : Measurable f) :
    (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ) = ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} := by
  set cst := fun _ : ℝ => (1 : ℝ)
  have cst_intble : ∀ t > 0, IntervalIntegrable cst volume 0 t := fun _ _ =>
    intervalIntegrable_const
  have key :=
    lintegral_comp_eq_lintegral_meas_le_mul μ f_nn f_mble cst_intble
      (eventually_of_forall fun _ => zero_le_one)
  simp_rw [ENNReal.ofReal_one, mul_one] at key
  rw [← key]
  congr with ω
  simp only [intervalIntegral.integral_const, sub_zero, Algebra.id.smul_eq_mul, mul_one]
#align measure_theory.lintegral_eq_lintegral_meas_le MeasureTheory.lintegral_eq_lintegral_meas_le

/-- An application of the layer cake formula / Cavalieri's principle / tail probability formula:

For a nonnegative function `f` on a sigma-finite measure space, the Lebesgue integral of `f` can
be written (roughly speaking) as: `∫⁻ f^p ∂μ = p * ∫⁻ t in (0).. ∞, t^(p-1) * μ {ω | f(ω) ≥ t}`.

See `lintegral_rpow_eq_lintegral_meas_lt_mul` for a version with sets of the form `{ω | f(ω) > t}`
instead. -/
theorem lintegral_rpow_eq_lintegral_meas_le_mul (μ : Measure α) [SigmaFinite μ] (f_nn : 0 ≤ f)
    (f_mble : Measurable f) {p : ℝ} (p_pos : 0 < p) :
    (∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ) =
      ENNReal.ofReal p * ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} * ENNReal.ofReal (t ^ (p - 1)) := by
  have one_lt_p : -1 < p - 1 := by linarith
  have obs : ∀ x : ℝ, (∫ t : ℝ in (0)..x, t ^ (p - 1)) = x ^ p / p := by
    intro x
    rw [integral_rpow (Or.inl one_lt_p)]
    simp [Real.zero_rpow p_pos.ne.symm]
  set g := fun t : ℝ => t ^ (p - 1)
  have g_nn : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ g t := by
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    intro t t_pos
    exact Real.rpow_nonneg_of_nonneg (mem_Ioi.mp t_pos).le (p - 1)
  have g_intble : ∀ t > 0, IntervalIntegrable g volume 0 t := fun _ _ =>
    intervalIntegral.intervalIntegrable_rpow' one_lt_p
  have key := lintegral_comp_eq_lintegral_meas_le_mul μ f_nn f_mble g_intble g_nn
  rw [← key, ← lintegral_const_mul (ENNReal.ofReal p)] <;> simp_rw [obs]
  · congr with ω
    rw [← ENNReal.ofReal_mul p_pos.le, mul_div_cancel' (f ω ^ p) p_pos.ne.symm]
  · exact ((f_mble.pow measurable_const).div_const p).ennreal_ofReal
#align measure_theory.lintegral_rpow_eq_lintegral_meas_le_mul MeasureTheory.lintegral_rpow_eq_lintegral_meas_le_mul

end MeasureTheory

end Layercake

section LayercakeLT

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

variable {β : Type*} [MeasurableSpace β] [MeasurableSingletonClass β]

namespace Measure

theorem meas_le_ne_meas_lt_subset_meas_pos {R : Type*} [LinearOrder R] [MeasurableSpace R]
    [MeasurableSingletonClass R] {g : α → R} (g_mble : Measurable g) {t : R}
    (ht : μ {a : α | t ≤ g a} ≠ μ {a : α | t < g a}) : 0 < μ {a : α | g a = t} := by
  have uni : {a : α | t ≤ g a} = {a : α | t < g a} ∪ {a : α | t = g a} := by
    ext a
    simp only [mem_setOf, mem_union]
    apply le_iff_lt_or_eq
  rw [show {a : α | t = g a} = {a : α | g a = t} by simp_rw [eq_comm]] at uni
  have disj : {a : α | t < g a} ∩ {a : α | g a = t} = ∅ := by
    ext a
    simp only [mem_inter_iff, mem_setOf, mem_empty_iff_false, iff_false_iff, not_and]
    exact ne_of_gt
  have μ_add : μ {a : α | t ≤ g a} = μ {a : α | t < g a} + μ {a : α | g a = t} := by
    rw [uni,
      measure_union (disjoint_iff_inter_eq_empty.mpr disj)
        (g_mble (Finite.measurableSet (finite_singleton t)))]
  by_contra con
  rw [not_lt, nonpos_iff_eq_zero] at con
  rw [con, add_zero] at μ_add
  exact ht μ_add
#align measure.meas_le_ne_meas_lt_subset_meas_pos Measure.meas_le_ne_meas_lt_subset_meas_pos

theorem countable_meas_le_ne_meas_lt [SigmaFinite μ] {R : Type*} [LinearOrder R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {g : α → R} (g_mble : Measurable g) :
    {t : R | μ {a : α | t ≤ g a} ≠ μ {a : α | t < g a}}.Countable :=
  Countable.mono (show _ from fun _ ht => meas_le_ne_meas_lt_subset_meas_pos μ g_mble ht)
    (Measure.countable_meas_level_set_pos g_mble)
#align measure.countable_meas_le_ne_meas_lt Measure.countable_meas_le_ne_meas_lt

theorem meas_le_ae_eq_meas_lt [SigmaFinite μ] {R : Type*} [LinearOrder R] [MeasurableSpace R]
    [MeasurableSingletonClass R] (ν : Measure R) [NoAtoms ν] {g : α → R} (g_mble : Measurable g) :
    (fun t => μ {a : α | t ≤ g a}) =ᵐ[ν] fun t => μ {a : α | t < g a} :=
  Set.Countable.measure_zero (Measure.countable_meas_le_ne_meas_lt μ g_mble) _
#align measure.meas_le_ae_eq_meas_lt Measure.meas_le_ae_eq_meas_lt

end Measure

variable {f : α → ℝ} {g : ℝ → ℝ} {s : Set α}

/-- The layer cake formula / Cavalieri's principle / tail probability formula:

Let `f` be a non-negative measurable function on a sigma-finite measure space. Let `G` be an
increasing absolutely continuous function on the positive real line, vanishing at the origin,
with derivative `G' = g`. Then the integral of the composition `G ∘ f` can be written as
the integral over the positive real line of the "tail measures" `μ {ω | f(ω) > t}` of `f`
weighted by `g`.

Roughly speaking, the statement is: `∫⁻ (G ∘ f) ∂μ = ∫⁻ t in (0).. ∞, g(t) * μ {ω | f(ω) > t}`.

See `lintegral_comp_eq_lintegral_meas_le_mul` for a version with sets of the form `{ω | f(ω) ≥ t}`
instead. -/
theorem lintegral_comp_eq_lintegral_meas_lt_mul (μ : Measure α) [SigmaFinite μ] (f_nn : 0 ≤ f)
    (f_mble : Measurable f) (g_intble : ∀ t > 0, IntervalIntegrable g volume 0 t)
    (g_nn : ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ g t) :
    (∫⁻ ω, ENNReal.ofReal (∫ t in (0)..f ω, g t) ∂μ) =
      ∫⁻ t in Ioi 0, μ {a : α | t < f a} * ENNReal.ofReal (g t) := by
  rw [lintegral_comp_eq_lintegral_meas_le_mul μ f_nn f_mble g_intble g_nn]
  apply lintegral_congr_ae
  filter_upwards [Measure.meas_le_ae_eq_meas_lt μ (volume.restrict (Ioi 0)) f_mble] with t ht
  rw [ht]
#align lintegral_comp_eq_lintegral_meas_lt_mul lintegral_comp_eq_lintegral_meas_lt_mul

/-- The standard case of the layer cake formula / Cavalieri's principle / tail probability formula:

For a nonnegative function `f` on a sigma-finite measure space, the Lebesgue integral of `f` can
be written (roughly speaking) as: `∫⁻ f ∂μ = ∫⁻ t in (0).. ∞, μ {ω | f(ω) > t}`.

See `lintegral_eq_lintegral_meas_le` for a version with sets of the form `{ω | f(ω) ≥ t}`
instead. -/
theorem lintegral_eq_lintegral_meas_lt (μ : Measure α) [SigmaFinite μ] (f_nn : 0 ≤ f)
    (f_mble : Measurable f) :
    (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ) = ∫⁻ t in Ioi 0, μ {a : α | t < f a} := by
  rw [lintegral_eq_lintegral_meas_le μ f_nn f_mble]
  apply lintegral_congr_ae
  filter_upwards [Measure.meas_le_ae_eq_meas_lt μ (volume.restrict (Ioi 0)) f_mble] with t ht
  rw [ht]
#align lintegral_eq_lintegral_meas_lt lintegral_eq_lintegral_meas_lt

/-- An application of the layer cake formula / Cavalieri's principle / tail probability formula:

For a nonnegative function `f` on a sigma-finite measure space, the Lebesgue integral of `f` can
be written (roughly speaking) as: `∫⁻ f^p ∂μ = p * ∫⁻ t in (0).. ∞, t^(p-1) * μ {ω | f(ω) > t}`.

See `lintegral_rpow_eq_lintegral_meas_le_mul` for a version with sets of the form `{ω | f(ω) ≥ t}`
instead. -/
theorem lintegral_rpow_eq_lintegral_meas_lt_mul (μ : Measure α) [SigmaFinite μ] (f_nn : 0 ≤ f)
    (f_mble : Measurable f) {p : ℝ} (p_pos : 0 < p) :
    (∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ) =
      ENNReal.ofReal p * ∫⁻ t in Ioi 0, μ {a : α | t < f a} * ENNReal.ofReal (t ^ (p - 1)) := by
  rw [lintegral_rpow_eq_lintegral_meas_le_mul μ f_nn f_mble p_pos]
  apply congr_arg fun z => ENNReal.ofReal p * z
  apply lintegral_congr_ae
  filter_upwards [Measure.meas_le_ae_eq_meas_lt μ (volume.restrict (Ioi 0)) f_mble] with t ht
  rw [ht]
#align lintegral_rpow_eq_lintegral_meas_lt_mul lintegral_rpow_eq_lintegral_meas_lt_mul

end LayercakeLT
