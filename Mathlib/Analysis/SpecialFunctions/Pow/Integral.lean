/-
Copyright (c) 2022 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.Tactic.MoveAdd

/-!
# The integral of the real power of a nonnegative function

In this file, we give a common application of the layer cake formula ---
a representation of the integral of the p:th power of a nonnegative function `f`:
`∫ f(ω)^p ∂μ(ω) = p * ∫ t^(p-1) * μ {ω | f(ω) ≥ t} dt`.

A variant of the formula with measures of sets of the form `{ω | f(ω) > t}` instead of
`{ω | f(ω) ≥ t}` is also included.

Moreover, we prove that `‖x‖ ^ (-d + ε)` is locally integrable.

## Main results

* `MeasureTheory.lintegral_rpow_eq_lintegral_meas_le_mul` and
  `MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul`:
  other common special cases of the layer cake formulas, stating that for a nonnegative function `f`
  and `p > 0`, we have `∫ f(ω)ᵖ ∂μ(ω) = p * ∫ μ {ω | f(ω) ≥ t} * tᵖ⁻¹ dt` and
  `∫ f(ω)ᵖ ∂μ(ω) = p * ∫ μ {ω | f(ω) > t} * tᵖ⁻¹ dt`, respectively.
* `MeasureTheory.locallyIntegrable_of_norm_le_rpow`:
  a function that is dominated by `‖x‖ ^ (-d + ε)` is locally integrable.

## Tags

layer cake representation, Cavalieri's principle, tail probability formula
-/

public section

open Set

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

section Layercake

/-- An application of the layer cake formula / Cavalieri's principle / tail probability formula:

For a nonnegative function `f` on a measure space, the Lebesgue integral of `f` can
be written (roughly speaking) as: `∫⁻ f^p ∂μ = p * ∫⁻ t in 0..∞, t^(p-1) * μ {ω | f(ω) ≥ t}`.

See `MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul` for a version with sets of the form
`{ω | f(ω) > t}` instead. -/
theorem lintegral_rpow_eq_lintegral_meas_le_mul
    {f : α → ℝ} (f_nn : 0 ≤ᵐ[μ] f) (f_mble : AEMeasurable f μ) {p : ℝ} (p_pos : 0 < p) :
    ∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ =
      ENNReal.ofReal p * ∫⁻ t in Ioi 0, μ {a : α | t ≤ f a} * ENNReal.ofReal (t ^ (p - 1)) := by
  have one_lt_p : -1 < p - 1 := by linarith
  have obs : ∀ x : ℝ, ∫ t : ℝ in 0..x, t ^ (p - 1) = x ^ p / p := by
    intro x
    rw [integral_rpow (Or.inl one_lt_p)]
    simp [Real.zero_rpow p_pos.ne.symm]
  set g := fun t : ℝ => t ^ (p - 1)
  have g_nn : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ g t := by
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    intro t t_pos
    exact Real.rpow_nonneg (mem_Ioi.mp t_pos).le (p - 1)
  have g_intble (t) (ht : 0 < t) : IntervalIntegrable g volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' one_lt_p
  have key := lintegral_comp_eq_lintegral_meas_le_mul μ f_nn f_mble g_intble g_nn
  rw [← key, ← lintegral_const_mul'' (ENNReal.ofReal p)] <;> simp_rw [obs]
  · congr with ω
    rw [← ENNReal.ofReal_mul p_pos.le, mul_div_cancel₀ (f ω ^ p) p_pos.ne.symm]
  · have aux := (measurable_const (a := p)).aemeasurable (μ := μ)
    exact measurable_id.ennreal_ofReal.comp_aemeasurable <| (f_mble.pow aux).div_const p

end Layercake

section LayercakeLT

/-- An application of the layer cake formula / Cavalieri's principle / tail probability formula:

For a nonnegative function `f` on a measure space, the Lebesgue integral of `f` can
be written (roughly speaking) as: `∫⁻ f^p ∂μ = p * ∫⁻ t in 0..∞, t^(p-1) * μ {ω | f(ω) > t}`.

See `MeasureTheory.lintegral_rpow_eq_lintegral_meas_le_mul` for a version with sets of the form
`{ω | f(ω) ≥ t}` instead. -/
theorem lintegral_rpow_eq_lintegral_meas_lt_mul
    {f : α → ℝ} (f_nn : 0 ≤ᵐ[μ] f) (f_mble : AEMeasurable f μ) {p : ℝ} (p_pos : 0 < p) :
    ∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ =
      ENNReal.ofReal p * ∫⁻ t in Ioi 0, μ {a : α | t < f a} * ENNReal.ofReal (t ^ (p - 1)) := by
  rw [lintegral_rpow_eq_lintegral_meas_le_mul μ f_nn f_mble p_pos]
  apply congr_arg fun z => ENNReal.ofReal p * z
  apply lintegral_congr_ae
  filter_upwards [meas_le_ae_eq_meas_lt μ (volume.restrict (Ioi 0)) f] with t ht
  rw [ht]

end LayercakeLT

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F]
  {μ : Measure E} [μ.IsAddHaarMeasure]

open Set Metric in
lemma integrableOn_ball_of_norm_le_rpow (hd : 1 ≤ Module.finrank ℝ E) {f : E → F} {C α r : ℝ}
    (hα : α < Module.finrank ℝ E) (h_decay : ∀ᵐ x ∂μ.restrict (ball 0 r), ‖f x‖ ≤ C * ‖x‖ ^ (-α))
    (h_meas : AEStronglyMeasurable f μ) :
    IntegrableOn f (ball 0 r) μ := by
  haveI : Nontrivial E := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    positivity
  have hint : IntegrableOn (fun y ↦ y ^ (Module.finrank ℝ E - 1) • (C * y ^ (-α))) (Ioo 0 r) := by
    simp only [smul_eq_mul]
    have h_rpow : IntegrableOn (fun y ↦ y ^ ((Module.finrank ℝ E : ℝ) - 1 - α)) (Ioo 0 r) := by
      by_cases! hr : 0 < r
      · rw [intervalIntegral.integrableOn_Ioo_rpow_iff hr]
        linarith
      · simp [hr]
    apply IntegrableOn.congr_fun (h_rpow.const_mul C) ?_ measurableSet_Ioo
    intro y ⟨hy, _⟩
    simp only
    move_mul [C]
    rw [← Real.rpow_natCast y (Module.finrank ℝ E - 1), ← Real.rpow_add hy]
    congr
    norm_cast
  rw [← integrableOn_fun_norm_addHaar μ] at hint
  exact Integrable.mono' hint h_meas.restrict h_decay

/-- A function that is dominated by `‖x‖ ^ (-d + ε)` is locally integrable -/
theorem locallyIntegrable_of_norm_le_rpow (hdim : 1 ≤ Module.finrank ℝ E) {f : E → F} {C α : ℝ}
    (hα : α < Module.finrank ℝ E)
    (h_decay : ∀ᵐ x ∂μ, ‖f x‖ ≤ C * ‖x‖ ^ (-α)) (h_meas : AEStronglyMeasurable f μ) :
    LocallyIntegrable f μ := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR_pos, hR⟩ := hK.isBounded.exists_pos_norm_lt
  exact (integrableOn_ball_of_norm_le_rpow hdim hα (ae_restrict_of_ae h_decay) h_meas).mono_set
    (mem_ball_zero_iff.mpr <| hR · ·)

end MeasureTheory
