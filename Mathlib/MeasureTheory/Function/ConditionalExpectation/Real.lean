/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym

/-!

# Conditional expectation of real-valued functions

This file proves some results regarding the conditional expectation of real-valued functions.

## Main results

* `MeasureTheory.rnDeriv_ae_eq_condExp`: the conditional expectation `μ[f | m]` is equal to the
  Radon-Nikodym derivative of `fμ` restricted on `m` with respect to `μ` restricted on `m`.
* `MeasureTheory.Integrable.uniformIntegrable_condExp`: the conditional expectation of a function
  form a uniformly integrable class.

-/

public section


noncomputable section

open TopologicalSpace MeasureTheory.Lp Filter ContinuousLinearMap

open scoped NNReal ENNReal Topology MeasureTheory

namespace MeasureTheory

variable {α : Type*} {m m0 : MeasurableSpace α} {μ : Measure α}

theorem rnDeriv_ae_eq_condExp {hm : m ≤ m0} [hμm : SigmaFinite (μ.trim hm)] {f : α → ℝ}
    (hf : Integrable f μ) :
    SignedMeasure.rnDeriv ((μ.withDensityᵥ f).trim hm) (μ.trim hm) =ᵐ[μ] μ[f | m] := by
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hf ?_ ?_ ?_
  · exact fun _ _ _ => (integrable_of_integrable_trim hm
      (SignedMeasure.integrable_rnDeriv ((μ.withDensityᵥ f).trim hm) (μ.trim hm))).integrableOn
  · intro s hs _
    conv_rhs => rw [← hf.withDensityᵥ_trim_eq_integral hm hs,
      ← SignedMeasure.withDensityᵥ_rnDeriv_eq ((μ.withDensityᵥ f).trim hm) (μ.trim hm)
        (hf.withDensityᵥ_trim_absolutelyContinuous hm)]
    rw [withDensityᵥ_apply
      (SignedMeasure.integrable_rnDeriv ((μ.withDensityᵥ f).trim hm) (μ.trim hm)) hs,
      ← setIntegral_trim hm _ hs]
    exact (SignedMeasure.measurable_rnDeriv _ _).stronglyMeasurable
  · exact (SignedMeasure.measurable_rnDeriv _ _).stronglyMeasurable.aestronglyMeasurable

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem integral_norm_rpow_condExp_le {p : ℝ} (hp : 1 ≤ p) {f : α → E}
    (hf : Integrable (fun x => ‖f x‖ ^ p) μ) :
    ∫ x, ‖(μ[f | m]) x‖ ^ p ∂μ ≤ ∫ x, ‖f x‖ ^ p ∂μ := by
  have hp' : 0 < p := by linarith
  by_cases! hm : ¬ m ≤ m0
  · simp only [condExp_of_not_le hm, Pi.zero_apply, _root_.norm_zero,
      Real.zero_rpow hp'.ne.symm, integral_zero]
    positivity
  by_cases! hfint : ¬ Integrable f μ
  · simp only [condExp_of_not_integrable hfint, Pi.zero_apply, _root_.norm_zero,
      Real.zero_rpow hp'.ne.symm, integral_zero]
    positivity
  by_cases! hsig : ¬ SigmaFinite (μ.trim hm)
  · simp only [condExp_of_not_sigmaFinite hm hsig, Pi.zero_apply, _root_.norm_zero,
      Real.zero_rpow hp'.ne.symm, integral_zero]
    positivity
  calc
  _ ≤ ∫ x, μ[(fun x => ‖f x‖ ^ p) | m] x ∂μ := by
    refine integral_mono_of_nonneg ?_ integrable_condExp ?_
    · filter_upwards with a; positivity
    · exact Integrable.norm_rpow_condExp_le hp hf
  _ = _ := integral_condExp hm

theorem integral_norm_condExp_le (f : α → E) : ∫ x, ‖(μ[f | m]) x‖ ∂μ ≤ ∫ x, ‖f x‖ ∂μ := by
  by_cases! hfint : ¬ Integrable f μ
  · simpa [condExp_of_not_integrable hfint] using integral_nonneg (fun x => norm_nonneg (f x))
  have : Integrable (fun x => ‖f x‖ ^ (1 : ℝ)) μ := by simpa using hfint.norm
  simpa using integral_norm_rpow_condExp_le (refl 1) this

theorem setIntegral_norm_condExp_le {s : Set α} (hs : MeasurableSet[m] s) (f : α → E) :
    ∫ x in s, ‖(μ[f | m]) x‖ ∂μ ≤ ∫ x in s, ‖f x‖ ∂μ := by
  by_cases! hm : ¬ m ≤ m0
  · simpa [condExp_of_not_le hm] using integral_nonneg (fun x => norm_nonneg (f x))
  by_cases! hfint : ¬ Integrable f μ
  · simpa [condExp_of_not_integrable hfint] using integral_nonneg (fun x => norm_nonneg (f x))
  by_cases! hsig : ¬ SigmaFinite (μ.trim hm)
  · simpa [condExp_of_not_sigmaFinite hm hsig] using integral_nonneg (fun x => norm_nonneg (f x))
  calc
  _ = ∫ x in s, ‖(μ.restrict s)[f | m] x‖ ∂μ :=
    (integral_congr_ae ((condExp_restrict_ae_eq_restrict hm hs hfint).fun_comp norm)).symm
  _  ≤ _ := integral_norm_condExp_le f

lemma condExp_le_nonneg_const [PartialOrder E] [ClosedIciTopology E] [IsOrderedAddMonoid E]
    [IsOrderedModule ℝ E] {f : α → E} {c : E} (hc : 0 ≤ c) (hfc : f ≤ᵐ[μ] fun _ => c) :
    μ[f | m] ≤ᵐ[μ] fun _ => c := by
  by_cases! hm : ¬ m ≤ m0
  · filter_upwards with a using by simp_all [condExp_of_not_le hm]
  by_cases! hfint : ¬ Integrable f μ
  · filter_upwards with a using by simp_all [condExp_of_not_integrable hfint]
  by_cases! hsig : ¬ SigmaFinite (μ.trim hm)
  · filter_upwards with a using by simp_all [condExp_of_not_sigmaFinite hm hsig]
  refine (isCountablySpanning_spanningSets (μ.trim hm)).null_of_forall_restrict_null
    (fun t ⟨n, hn⟩ => ?_) fun t ⟨n, hn⟩ => hn ▸ ?_
  · exact hn ▸ hm _ (measurableSet_spanningSets (μ.trim hm) n)
  have h1 := condExp_restrict_ae_eq_restrict hm (measurableSet_spanningSets (μ.trim hm) n) hfint
  have : IsFiniteMeasure (μ.restrict (spanningSets (μ.trim hm) n)) := isFiniteMeasure_restrict.2
    ((le_trim hm).trans_lt (measure_spanningSets_lt_top (μ.trim hm) n)).ne
  have h2 := condExp_mono (μ := (μ.restrict (spanningSets (μ.trim hm) n))) (m := m)
    hfint.restrict (integrable_const c) (ae_restrict_of_ae hfc)
  rw [← condExp_const (μ := (μ.restrict (spanningSets (μ.trim hm) n))) hm c]
  filter_upwards [h1, h2] with a ha hb
  rwa [← ha]

/-- If `‖f‖` is bounded almost everywhere by `R`, then so is its conditional expectation. -/
theorem ae_bdd_norm_condExp_of_ae_bdd_norm {R : ℝ} {f : α → E} (hbdd : (‖f ·‖) ≤ᵐ[μ] fun _ => R) :
    (‖(μ[f | m]) ·‖) ≤ᵐ[μ] fun _ => R := by
  by_cases! hn : {x | ‖f x‖ ≤ R} = ∅
  · exact measure_mono_null (by simp) <| ae_eq_empty.1 (hn ▸ (ae_eq_univ.2 hbdd).symm)
  exact norm_condExp_le.trans (condExp_le_nonneg_const ((norm_nonneg _).trans hn.some_mem) hbdd)

theorem lpNorm_condExp_le_lpNorm {f : α → E} {p : ℝ≥0∞} (hp : 1 ≤ p) (hf : MemLp f p μ) :
    lpNorm (μ[f | m]) p μ ≤ lpNorm f p μ := by
  have hp' : 0 < p := zero_lt_one.trans_le hp
  by_cases! hm : ¬ m ≤ m0
  · simp [condExp_of_not_le hm]
  by_cases! hsig : ¬ SigmaFinite (μ.trim hm)
  · simp [condExp_of_not_sigmaFinite hm hsig]
  · by_cases! hpt : p ≠ ⊤
    · rw [lpNorm_eq_integral_norm_rpow_toReal hp'.ne.symm hpt hf.1,
        lpNorm_eq_integral_norm_rpow_toReal hp'.ne.symm hpt integrable_condExp.1]
      gcongr ?_ ^ ?_
      have : 1 ≤ p.toReal := by
        rwa [← ENNReal.toReal_one, ENNReal.toReal_le_toReal ENNReal.one_ne_top hpt]
      exact integral_norm_rpow_condExp_le this <|
        (integrable_norm_rpow_iff hf.1 hp'.ne.symm hpt).2 hf
    · by_cases! h : MemLp μ[f | m] ⊤ μ
      · simp_all only [lpNorm_exponent_top_eq_essSup]
        sorry
      · simp_all

theorem MemLp.condExp {f : α → E} {p : ℝ≥0∞} (hp : 1 ≤ p) (hf : MemLp f p μ) :
    MemLp (μ[f | m]) p μ := by
  have hp' : 0 < p := zero_lt_one.trans_le hp
  by_cases! hpt : p ≠ ⊤
  · rw [← integrable_norm_rpow_iff integrable_condExp.1 hp'.ne.symm hpt]
    have hp : 1 ≤ p.toReal := by
      rwa [← ENNReal.toReal_one, ENNReal.toReal_le_toReal ENNReal.one_ne_top hpt]
    have := Integrable.norm_rpow_condExp_le (m := m) hp <|
      (integrable_norm_rpow_iff hf.1 hp'.ne.symm hpt).2 hf
    refine Integrable.mono_nonneg integrable_condExp ?_ ?_ this
    · exact (Real.continuous_rpow_const (zero_le_one.trans hp)).comp_aestronglyMeasurable
        integrable_condExp.norm.1
    · filter_upwards with a; positivity
  · rw [hpt]
    refine memLp_top_of_bound integrable_condExp.1 (essSup (‖f ·‖) μ)
      (ae_bdd_norm_condExp_of_ae_bdd_norm (ae_le_essSup ?_))
    sorry

theorem eLpNorm_condExp_le_eLpNorm {f : α → E} {p : ℝ≥0∞} (hp : 1 ≤ p) (hf : MemLp f p μ) :
    eLpNorm (μ[f | m]) p μ ≤ eLpNorm f p μ := by
  have hp' : 0 < p := zero_lt_one.trans_le hp
  rw [← ofReal_lpNorm hf, ← ofReal_lpNorm]
  · exact ENNReal.ofReal_le_ofReal (lpNorm_condExp_le_lpNorm hp hf)
  · exact hf.condExp hp

theorem eLpNorm_one_condExp_le_eLpNorm (f : α → E) : eLpNorm (μ[f | m]) 1 μ ≤ eLpNorm f 1 μ := by
  by_cases! hfint : ¬ Integrable f μ
  · simp [condExp_of_not_integrable hfint]
  exact eLpNorm_condExp_le_eLpNorm (refl 1) <| memLp_one_iff_integrable.2 hfint

variable [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]

theorem ae_condExp_abs_le_abs_condExp (f : α → E) : |(μ[f | m])| ≤ᵐ[μ] μ[|f| | m] := by
  by_cases! hfint : ¬Integrable f μ
  · simp only [condExp_of_not_integrable hfint, abs_zero]
    apply condExp_nonneg
    filter_upwards with a using (abs_nonneg f a)
  have h1 := condExp_mono (m := m) hfint hfint.abs (.of_forall (fun x => le_abs_self f x))
  have (x : α) := abs_neg (f x) ▸ le_abs_self (- f x)
  have h2 := condExp_mono (m := m) hfint.neg hfint.abs (.of_forall this)
  filter_upwards [h1, h2, condExp_neg f m] with a ha hb hc
  exact abs_le'.2 ⟨ha, hc.symm.le.trans hb⟩

theorem integral_abs_condExp_le (f : α → E) : ∫ x, |μ[f | m] x| ∂μ ≤ ∫ x, |f x| ∂μ := by
  by_cases! hm : ¬ m ≤ m0
  · simpa [condExp_of_not_le hm] using integral_nonneg (fun x => abs_nonneg f x)
  by_cases! hsig : ¬ SigmaFinite (μ.trim hm)
  · simpa [condExp_of_not_sigmaFinite hm hsig] using integral_nonneg (fun x => abs_nonneg f x)
  calc
  _ ≤ ∫ x, μ[|f| | m] x ∂μ :=
    integral_mono_ae integrable_condExp.abs integrable_condExp (ae_condExp_abs_le_abs_condExp f)
  _ = _ := integral_condExp hm

theorem setIntegral_abs_condExp_le {s : Set α} (hs : MeasurableSet[m] s) (f : α → E) :
    ∫ x in s, |μ[f | m] x| ∂μ ≤ ∫ x in s, |f x| ∂μ := by
  by_cases! hm : ¬ m ≤ m0
  · simpa [condExp_of_not_le hm] using integral_nonneg (fun x => abs_nonneg f x)
  by_cases! hfint : ¬ Integrable f μ
  · simpa [condExp_of_not_integrable hfint] using integral_nonneg (fun x => abs_nonneg f x)
  by_cases! hsig : ¬ SigmaFinite (μ.trim hm)
  · simpa [condExp_of_not_sigmaFinite hm hsig] using integral_nonneg (fun x => abs_nonneg f x)
  calc
  _ = ∫ x in s, |(μ.restrict s)[f | m] x| ∂μ :=
    (integral_congr_ae ((condExp_restrict_ae_eq_restrict hm hs hfint).fun_comp abs)).symm
  _  ≤ _ := integral_abs_condExp_le f

/-- If `|f|` is bounded almost everywhere by `R`, then so is its conditional expectation. -/
theorem ae_bdd_abs_condExp_of_ae_bdd_abs {R : E} {f : α → E} (hbdd : |f| ≤ᵐ[μ] fun _ => R) :
    |(μ[f | m])| ≤ᵐ[μ] fun _ => R := by
  by_cases! hn : {x | |f x| ≤ R} = ∅
  · exact measure_mono_null (by simp) <| ae_eq_empty.1 (hn ▸ (ae_eq_univ.2 hbdd).symm)
  have hR : 0 ≤ R := (abs_nonneg _).trans hn.some_mem
  exact (ae_condExp_abs_le_abs_condExp f).trans (condExp_le_nonneg_const (m := m) hR hbdd)

set_option backward.isDefEq.respectTransparency false in
/-- Given an integrable function `g`, the conditional expectations of `g` with respect to
a sequence of sub-σ-algebras is uniformly integrable. -/
theorem Integrable.uniformIntegrable_condExp {ι : Type*} [IsFiniteMeasure μ] {g : α → ℝ}
    (hint : Integrable g μ) {ℱ : ι → MeasurableSpace α} (hℱ : ∀ i, ℱ i ≤ m0) :
    UniformIntegrable (fun i => μ[g | ℱ i]) 1 μ := by
  let A : MeasurableSpace α := m0
  have hmeas : ∀ n, ∀ C, MeasurableSet {x | C ≤ ‖(μ[g|ℱ n]) x‖₊} := fun n C =>
    measurableSet_le measurable_const (stronglyMeasurable_condExp.mono (hℱ n)).measurable.nnnorm
  have hg : MemLp g 1 μ := memLp_one_iff_integrable.2 hint
  refine uniformIntegrable_of le_rfl ENNReal.one_ne_top
    (fun n => (stronglyMeasurable_condExp.mono (hℱ n)).aestronglyMeasurable) fun ε hε => ?_
  by_cases hne : eLpNorm g 1 μ = 0
  · rw [eLpNorm_eq_zero_iff hg.1 one_ne_zero] at hne
    refine ⟨0, fun n => (le_of_eq <|
      (eLpNorm_eq_zero_iff ((stronglyMeasurable_condExp.mono (hℱ n)).aestronglyMeasurable.indicator
        (hmeas n 0)) one_ne_zero).2 ?_).trans (zero_le _)⟩
    filter_upwards [condExp_congr_ae (m := ℱ n) hne] with x hx
    simp only [zero_le', Set.setOf_true, Set.indicator_univ, Pi.zero_apply, hx, condExp_zero]
  obtain ⟨δ, hδ, h⟩ := hg.eLpNorm_indicator_le le_rfl ENNReal.one_ne_top hε
  set C : ℝ≥0 := ⟨δ, hδ.le⟩⁻¹ * (eLpNorm g 1 μ).toNNReal with hC
  have hCpos : 0 < C := mul_pos (inv_pos.2 hδ) (ENNReal.toNNReal_pos hne hg.eLpNorm_lt_top.ne)
  have : ∀ n, μ {x : α | C ≤ ‖(μ[g|ℱ n]) x‖₊} ≤ ENNReal.ofReal δ := by
    intro n
    have : C ^ ENNReal.toReal 1 * μ {x | ENNReal.ofNNReal C ≤ ‖μ[g|ℱ n] x‖₊} ≤
        eLpNorm μ[g | ℱ n] 1 μ ^ ENNReal.toReal 1 := by
      rw [ENNReal.toReal_one, ENNReal.rpow_one]
      convert mul_meas_ge_le_pow_eLpNorm μ one_ne_zero ENNReal.one_ne_top
        (stronglyMeasurable_condExp.mono (hℱ n)).aestronglyMeasurable C
      · rw [ENNReal.toReal_one, ENNReal.rpow_one, enorm_eq_nnnorm]
    rw [ENNReal.toReal_one, ENNReal.rpow_one, mul_comm, ←
      ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.coe_ne_zero.2 hCpos.ne'))
        (Or.inl ENNReal.coe_lt_top.ne)] at this
    simp_rw [ENNReal.coe_le_coe] at this
    refine this.trans ?_
    rw [ENNReal.div_le_iff_le_mul (Or.inl (ENNReal.coe_ne_zero.2 hCpos.ne'))
        (Or.inl ENNReal.coe_lt_top.ne),
      hC, Nonneg.inv_mk, ENNReal.coe_mul, ENNReal.coe_toNNReal hg.eLpNorm_lt_top.ne, ← mul_assoc, ←
      ENNReal.ofReal_eq_coe_nnreal, ← ENNReal.ofReal_mul hδ.le, mul_inv_cancel₀ hδ.ne',
      ENNReal.ofReal_one, one_mul, ENNReal.rpow_one]
    exact eLpNorm_one_condExp_le_eLpNorm _
  refine ⟨C, fun n => le_trans ?_ (h {x : α | C ≤ ‖(μ[g|ℱ n]) x‖₊} (hmeas n C) (this n))⟩
  have hmeasℱ : MeasurableSet[ℱ n] {x : α | C ≤ ‖(μ[g|ℱ n]) x‖₊} :=
    @measurableSet_le _ _ _ _ _ (ℱ n) _ _ _ _ _ measurable_const
      (@Measurable.nnnorm _ _ _ _ _ (ℱ n) _ stronglyMeasurable_condExp.measurable)
  rw [← eLpNorm_congr_ae (condExp_indicator hint hmeasℱ)]
  exact eLpNorm_one_condExp_le_eLpNorm _

end MeasureTheory
