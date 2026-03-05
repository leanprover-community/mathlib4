/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.ConditionalLExpectation
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
# Radon-Nikodym derivatives and conditional expectations

We express the Radon-Nikodym derivative of the pushforward of measures in terms of the conditional
expectation of the Radon-Nikodym derivative of the original measures.

## Main statements

In all statements, `μ` and `ν` are measures with `μ ≪ ν`.

* `toReal_rnDeriv_map`: the Radon-Nikodym derivative `∂(μ.map g)/∂(ν.map g)` of the pushforward of
  measures by a function `g : 𝓧 → 𝓨` evaluated at `g x` is a.e.-equal to the conditional expectation
  of `∂μ/∂ν` with respect to the comap by `g` of the sigma-algebra on `𝓨`.
* `toReal_rnDeriv_trim`: the Radon-Nikodym derivative `∂(μ.trim hm)/∂(ν.trim hm)` of the trimmed
  measures (for `hm : m ≤ m0` stating that `m` is a sub-sigma-algebra of `m0`) is a.e.-equal to the
  conditional expectation of `∂μ/∂ν` with respect to the sigma-algebra `m`.

-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {𝓧 𝓨 : Type*} {m m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨} {μ ν : Measure 𝓧}

/-- The Radon-Nikodym derivative `∂(μ.map g)/∂(ν.map g)` of the pushforward of measures by
a function `g : 𝓧 → 𝓨` evaluated at `g x` is a.e.-equal to the conditional expectation of `∂μ/∂ν`
with respect to the comap by `g` of the sigma-algebra on `𝓨`.

See `toReal_rnDeriv_map_ae_eq_trim` for the same statement, but with a.e. equality with respect to
the trimmed measure `ν.trim hg.comap_le`. -/
lemma toReal_rnDeriv_map [IsFiniteMeasure μ] (hμν : μ ≪ ν)
    {g : 𝓧 → 𝓨} (hg : Measurable g) [hσ : SigmaFinite (ν.map g)] :
    (fun a ↦ ((μ.map g).rnDeriv (ν.map g) (g a)).toReal) =ᵐ[ν]
      ν[(fun a ↦ (μ.rnDeriv ν a).toReal) | m𝓨.comap g] := by
  have : SigmaFinite (ν.trim hg.comap_le) := by
    rw [← map_trim_comap hg] at hσ
    refine SigmaFinite.of_map (ν.trim hg.comap_le) ?_ hσ
    refine Measurable.aemeasurable ?_
    exact measurable_iff_comap_le.mpr le_rfl
  have : SigmaFinite ν := SigmaFinite.of_map _ hg.aemeasurable hσ
  refine ae_eq_condExp_of_forall_setIntegral_eq _ (by fun_prop) ?_ ?_ ?_
  · rintro _ ⟨t, _, rfl⟩ _
    refine Integrable.integrableOn ?_
    change Integrable ((fun x ↦ ((μ.map g).rnDeriv (ν.map g) x).toReal) ∘ g) ν
    rw [← integrable_map_measure (f := g) (Measurable.aestronglyMeasurable (by fun_prop))
      (by fun_prop)]
    fun_prop
  · rintro _ ⟨t, ht, rfl⟩ _
    calc ∫ x in g ⁻¹' t, ((μ.map g).rnDeriv (ν.map g) (g x)).toReal ∂ν
    _ = ∫ y in t, ((μ.map g).rnDeriv (ν.map g) y).toReal ∂(ν.map g) := by
      rw [setIntegral_map ht _ hg.aemeasurable]
      exact Measurable.aestronglyMeasurable (by fun_prop)
    _ = ∫ x in g ⁻¹' t, (μ.rnDeriv ν x).toReal ∂ν := by
      rw [Measure.setIntegral_toReal_rnDeriv (hμν.map hg),
        Measure.setIntegral_toReal_rnDeriv hμν, measureReal_def, Measure.map_apply hg ht,
        measureReal_def]
  · refine (Measurable.ennreal_toReal fun s hs ↦ ?_).aestronglyMeasurable
    exact ⟨_, Measure.measurable_rnDeriv _ _ hs, rfl⟩

lemma toReal_condLExp {α : Type*} (m : MeasurableSpace α) {mα : MeasurableSpace α} {μ : Measure α}
    {f : α → ℝ≥0∞} (hf_meas : AEMeasurable f μ) (hf : ∫⁻ x, f x ∂μ ≠ ∞) :
    (fun x ↦ (μ⁻[f | m] x).toReal) =ᵐ[μ] μ[fun x ↦ (f x).toReal | m] := by
  by_cases hm : m ≤ mα
  swap; · simp [condLExp_of_not_le hm, condExp_of_not_le hm]; rfl
  by_cases hμ : SigmaFinite (μ.trim hm)
  swap; · simp [condLExp_of_not_sigmaFinite hm hμ, condExp_of_not_sigmaFinite hm hμ]; rfl
  refine ae_eq_condExp_of_forall_setIntegral_eq hm (E := ℝ) ?_ ?_ ?_ ?_ (μ := μ)
  · rwa [integrable_toReal_iff]
    · fun_prop
    · suffices ∀ᵐ (x : α) ∂μ, f x < ⊤ by filter_upwards [this] with x hx using hx.ne
      exact ae_lt_top' (by fun_prop) hf
  · intro s hs hsμ
    refine Integrable.integrableOn ?_
    rw [integrable_toReal_iff]
    · rwa [lintegral_condLExp]
    · fun_prop
    · exact condLExp_ne_top hf
  · intro s hs hsμ
    rw [integral_toReal, integral_toReal, setLIntegral_condLExp _ _ _ hs]
    · fun_prop
    · refine ae_lt_top' hf_meas.restrict ?_
      exact ((setLIntegral_le_lintegral _ _).trans_lt hf.lt_top).ne
    · fun_prop
    · exact ae_restrict_of_ae (condLExp_lt_top hf)
  · refine StronglyMeasurable.aestronglyMeasurable ?_
    fun_prop

lemma rnDeriv_map [IsFiniteMeasure μ] (hμν : μ ≪ ν)
    {g : 𝓧 → 𝓨} (hg : Measurable g) [hσ : SigmaFinite (ν.map g)] :
    (fun a ↦ (μ.map g).rnDeriv (ν.map g) (g a)) =ᵐ[ν] ν⁻[μ.rnDeriv ν | m𝓨.comap g] := by
  have : SigmaFinite (ν.trim hg.comap_le) := by
    rw [← map_trim_comap hg] at hσ
    refine SigmaFinite.of_map (ν.trim hg.comap_le) ?_ hσ
    refine Measurable.aemeasurable ?_
    exact measurable_iff_comap_le.mpr le_rfl
  have : SigmaFinite ν := SigmaFinite.of_map _ hg.aemeasurable hσ
  have h_ne_top1 : ∀ᵐ x ∂ν, (μ.map g).rnDeriv (ν.map g) (g x) ≠ ∞ :=
    ae_of_ae_map hg.aemeasurable (Measure.rnDeriv_ne_top (μ.map g) (ν.map g))
  have h_ne_top2 : ∀ᵐ x ∂ν, ν⁻[μ.rnDeriv ν|MeasurableSpace.comap g m𝓨] x ≠ ∞ := by
    refine condLExp_ne_top ?_
    simp [Measure.lintegral_rnDeriv hμν]
  have h_condExp := toReal_condLExp (m𝓨.comap g) (f := μ.rnDeriv ν) (μ := ν) (by fun_prop) ?_
  swap; · simp [Measure.lintegral_rnDeriv hμν]
  filter_upwards [toReal_rnDeriv_map hμν hg, h_condExp, h_ne_top1, h_ne_top2]
    with x hx h_condExp h_ne_top1 h_ne_top2
  rwa [← h_condExp, ENNReal.toReal_eq_toReal_iff' h_ne_top1 h_ne_top2] at hx

lemma rnDeriv_map_ae_eq_trim [IsFiniteMeasure μ] (hμν : μ ≪ ν)
    {g : 𝓧 → 𝓨} (hg : Measurable g) [SigmaFinite (ν.map g)] :
    (fun a ↦ (μ.map g).rnDeriv (ν.map g) (g a)) =ᵐ[ν.trim hg.comap_le]
      ν⁻[μ.rnDeriv ν | m𝓨.comap g] := by
  rw [StronglyMeasurable.ae_eq_trim_iff]
  · exact rnDeriv_map hμν hg
  · refine Measurable.stronglyMeasurable fun s hs ↦ ?_
    refine ⟨((μ.map g).rnDeriv (ν.map g)) ⁻¹' s, hs.preimage (by fun_prop), ?_⟩
    rw [← Set.preimage_comp]
    rfl
  · fun_prop

/-- The Radon-Nikodym derivative `∂(μ.map g)/∂(ν.map g)` of the pushforward of measures by
a function `g : 𝓧 → 𝓨` evaluated at `g x` is a.e.-equal to the conditional expectation of `∂μ/∂ν`
with respect to the comap by `g` of the sigma-algebra on `𝓨`.

See `toReal_rnDeriv_map` for the same statement, but with a.e. equality with respect to
the measure `ν`. -/
lemma toReal_rnDeriv_map_ae_eq_trim [IsFiniteMeasure μ] (hμν : μ ≪ ν)
    {g : 𝓧 → 𝓨} (hg : Measurable g) [SigmaFinite (ν.map g)] :
    (fun a ↦ ((μ.map g).rnDeriv (ν.map g) (g a)).toReal) =ᵐ[ν.trim hg.comap_le]
      ν[(fun a ↦ (μ.rnDeriv ν a).toReal) | m𝓨.comap g] := by
  rw [StronglyMeasurable.ae_eq_trim_iff]
  · exact toReal_rnDeriv_map hμν hg
  · refine Measurable.stronglyMeasurable fun s hs ↦ ?_
    refine ⟨(fun a ↦ ((μ.map g).rnDeriv (ν.map g) a).toReal) ⁻¹' s, hs.preimage (by fun_prop), ?_⟩
    rw [← Set.preimage_comp]
    rfl
  · fun_prop

/-- The Radon-Nikodym derivative `∂(μ.trim hm)/∂(ν.trim hm)` of the trimmed measures
(for `hm : m ≤ m0` stating that `m` is a sub-sigma-algebra of `m0`) is a.e.-equal to the
conditional expectation of `∂μ/∂ν` with respect to the sigma-algebra `m`. -/
lemma toReal_rnDeriv_trim (hm : m ≤ m𝓧) [IsFiniteMeasure μ] [hsf : SigmaFinite (ν.trim hm)]
    (hμν : μ ≪ ν) :
    (fun x ↦ ((μ.trim hm).rnDeriv (ν.trim hm) x).toReal) =ᵐ[ν.trim hm]
      ν[fun x ↦ (μ.rnDeriv ν x).toReal | m] := by
  simp_rw [trim_eq_map hm]
  have : SigmaFinite (ν.trim (measurable_id'' hm).comap_le) := by convert hsf; simp
  have : SigmaFinite (@Measure.map _ _ m𝓧 m id ν) := by rwa [← trim_eq_map hm]
  have h := toReal_rnDeriv_map_ae_eq_trim hμν (measurable_id'' hm)
  simp_rw [MeasurableSpace.comap_id, id_def, trim_eq_map] at h
  convert h <;> rw [MeasurableSpace.comap_id]

/-- The Radon-Nikodym derivative `∂(μ.trim hm)/∂(ν.trim hm)` of the trimmed measures
(for `hm : m ≤ m0` stating that `m` is a sub-sigma-algebra of `m0`) is a.e.-equal to the
conditional expectation of `∂μ/∂ν` with respect to the sigma-algebra `m`. -/
lemma rnDeriv_trim (hm : m ≤ m𝓧) [IsFiniteMeasure μ] [SigmaFinite (ν.trim hm)] (hμν : μ ≪ ν) :
    (μ.trim hm).rnDeriv (ν.trim hm)
      =ᵐ[ν.trim hm] fun x ↦ ENNReal.ofReal (ν[fun x ↦ (μ.rnDeriv ν x).toReal | m] x) := by
  filter_upwards [toReal_rnDeriv_trim hm hμν, Measure.rnDeriv_ne_top (μ.trim hm) (ν.trim hm)]
    with x hx hx_ne_top
  rw [← hx, ENNReal.ofReal_toReal hx_ne_top]

end MeasureTheory
