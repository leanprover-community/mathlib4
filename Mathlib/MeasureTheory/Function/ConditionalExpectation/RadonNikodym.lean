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
import Mathlib.MeasureTheory.Function.ConditionalExpectation.LebesgueBochner

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

/-- The Radon-Nikodym derivative `∂(μ.map g)/∂(ν.map g)` of the pushforward of measures by
a function `g : 𝓧 → 𝓨` evaluated at `g x` is a.e.-equal to the conditional expectation of `∂μ/∂ν`
with respect to the comap by `g` of the sigma-algebra on `𝓨`.

See `rnDeriv_map_ae_eq_trim` for the same statement, but with a.e. equality with respect to
the trimmed measure `ν.trim hg.comap_le`. -/
lemma rnDeriv_map [IsFiniteMeasure μ] (hμν : μ ≪ ν)
    {g : 𝓧 → 𝓨} (hg : Measurable g) [hσ : SigmaFinite (ν.map g)] :
    (fun a ↦ (μ.map g).rnDeriv (ν.map g) (g a)) =ᵐ[ν] ν⁻[μ.rnDeriv ν | m𝓨.comap g] := by
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

/-- The Radon-Nikodym derivative `∂(μ.map g)/∂(ν.map g)` of the pushforward of measures by
a function `g : 𝓧 → 𝓨` evaluated at `g x` is a.e.-equal to the conditional expectation of `∂μ/∂ν`
with respect to the comap by `g` of the sigma-algebra on `𝓨`.

See `rnDeriv_map` for the same statement, but with a.e. equality with respect to the measure `ν`. -/
lemma rnDeriv_map_ae_eq_trim [IsFiniteMeasure μ] (hμν : μ ≪ ν)
    {g : 𝓧 → 𝓨} (hg : Measurable g) [SigmaFinite (ν.map g)] :
    (fun a ↦ (μ.map g).rnDeriv (ν.map g) (g a)) =ᵐ[ν.trim hg.comap_le]
      ν⁻[μ.rnDeriv ν | m𝓨.comap g] := by
  rw [StronglyMeasurable.ae_eq_trim_iff]
  · exact rnDeriv_map hμν hg
  · refine Measurable.stronglyMeasurable fun s hs ↦ ?_
    exact ⟨((μ.map g).rnDeriv (ν.map g)) ⁻¹' s, hs.preimage (by fun_prop), by grind⟩
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
