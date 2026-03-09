/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym
public import Mathlib.Probability.Kernel.Composition.MeasureComp

import Mathlib.Analysis.Convex.Deriv
import Mathlib.InformationTheory.KullbackLeibler.ChainRule

/-!
# Data processing inequality for the Kullback-Leibler divergence

## Main statements

*

-/

@[expose] public section

open Real MeasureTheory Set ProbabilityTheory

open scoped ENNReal

namespace InformationTheory

section FromCondJensenPR27953

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {α : Type*} {f : α → E} {φ : E → ℝ} {m mα : MeasurableSpace α} {μ : Measure α} {s : Set E}

theorem conditional_jensen (hm : m ≤ mα) [SigmaFinite (μ.trim hm)]
    (hφ_cvx : ConvexOn ℝ s φ) (hφ_cont : LowerSemicontinuousOn φ s) (hf : ∀ᵐ a ∂μ, f a ∈ s)
    (hs : IsClosed s) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    φ ∘ μ[f | m] ≤ᵐ[μ] μ[φ ∘ f | m] := by
  sorry

end FromCondJensenPR27953

section Aux

variable {α β : Type*} {m mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {f : ℝ → ℝ}

lemma f_condexp_rnDeriv_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hm : m ≤ mα)
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (h_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) :
    (fun x ↦ f ((ν[fun x ↦ (μ.rnDeriv ν x).toReal | m]) x))
      ≤ᵐ[ν.trim hm] ν[fun x ↦ f (μ.rnDeriv ν x).toReal | m] := by
  have h_ae := conditional_jensen hm hf_cvx hf_cont.lowerSemicontinuousOn
    (ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg) isClosed_Ici Measure.integrable_toReal_rnDeriv h_int
  rwa [StronglyMeasurable.ae_le_trim_iff]
  · fun_prop
  · fun_prop

end Aux

variable {𝓧 𝓨 : Type*} {m m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨} {μ ν : Measure 𝓧}

section ConvexFunction

variable {f : ℝ → ℝ}

lemma f_rnDeriv_map_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) {g : 𝓧 → 𝓨} (hg : Measurable g) (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (h_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) :
    (fun x ↦ f ((μ.map g).rnDeriv (ν.map g) (g x)).toReal)
      ≤ᵐ[ν] ν[fun x ↦ f (μ.rnDeriv ν x).toReal | m𝓨.comap g] := by
  filter_upwards [toReal_rnDeriv_map hμν hg,
    ae_of_ae_trim _ <| f_condexp_rnDeriv_le hg.comap_le hf hf_cvx hf_cont h_int] with a ha1 ha2
  calc f ((μ.map g).rnDeriv (ν.map g) (g a)).toReal
      = f ((ν[fun x ↦ (μ.rnDeriv ν x).toReal | m𝓨.comap g]) a) := by rw [ha1]
    _ ≤ (ν[fun x ↦ f (μ.rnDeriv ν x).toReal | m𝓨.comap g]) a := ha2

lemma integrable_f_rnDeriv_map [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) {g : 𝓧 → 𝓨} (hg : Measurable g) (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (h_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) :
    Integrable (fun x ↦ f ((μ.map g).rnDeriv (ν.map g) x).toReal) (ν.map g) := by
  obtain ⟨c, c', h⟩ : ∃ c c', ∀ x, 0 ≤ x → c * x + c' ≤ f x :=
    hf_cvx.exists_affine_le (convex_Ici 0)
  rw [integrable_map_measure _ hg.aemeasurable]
  swap
  · refine (hf.comp_measurable ?_).aestronglyMeasurable
    exact (Measure.measurable_rnDeriv _ _).ennreal_toReal
  refine integrable_of_le_of_le (f := fun x ↦ f ((∂μ.map g/∂ν.map g) (g x)).toReal)
    (g₁ := fun x ↦ c * ((∂μ.map g/∂ν.map g) (g x)).toReal + c')
    (g₂ := fun x ↦ (ν[fun x ↦ f (μ.rnDeriv ν x).toReal | m𝓨.comap g]) x)
    ?_ ?_ ?_ ?_ ?_
  · refine (hf.comp_measurable ?_).aestronglyMeasurable
    exact ((Measure.measurable_rnDeriv _ _).comp hg).ennreal_toReal
  · exact ae_of_all _ (fun x ↦ h _ ENNReal.toReal_nonneg)
  · exact f_rnDeriv_map_le hμν hg hf hf_cvx hf_cont h_int
  · refine (Integrable.const_mul ?_ _).add (integrable_const _)
    rw [integrable_congr (toReal_rnDeriv_map hμν hg)]
    exact integrable_condExp
  · exact integrable_condExp

lemma f_rnDeriv_trim_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hm : m ≤ m𝓧) (hμν : μ ≪ ν)
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (h_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) :
    (fun x ↦ f ((∂μ.trim hm/∂ν.trim hm) x).toReal)
      ≤ᵐ[ν.trim hm] ν[fun x ↦ f (μ.rnDeriv ν x).toReal | m] := by
  filter_upwards [toReal_rnDeriv_trim hm hμν,
    f_condexp_rnDeriv_le hm hf hf_cvx hf_cont h_int] with a ha1 ha2
  calc f ((∂μ.trim hm/∂ν.trim hm) a).toReal
      = f ((ν[fun x ↦ (μ.rnDeriv ν x).toReal | m]) a) := by rw [ha1]
    _ ≤ (ν[fun x ↦ f (μ.rnDeriv ν x).toReal | m]) a := ha2

lemma integrable_f_rnDeriv_trim [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hm : m ≤ m𝓧) (hμν : μ ≪ ν)
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (h_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) :
    Integrable (fun x ↦ f ((μ.trim hm).rnDeriv (ν.trim hm) x).toReal) (ν.trim hm) := by
  obtain ⟨c, c', h⟩ : ∃ c c', ∀ x, 0 ≤ x → c * x + c' ≤ f x :=
    hf_cvx.exists_affine_le (convex_Ici 0)
  refine integrable_of_le_of_le (f := fun x ↦ f ((∂μ.trim hm/∂ν.trim hm) x).toReal)
    (g₁ := fun x ↦ c * ((∂μ.trim hm/∂ν.trim hm) x).toReal + c')
    (g₂ := fun x ↦ (ν[fun x ↦ f (μ.rnDeriv ν x).toReal | m]) x)
    ?_ ?_ ?_ ?_ ?_
  · refine (hf.comp_measurable ?_).aestronglyMeasurable
    exact @Measurable.ennreal_toReal _ m _ (Measure.measurable_rnDeriv _ _)
  · exact ae_of_all _ (fun x ↦ h _ ENNReal.toReal_nonneg)
  · exact f_rnDeriv_trim_le hm hμν hf hf_cvx hf_cont h_int
  · refine (Integrable.const_mul ?_ _).add (integrable_const _)
    exact Measure.integrable_toReal_rnDeriv
  · exact integrable_condExp.trim hm stronglyMeasurable_condExp

lemma integrable_f_condexp_rnDeriv [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hm : m ≤ m𝓧) (hμν : μ ≪ ν)
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (h_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) :
    Integrable (fun x ↦ f ((ν[fun x ↦ (μ.rnDeriv ν x).toReal | m]) x)) ν := by
  have h := integrable_f_rnDeriv_trim hm hμν hf hf_cvx hf_cont h_int
  refine integrable_of_integrable_trim hm ((integrable_congr ?_).mp h)
  filter_upwards [toReal_rnDeriv_trim hm hμν] with a ha
  rw [ha]

end ConvexFunction

lemma integrable_llr_map [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) {g : 𝓧 → 𝓨} (hg : Measurable g) (h_int : Integrable (llr μ ν) μ) :
    Integrable (llr (μ.map g) (ν.map g)) (μ.map g) := by
  rw [← integrable_klFun_rnDeriv_iff (hμν.map hg)]
  refine integrable_f_rnDeriv_map hμν hg (by fun_prop) convexOn_klFun (by fun_prop) ?_
  rwa [integrable_klFun_rnDeriv_iff hμν]

lemma toReal_klDiv_map_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) {g : 𝓧 → 𝓨} (hg : Measurable g)
    (h_int : Integrable (llr μ ν) μ) :
    (klDiv (μ.map g) (ν.map g)).toReal =
      ∫ x, klFun ((ν[fun x ↦ (μ.rnDeriv ν x).toReal | m𝓨.comap g]) x) ∂ν := by
  classical
  have hf : StronglyMeasurable klFun := by fun_prop
  have hf_cvx : ConvexOn ℝ (Ici 0) klFun := convexOn_klFun
  have hf_cont : ContinuousOn klFun (Ici 0) := by fun_prop
  have h_int' : Integrable (fun x ↦ klFun (μ.rnDeriv ν x).toReal) ν := by
    rwa [integrable_klFun_rnDeriv_iff hμν]
  rw [toReal_klDiv_eq_integral_klFun (hμν.map hg), integral_map hg.aemeasurable]
  swap
  · refine (hf.comp_measurable ?_).aestronglyMeasurable
    exact (Measure.measurable_rnDeriv _ _).ennreal_toReal
  refine integral_congr_ae ?_
  filter_upwards [toReal_rnDeriv_map hμν hg] with a ha
  rw [ha]

lemma klDiv_map_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) {g : 𝓧 → 𝓨} (hg : Measurable g)
    (h_int : Integrable (llr μ ν) μ) :
    klDiv (μ.map g) (ν.map g) =
      ENNReal.ofReal (∫ x, klFun ((ν[fun x ↦ (μ.rnDeriv ν x).toReal | m𝓨.comap g]) x) ∂ν) := by
  rw [klDiv_eq_integral_klFun, if_pos ⟨hμν.map hg, integrable_llr_map hμν hg h_int⟩]
  congr
  rw [← toReal_klDiv_eq_integral_klFun (hμν.map hg), toReal_klDiv_map_of_ac hμν hg h_int]

lemma toReal_klDiv_trim_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hm : m ≤ m𝓧) (hμν : μ ≪ ν)
    (h_int : Integrable (llr μ ν) μ) :
    (klDiv (μ.trim hm) (ν.trim hm)).toReal =
      ∫ x, klFun ((ν[fun x ↦ (μ.rnDeriv ν x).toReal | m]) x) ∂ν := by
  simp_rw [trim_eq_map]
  rw [toReal_klDiv_map_of_ac hμν (measurable_id'' hm) h_int]
  congr with x
  congr
  simp

/-- **Data processing inequality** for the Kullback-Leibler divergence and measurable functions. -/
theorem klDiv_map_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {g : 𝓧 → 𝓨} (hg : Measurable g) :
    klDiv (μ.map g) (ν.map g) ≤ klDiv μ ν := by
  by_cases hμν : μ ≪ ν
  swap; · simp [hμν]
  by_cases h_int : Integrable (llr μ ν) μ
  swap; · simp [klDiv_of_not_integrable h_int]
  rw [klDiv_map_of_ac hμν hg h_int, klDiv_eq_integral_klFun]
  simp only [hμν, h_int, and_self, ↓reduceIte]
  conv_rhs => rw [← integral_condExp hg.comap_le]
  gcongr 1
  have hf : StronglyMeasurable klFun := by fun_prop
  have hf_cvx : ConvexOn ℝ (Ici 0) klFun := convexOn_klFun
  have hf_cont : ContinuousOn klFun (Ici 0) := by fun_prop
  have h_int' : Integrable (fun x ↦ klFun (μ.rnDeriv ν x).toReal) ν := by
    rwa [integrable_klFun_rnDeriv_iff hμν]
  refine integral_mono_ae ?_ integrable_condExp ?_
  · exact integrable_f_condexp_rnDeriv hg.comap_le hμν hf hf_cvx hf_cont h_int'
  · refine ae_of_ae_trim hg.comap_le ?_
    exact f_condexp_rnDeriv_le hg.comap_le hf hf_cvx hf_cont h_int'

/-- **Data processing inequality** for the Kullback-Leibler divergence and sub-sigma-algebras. -/
theorem klDiv_trim_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hm : m ≤ m𝓧) :
    klDiv (μ.trim hm) (ν.trim hm) ≤ klDiv μ ν := by
  simp_rw [trim_eq_map]
  exact klDiv_map_le (measurable_id'' hm)

lemma klDiv_comp_le_compProd_right (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel 𝓧 𝓨) [IsFiniteKernel κ] :
    klDiv (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ klDiv (μ ⊗ₘ κ) (ν ⊗ₘ κ) := by
  simp_rw [← Measure.snd_compProd]
  exact klDiv_map_le measurable_snd

/-- The **Data Processing Inequality** for the Kullback-Leibler divergence. -/
theorem klDiv_comp_right_le (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ] :
    klDiv (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ klDiv μ ν :=
  (klDiv_comp_le_compProd_right μ ν κ).trans_eq (klDiv_compProd_left μ ν κ)

end InformationTheory
