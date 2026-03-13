/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin, Thomas Zhu
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

import Mathlib.Analysis.Convex.Approximation
import Mathlib.Analysis.Convex.Continuous

/-!
# Conditional Jensen's Inequality

This file contains the conditional Jensen's inequality. We follow the proof in
[Hytonen_VanNeerven_Veraar_Wies_2016].

## Main Statement

* `condExp_mem_convex`: in a Banach space `E` with a finite measure `μ`, if `f` lies in a
  closed convex set `s` a.e., then `μ[f | m]` lies in `s` a.e.
* `conditional_jensen_univ`: in a Banach space `E` with a sigma finite measure `μ`, if `φ : E → ℝ`
  is a convex lower-semicontinuous function, then for any `f : α → E` such that `f` and `φ ∘ f` are
  integrable, we have `φ (𝔼[f | m]) ≤ 𝔼[φ ∘ f | m]` a.e.

-/

public section

open MeasureTheory Function Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {α : Type*} {f : α → E} {φ : E → ℝ} {m mα : MeasurableSpace α} {μ : Measure α} {s : Set E}

/-- If `f` lies in a closed convex set `s` a.e., then `μ[f | m]` lies in `s` a.e. -/
lemma Convex.condExp_mem [IsFiniteMeasure μ] [HereditarilyLindelofSpace E] (hm : m ≤ mα)
    (hf_int : Integrable f μ) (hs : IsClosed s) (hc : Convex ℝ s) (hf : ∀ᵐ a ∂μ, f a ∈ s) :
    ∀ᵐ a ∂μ, μ[f | m] a ∈ s := by
  obtain ⟨L, c, hLc⟩ := RCLike.iInter_countable_halfSpaces_eq (𝕜 := ℝ) hc hs
  simp_all only [← hLc, RCLike.re_to_real, mem_iInter, ae_all_iff]
  intro n
  have h1 := ContinuousLinearMap.comp_condExp_comm (m := m) hf_int (L n)
  have h2 := condExp_mono (m := m) ((L n).integrable_comp hf_int) (integrable_const (c n)) (hf n)
  filter_upwards [h1, h2] with a ha hb
  simp_all only [condExp_const, comp_apply]
  exact hb

/-- Conditional Jensen's inequality for hereditarily Lindelof Spaces. -/
private lemma ConvexOn.map_condExp_le_hereditarilyLindelof [IsFiniteMeasure μ]
    [HereditarilyLindelofSpace E] (hm : m ≤ mα) (hφ_cvx : ConvexOn ℝ s φ)
    (hφ_cont : LowerSemicontinuousOn φ s) (hf : ∀ᵐ a ∂μ, f a ∈ s) (hs : IsClosed s)
    (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    ∀ᵐ a ∂μ, φ (μ[f | m] a) ≤ μ[φ ∘ f | m] a := by
  obtain ⟨L, c, hLc1, hLc2⟩ := hφ_cvx.real_sSup_of_nat_affine_eq hs hφ_cont
  have hp := ae_all_iff.2 fun i => (L i).comp_condExp_add_const_comm hm hf_int (c i)
  have hw : ∀ᵐ a ∂μ, ∀ i : ℕ, μ[(L i) ∘ f + const α (c i) | m] a ≤ μ[φ ∘ f | m] a := by
    refine ae_all_iff.2 fun i => condExp_mono ?_ hφ_int ?_
    · exact ((L i).integrable_comp hf_int).add (integrable_const (c i))
    · filter_upwards [hf] with a ha using hLc1 i ⟨f a, ha⟩
  filter_upwards [hp, hw, hφ_cvx.1.condExp_mem hm hf_int hs hf] with a hp hw hq
  rw [show φ (μ[f | m] a) = s.restrict φ ⟨μ[f | m] a, hq⟩ by simp, ← hLc2]
  simpa [iSup_congr hp] using ciSup_le hw

set_option backward.isDefEq.respectTransparency false
/-- Conditional Jensen's inequality for finite measures. -/
private theorem ConvexOn.map_condExp_le_finiteMeasure [IsFiniteMeasure μ] (hm : m ≤ mα)
    (hφ_cvx : ConvexOn ℝ s φ) (hφ_cont : LowerSemicontinuousOn φ s) (hf : ∀ᵐ a ∂μ, f a ∈ s)
    (hs : IsClosed s) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    φ ∘ μ[f | m] ≤ᵐ[μ] μ[φ ∘ f | m] := by
  borelize E
  obtain ⟨t, ht, htt⟩ := hf_int.aestronglyMeasurable.isSeparable_ae_range
  let Y := (Submodule.span ℝ t).topologicalClosure
  have : CompleteSpace Y := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have : SecondCountableTopology Y := ht.span.closure.secondCountableTopology
  let φY := φ ∘ Y.subtypeL
  classical
  let fY : α → Y := fun a => if h : f a ∈ Y then ⟨f a, h⟩ else 0
  let fX : α → E := Y.subtypeL ∘ fY
  have lem0 : ∀ᵐ a ∂μ, f a ∈ Y := by
    filter_upwards [htt] with a ha using
      (Submodule.closure_subset_topologicalClosure_span t) (subset_closure ha)
  have lem1 : f =ᵐ[μ] fX := by
    filter_upwards [lem0] with a ha
    simp_all [fX, fY]
  have hfY_int : Integrable fY μ := by
    refine (hf_int.congr lem1).mono ?_ (by simp [fX])
    obtain ⟨g, hg1, hg2, hg3⟩ := hf_int.1.exists_stronglyMeasurable_range_subset
      ((Submodule.isClosed_topologicalClosure _).measurableSet) Nonempty.of_subtype lem0
    refine ⟨codRestrict g Y hg2, (hg1.measurable.codRestrict hg2).stronglyMeasurable, ?_⟩
    filter_upwards [hg3] with a ha
    have : g a ∈ Y := hg2 a
    simp_all [fY, codRestrict]
  have lem2 : μ[f | m] =ᵐ[μ] Y.subtypeL ∘ μ[fY | m] := calc
    _ =ᵐ[μ] μ[fX | m] := condExp_congr_ae lem1
    _ =ᵐ[μ] _ := (Y.subtypeL.comp_condExp_comm hfY_int).symm
  have lem3 : φ ∘ f =ᵐ[μ] φY ∘ fY := by filter_upwards [lem1] with a ha; simp [φY, ha, fX]
  calc
    φ ∘ μ[f | m]
      =ᵐ[μ] φY ∘ μ[fY | m] := by filter_upwards [lem2] with a ha; simp [φY, ha]
    _ ≤ᵐ[μ] μ[φY ∘ fY | m] := by
      refine (hφ_cvx.comp_linearMap Y.subtype).map_condExp_le_hereditarilyLindelof
        (s := Y.subtypeL ⁻¹' s) hm ?_ ?_ ?_ hfY_int (Integrable.congr hφ_int lem3)
      · exact hφ_cont.comp (by fun_prop) fun x => by grind
      · filter_upwards [lem0, hf] with a ha hb
        simp_all [fY]
      · exact hs.preimage Y.subtypeL.continuous
    _ =ᵐ[μ] μ[φ ∘ f | m] := condExp_congr_ae lem3.symm

/-- **Conditional Jensen's inequality**: in a Banach space `X` with a measure `μ` that is σ-finite
on a sub-σ-algebra `m`, if `φ : X → ℝ` is convex and lower-semicontinuous on a closed set `s`, then
for any `f : α → X` such that `f` and `φ ∘ f` are integrable, and `f` lies in `s` a.e., we have
`φ (𝔼[f | m]) ≤ᵐ[μ] 𝔼[φ ∘ f | m]`. -/
theorem ConvexOn.map_condExp_le (hm : m ≤ mα) [SigmaFinite (μ.trim hm)]
    (hφ_cvx : ConvexOn ℝ s φ) (hφ_cont : LowerSemicontinuousOn φ s) (hf : ∀ᵐ a ∂μ, f a ∈ s)
    (hs : IsClosed s) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    φ ∘ μ[f | m] ≤ᵐ[μ] μ[φ ∘ f | m] := by
  refine (forall_measure_restrict_finiteSpanningSetsIn_eq_zero μ.toFiniteSpanningSetsIn ?_).1
  · sorry
  intro n
  have h1 := condExp_restrict_ae_eq_restrict hm (measurableSet_spanningSets (μ.trim hm) n) hf_int
  have h2 := condExp_restrict_ae_eq_restrict hm (measurableSet_spanningSets (μ.trim hm) n) hφ_int
  have : IsFiniteMeasure (μ.restrict (spanningSets (μ.trim hm) n)) := isFiniteMeasure_restrict.2
    ((le_trim hm).trans_lt (measure_spanningSets_lt_top (μ.trim hm) n)).ne
  have h3 := hφ_cvx.map_condExp_le_finiteMeasure (μ := μ.restrict (spanningSets (μ.trim hm) n)) hm
    hφ_cont (ae_restrict_of_ae hf) hs hf_int.restrict hφ_int.restrict
  filter_upwards [h1, h2, h3] with a ha hb hc
  simpa [← ha, ← hb]

theorem ConcaveOn.condExp_map_le (hm : m ≤ mα) [SigmaFinite (μ.trim hm)]
    (hφ_cvx : ConcaveOn ℝ s φ) (hφ_cont : UpperSemicontinuousOn φ s) (hf : ∀ᵐ a ∂μ, f a ∈ s)
    (hs : IsClosed s) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    μ[φ ∘ f | m] ≤ᵐ[μ] φ ∘ μ[f | m] := by
  filter_upwards [hφ_cvx.neg.map_condExp_le hm hφ_cont.neg hf hs hf_int hφ_int.neg,
    condExp_neg (φ ∘ f) m] with a h ha
  simp_all [Pi.neg_comp]

/-- **Conditional Jensen's inequality**: in a Banach space `X` with a measure `μ` that is σ-finite
on a sub-σ-algebra `m`, if `φ : X → ℝ` is convex and lower-semicontinuous, then for any `f : α → X`
such that `f` and `φ ∘ f` are integrable, we have `φ (𝔼[f | m]) ≤ᵐ[μ] 𝔼[φ ∘ f | m]`. -/
theorem ConvexOn.map_condExp_le_univ (hm : m ≤ mα) [SigmaFinite (μ.trim hm)]
    (hφ_cvx : ConvexOn ℝ univ φ) (hφ_cont : LowerSemicontinuous φ)
    (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    φ ∘ μ[f | m] ≤ᵐ[μ] μ[φ ∘ f | m] :=
  ConvexOn.map_condExp_le hm hφ_cvx (lowerSemicontinuousOn_univ_iff.2 hφ_cont) (by simp)
    isClosed_univ hf_int hφ_int

theorem ConcaveOn.condExp_map_le_univ (hm : m ≤ mα) [SigmaFinite (μ.trim hm)]
    (hφ_cvx : ConcaveOn ℝ univ φ) (hφ_cont : UpperSemicontinuous φ)
    (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    μ[φ ∘ f | m] ≤ᵐ[μ] φ ∘ μ[f | m] := by
  filter_upwards [hφ_cvx.neg.map_condExp_le_univ hm hφ_cont.neg hf_int hφ_int.neg,
    condExp_neg (φ ∘ f) m] with a h ha
  simp_all [Pi.neg_comp]

/-- In a Banach space `X` with a measure `μ`, then for any `μ`-a.e. strongly measurable function
`f : α → X`, we have `‖𝔼[f | m])‖ ≤ᵐ[μ] 𝔼[‖f‖ | m]`. -/
theorem AEStronglyMeasurable.norm_condExp_le (hf : AEStronglyMeasurable f μ) :
    (‖μ[f | m] ·‖) ≤ᵐ[μ] μ[(‖f ·‖) | m] := by
  by_cases! hm : ¬ m ≤ mα
  · simp_all [condExp_of_not_le hm]; aesop
  by_cases! hμm : ¬ SigmaFinite (μ.trim hm)
  · simp [condExp_of_not_sigmaFinite hm hμm]; aesop
  by_cases! hf_int : ¬ Integrable f μ
  · have : ¬ Integrable (‖f ·‖) μ := by simpa [integrable_norm_iff hf]
    simp [condExp_of_not_integrable hf_int, condExp_of_not_integrable this]
    aesop
  exact convexOn_univ_norm.map_condExp_le_univ hm continuous_norm.lowerSemicontinuous hf_int
    hf_int.norm

/-- **Conditional Jensen's inequality**: in a finite dimensional Banach space `X` with a measure
`μ` that is σ-finite on a sub-σ-algebra `m`, if `φ : X → ℝ` is convex, then for any `f : α → X` such
that `f` and `φ ∘ f` are integrable, we have `φ (𝔼[f | m]) ≤ᵐ[μ] 𝔼[φ ∘ f | m]`. -/
theorem ConvexOn.map_condExp_le_finiteDimensional [FiniteDimensional ℝ E] (hm : m ≤ mα)
    [SigmaFinite (μ.trim hm)] (hφ_cvx : ConvexOn ℝ univ φ) (hf_int : Integrable f μ)
    (hφ_int : Integrable (φ ∘ f) μ) :
    φ ∘ μ[f | m] ≤ᵐ[μ] μ[φ ∘ f | m] :=
  hφ_cvx.map_condExp_le_univ hm
    (continuousOn_univ.1 (hφ_cvx.continuousOn isOpen_univ)).lowerSemicontinuous hf_int hφ_int

theorem ConcaveOn.condExp_map_le_finiteDimensional [FiniteDimensional ℝ E] (hm : m ≤ mα)
    [SigmaFinite (μ.trim hm)] (hφ_cvx : ConcaveOn ℝ univ φ) (hf_int : Integrable f μ)
    (hφ_int : Integrable (φ ∘ f) μ) :
    μ[φ ∘ f | m] ≤ᵐ[μ] φ ∘ μ[f | m] := by
  filter_upwards [hφ_cvx.neg.map_condExp_le_finiteDimensional hm hf_int hφ_int.neg,
    condExp_neg (φ ∘ f) m] with a h ha
  simp_all [Pi.neg_comp]
