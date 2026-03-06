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

@[expose] public section

open MeasureTheory Function Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {α : Type*} {f : α → E} {φ : E → ℝ} {m mα : MeasurableSpace α} {μ : Measure α} {s : Set E}

/-- If `f` lies in a closed convex set `s` a.e., then `μ[f | m]` lies in `s` a.e.
#TODO: Generalize this theorem. -/
lemma condExp_mem_convex [IsFiniteMeasure μ] [HereditarilyLindelofSpace E] (hm : m ≤ mα)
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
private lemma conditional_jensen_of_hereditarilyLindelofSpace [IsFiniteMeasure μ]
    [HereditarilyLindelofSpace E] (hm : m ≤ mα) (hφ_cvx : ConvexOn ℝ s φ)
    (hφ_cont : LowerSemicontinuousOn φ s) (hf : ∀ᵐ a ∂μ, f a ∈ s) (hs : IsClosed s)
    (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    ∀ᵐ a ∂μ, φ (μ[f | m] a) ≤ μ[φ ∘ f | m] a := by
  obtain ⟨L, c, hLc⟩ := hφ_cvx.real_sSup_of_nat_affine_eq hs hφ_cont
  have hp := ae_all_iff.2 fun i => (L i).comp_condExp_add_const_comm hm hf_int (c i)
  have hw : ∀ᵐ a ∂μ, ∀ i : ℕ, μ[(L i) ∘ f + const α (c i) | m] a ≤ μ[φ ∘ f | m] a := by
    refine ae_all_iff.2 fun i => condExp_mono ?_ hφ_int ?_
    · exact ((L i).integrable_comp hf_int).add (integrable_const (c i))
    · filter_upwards [hf] with a ha
      have := congrFun hLc.2 ⟨f a, ha⟩
      simp_all only [iSup_apply, Pi.add_apply, restrict_apply, const_apply, comp_apply, ge_iff_le]
      rw [← this]
      exact le_ciSup (bddAbove_def.2 ⟨φ (f a), fun r ⟨z, hz⟩ => hz ▸ hLc.1 z ⟨f a, ha⟩⟩) i
  filter_upwards [hp, hw, condExp_mem_convex hm hf_int hs hφ_cvx.1 hf] with a hp hw hq
  rw [show φ (μ[f | m] a) = s.restrict φ ⟨μ[f | m] a, hq⟩ from by simp, ← hLc.2]
  simpa [iSup_congr hp] using ciSup_le hw

/-- Conditional Jensen's inequality for finite measures. -/
private theorem conditional_jensen_of_finiteMeasure [IsFiniteMeasure μ] (hm : m ≤ mα)
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
    filter_upwards [htt] with a ha
    exact (Submodule.closure_subset_topologicalClosure_span (R := ℝ) t) (subset_closure ha)
  have lem1 : f =ᵐ[μ] fX := by
    filter_upwards [lem0] with a ha
    simp_all [fX, fY]
  have hfX_int : Integrable fX μ := Integrable.congr hf_int lem1
  have hfY_int : Integrable fY μ := by
    refine ⟨?_, hfX_int.2.mono (by simp [fX])⟩
    have hs : MeasurableSet (Y : Set E) := (Submodule.isClosed_topologicalClosure _).measurableSet
    have h_nonempty : (Y : Set E).Nonempty := Set.Nonempty.of_subtype
    obtain ⟨g, hg1, hg2, hg3⟩ := hf_int.1.exists_stronglyMeasurable_range_subset hs h_nonempty lem0
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
      refine conditional_jensen_of_hereditarilyLindelofSpace
        (s := Y.subtypeL ⁻¹' s) hm ?_ ?_ ?_ ?_ hfY_int (Integrable.congr hφ_int lem3)
      · exact hφ_cvx.comp_linearMap Y.subtype
      · exact hφ_cont.comp (by fun_prop) fun x => by grind
      · filter_upwards [lem0, hf] with a ha hb
        simp_all [fY]
      · exact hs.preimage Y.subtypeL.continuous
    _ =ᵐ[μ] μ[φ ∘ f | m] := condExp_congr_ae lem3.symm

/-- **Conditional Jensen's inequality**: in a Banach space `X` with a measure `μ` that is σ-finite
on a sub-σ-algebra `m`, if `φ : X → ℝ` is convex and lower-semicontinuous on a closed set `s`, then
for any `f : α → X` such that `f` and `φ ∘ f` are integrable, and `f` lies in `s` a.e., we have
`φ (𝔼[f | m]) ≤ᵐ[μ] 𝔼[φ ∘ f | m]`. -/
theorem conditional_jensen (hm : m ≤ mα) [SigmaFinite (μ.trim hm)]
    (hφ_cvx : ConvexOn ℝ s φ) (hφ_cont : LowerSemicontinuousOn φ s) (hf : ∀ᵐ a ∂μ, f a ∈ s)
    (hs : IsClosed s) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    φ ∘ μ[f | m] ≤ᵐ[μ] μ[φ ∘ f | m] := by
  rw [EventuallyLE]
  refine forall_measure_restrict_spanningSets_trim_eq_zero hm fun n => ?_
  have ht := measurableSet_spanningSets (μ.trim hm) n
  have ht' := measure_spanningSets_lt_top (μ.trim hm) n
  have h1 := condExp_restrict_ae_eq_restrict hm ht hf_int
  have h2 := condExp_restrict_ae_eq_restrict hm ht hφ_int
  have : Fact (μ (spanningSets (μ.trim hm) n) < ⊤) := fact_iff.2 <| (le_trim hm).trans_lt ht'
  have h3 := conditional_jensen_of_finiteMeasure (μ := μ.restrict (spanningSets (μ.trim hm) n)) hm
    hφ_cvx hφ_cont (ae_restrict_of_ae hf) hs hf_int.restrict hφ_int.restrict
  borelize E
  filter_upwards [h1, h2, h3] with a ha hb hc
  simpa [← ha, ← hb]

/-- **Conditional Jensen's inequality**: in a Banach space `X` with a measure `μ` that is σ-finite
on a sub-σ-algebra `m`, if `φ : X → ℝ` is convex and lower-semicontinuous, then for any `f : α → X`
such that `f` and `φ ∘ f` are integrable, we have `φ (𝔼[f | m]) ≤ᵐ[μ] 𝔼[φ ∘ f | m]`. -/
theorem conditional_jensen_univ (hm : m ≤ mα) [SigmaFinite (μ.trim hm)]
    (hφ_cvx : ConvexOn ℝ univ φ) (hφ_cont : LowerSemicontinuous φ)
    (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    φ ∘ μ[f | m] ≤ᵐ[μ] μ[φ ∘ f | m] :=
  conditional_jensen hm hφ_cvx (lowerSemicontinuousOn_univ_iff.2 hφ_cont) (by simp)
    isClosed_univ hf_int hφ_int

/-- **Conditional Jensen's inequality**: in a Banach space `X` with a measure `μ`, then for any
`μ`-a.e. strongly measurable function `f : α → X`, we have `‖𝔼[f | m])‖ ≤ᵐ[μ] 𝔼[‖f‖ | m]`. -/
theorem conditional_jensen_norm (hf : AEStronglyMeasurable f μ) :
    (‖μ[f | m] ·‖) ≤ᵐ[μ] μ[(‖f ·‖) | m] := by
  by_cases! hm : ¬ m ≤ mα
  · simp_all [condExp_of_not_le hm]; aesop
  by_cases! hμm : ¬ SigmaFinite (μ.trim hm)
  · simp [condExp_of_not_sigmaFinite hm hμm]; aesop
  by_cases! hf_int : ¬ Integrable f μ
  · have : ¬ Integrable (‖f ·‖) μ := by simpa [integrable_norm_iff hf]
    simp [condExp_of_not_integrable hf_int, condExp_of_not_integrable this]
    aesop
  exact conditional_jensen_univ hm convexOn_univ_norm continuous_norm.lowerSemicontinuous hf_int
    hf_int.norm

/-- **Conditional Jensen's inequality**: in a finite dimensional Banach space `X` with a measure
`μ` that is σ-finite on a sub-σ-algebra `m`, if `φ : X → ℝ` is convex, then for any `f : α → X` such
that `f` and `φ ∘ f` are integrable, we have `φ (𝔼[f | m]) ≤ᵐ[μ] 𝔼[φ ∘ f | m]`. -/
theorem conditional_jensen_univ_finite_dim [FiniteDimensional ℝ E] (hm : m ≤ mα)
    [SigmaFinite (μ.trim hm)] (hφ_cvx : ConvexOn ℝ univ φ) (hf_int : Integrable f μ)
    (hφ_int : Integrable (φ ∘ f) μ) :
    φ ∘ μ[f | m] ≤ᵐ[μ] μ[φ ∘ f | m] :=
  conditional_jensen_univ hm hφ_cvx
    (continuousOn_univ.1 (hφ_cvx.continuousOn isOpen_univ)).lowerSemicontinuous hf_int hφ_int
