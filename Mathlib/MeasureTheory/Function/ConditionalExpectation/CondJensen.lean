/-
Copyright (c) 2025 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin, Thomas Zhu
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Conditional Jensen's Inequality

This file contains the conditional Jensen's inequality.

## Main Statement

* `conditional_jensen`: the conditional Jensen's inequality: in a Banach space `X` with finite
  measure `μ`, if `φ : X → ℝ` is a convex lower-semicontinuous function, then for any `f : α → X`
  such that `f` and `φ ∘ f` are integrable, we have `φ (𝔼[f | m]) ≤ 𝔼[φ ∘ f | m]`.

## References

* [Hytönen, Tuomas, Jan Van Neerven, Mark Veraar, and Lutz Weis. Analysis in Banach spaces.
  Springer, 2016.][Hytonen_VanNeerven_Veraar_Wies_2016]
-/

open MeasureTheory ProbabilityTheory TopologicalSpace Set Metric ContinuousLinearMap RCLike
open scoped ENNReal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {φ : E → ℝ}
variable [CompleteSpace E] {α : Type*} {f : α → E}
variable {m mα : MeasurableSpace α} {μ : Measure α} [IsFiniteMeasure μ]

/-- Conditional Jensen for separable spaces. -/
private lemma conditional_jensen_of_separableSpace [SecondCountableTopology E]
    (hm : m ≤ mα) (hφ_cvx : ConvexOn ℝ Set.univ φ) (hφ_cont : LowerSemicontinuous φ)
    (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    ∀ᵐ a ∂μ, φ (μ[f | m] a) ≤ μ[φ ∘ f | m] a := by
  rcases hφ_cvx.iSup_affine_eq_of_separableSpace (K := ℝ) hφ_cont with ⟨L, c, hp⟩
  have py : ∀ᵐ a ∂μ, ∀ i : ℕ, re (L i (μ[f | m] a)) + c i
    = μ[re ∘ (L i) ∘ f + (fun (b : α) ↦ (c i)) | m] a := by
    rw [ae_all_iff]; intro i; apply condExp_comm_affine hm hf_int (L i) (c i)
  have pz : ∀ᵐ a ∂μ, ∀ i : ℕ, (re ∘ (L i) ∘ f + (fun (b : α) ↦ (c i))) a ≤ (φ ∘ f) a := by
    rw [ae_all_iff]; intro i; filter_upwards with a
    rw [Function.comp_apply, ← (hp (f a)).2, Pi.add_apply, Function.comp_apply, Function.comp_apply]
    apply le_ciSup (hp (f a)).1 i
  have pw : ∀ᵐ a ∂μ, ∀ i : ℕ, μ[(re ∘ (L i) ∘ f + (fun (b : α) ↦ (c i))) | m] a
    ≤ μ[φ ∘ f | m] a := by
    rw [ae_all_iff]; intro i; apply condExp_mono
    · let g := @reCLM ℝ (by infer_instance)
      have reLif_int : Integrable (fun (a : α) ↦ (re ∘ (L i)) (f a)) μ
        := integrable_comp (comp g (L i)) hf_int
      exact Integrable.add reLif_int (integrable_const (c i))
    · exact hφ_int
    · exact ae_all_iff.mp pz i
  filter_upwards [py, pw] with a
  intro hy hw
  rw [← (hp (μ[f | m] a)).right]
  apply ciSup_le
  intro i
  rw [hy i]
  apply hw i

/-- Conditional Jensen's inequality.
# TODO

Generalize this theorem to σ-finite measures.
-/
theorem conditional_jensen (hm : m ≤ mα)
    (hφ_cvx : ConvexOn ℝ Set.univ φ) (hφ_cont : LowerSemicontinuous φ)
    (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    φ ∘ μ[f | m] ≤ᵐ[μ] μ[φ ∘ f | m] := by
  classical
  borelize E
  have sep := hf_int.aestronglyMeasurable.isSeparable_ae_range
  rcases sep with ⟨t, ht, htt⟩
  let Y := (Submodule.span ℝ t).topologicalClosure
  have : CompleteSpace Y := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have : SecondCountableTopology Y := ht.span.closure.secondCountableTopology
  let φY := φ ∘ Y.subtypeL
  have hφY_cvx : ConvexOn ℝ Set.univ φY := hφ_cvx.comp_linearMap Y.subtype
  have hφY_cont : LowerSemicontinuous φY := hφ_cont.comp_continuous Y.subtypeL.cont
  have tsubY : t ⊆ Y := subset_trans Submodule.subset_span subset_closure
  have aeinY : ∀ᵐ (x : α) ∂μ, f x ∈ Y := by filter_upwards [htt] with a ha; exact tsubY ha
  let fY : α → Y := fun a => if h : f a ∈ Y then ⟨f a, h⟩ else 0
  let fX : α → E := Y.subtypeL ∘ fY
  have lem1 : f =ᵐ[μ] fX := by filter_upwards [aeinY] with a ha; simp [fX, fY, ha, reduceDIte]
  have hfX_int : Integrable fX μ := Integrable.congr hf_int lem1
  have hfY_int : Integrable fY μ := by
    constructor
    · have hs : MeasurableSet (Y : Set E) :=
        (Submodule.isClosed_topologicalClosure _).measurableSet
      have h_nonempty : (Y : Set E).Nonempty := Set.Nonempty.of_subtype
      obtain ⟨g, hg1, hg2 : ∀ x, g x ∈ Y, hg3⟩ :=
        hf_int.1.exists_stronglyMeasurable_range_subset hs h_nonempty aeinY
      use codRestrict g Y hg2
      constructor
      · rw [stronglyMeasurable_iff_measurable]
        exact hg1.measurable.codRestrict hg2
      · filter_upwards [hg3] with a ha1
        simp [fY, ha1, Set.codRestrict, dif_pos (hg2 a)]
    · apply hfX_int.2.mono
      simp [fX, Function.comp_apply, le_refl, Filter.eventually_true]
  have lem3 : μ[f | m] =ᵐ[μ] Y.subtypeL ∘ μ[fY | m] :=
    calc
      μ[f | m] =ᵐ[μ] μ[fX | m] := condExp_congr_ae lem1
      _        =ᵐ[μ] Y.subtypeL ∘ μ[fY | m] :=
        (condExp_comm_continuousLinearMap hm hfY_int Y.subtypeL).symm
  have lem2 : φ ∘ f =ᵐ[μ] φY ∘ fY := by filter_upwards [lem1] with a ha; simp [φY, ha, fX]
  have hφYfY_int : Integrable (φY ∘ fY) μ := hφ_int.congr lem2
  calc
    φ ∘ μ[f | m]
      =ᵐ[μ] φY ∘ μ[fY | m] := by filter_upwards [lem3] with a ha; simp [φY, ha]
    _ ≤ᵐ[μ] μ[φY ∘ fY | m] :=
      conditional_jensen_of_separableSpace hm hφY_cvx hφY_cont hfY_int hφYfY_int
    _ =ᵐ[μ] μ[φ ∘ f | m] := condExp_congr_ae lem2.symm
