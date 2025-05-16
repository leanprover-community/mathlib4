/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Integrals and the continuous functional calculus

This file gives results about integrals of the form `∫ x, cfc (f x) a`. Most notably, we show
that the integral commutes with the continuous functional calculus under appropriate conditions.

## Main declarations

+ `cfc_setIntegral` (resp. `cfc_integral`): given a function `f : X → 𝕜 → 𝕜`, we have that
  `cfc (fun r => ∫ x in s, f x r ∂μ) a = ∫ x in s, cfc (f x) a ∂μ`
  under appropriate conditions (resp. with `s = univ`)
+ `cfcₙ_integral`: the same for the non-unital continuous functional calculus
+ `integrable_cfc_set`, `integrable_cfcₙ_set`, `integrable_cfc`, `integrable_cfcₙ`:
  functions of the form `fun x => cfc (f x) a` are integrable.

## TODO

+ Lift this to the case where the CFC is over `ℝ≥0`
+ Use this to prove operator monotonicity and concavity/convexity of `rpow` and `log`
-/

open MeasureTheory Topology
open scoped ContinuousMapZero

section unital

variable {X : Type*} {𝕜 : Type*} {A : Type*} {p : A → Prop} [RCLike 𝕜]
  [MeasurableSpace X] {μ : Measure X}
  [NormedRing A] [StarRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]
  [ContinuousFunctionalCalculus 𝕜 A p]

lemma cfcL_integral [NormedAlgebra ℝ A] (a : A) (f : X → C(spectrum 𝕜 a, 𝕜)) (hf₁ : Integrable f μ)
    (ha : p a := by cfc_tac) :
    ∫ x, cfcL (a := a) ha (f x) ∂μ = cfcL (a := a) ha (∫ x, f x ∂μ) := by
  rw [ContinuousLinearMap.integral_comp_comm _ hf₁]

lemma cfcHom_integral [NormedAlgebra ℝ A] (a : A) (f : X → C(spectrum 𝕜 a, 𝕜))
    (hf₁ : Integrable f μ) (ha : p a := by cfc_tac) :
    ∫ x, cfcHom (a := a) ha (f x) ∂μ = cfcHom (a := a) ha (∫ x, f x ∂μ) :=
  cfcL_integral a f hf₁ ha

open ContinuousMap Classical in
lemma integrable_cfc_set {s : Set X} (hs : MeasurableSet s) (f : X → 𝕜 → 𝕜)
    (bound : X → ℝ) (a : A) (hf₁ : ∀ x ∈ s, ContinuousOn (f x) (spectrum 𝕜 a))
    (hf₂ : AEStronglyMeasurable (fun x : X =>
      if h : x ∈ s then (⟨_, (hf₁ x h).restrict⟩ : C(spectrum 𝕜 a, 𝕜)) else 0) (μ.restrict s))
    (hbound : ∀ x ∈ s, ∀ z ∈ spectrum 𝕜 a, ‖f x z‖ ≤ ‖bound x‖)
    (hbound_finite_integral : HasFiniteIntegral bound (μ.restrict s)) (ha : p a := by cfc_tac) :
    IntegrableOn (fun x => cfc (f x) a) s μ := by
  have ha : p a := ha
  let fc : X → C(spectrum 𝕜 a, 𝕜) := fun x =>
    if h : x ∈ s then ⟨_, (hf₁ x h).restrict⟩ else 0
  have hfc : s.EqOn (fun x r => fc x r) (fun x => (spectrum 𝕜 a).restrict (f x)) := by
    intro x hx
    ext
    simp [fc, hx]
  have fc_integrable : IntegrableOn fc s μ := by
    refine ⟨hf₂, ?_⟩
    refine hbound_finite_integral.mono ?_
    filter_upwards [ae_restrict_mem hs] with x hx
    rw [norm_le _ (norm_nonneg (bound x))]
    intro z
    have := hfc hx
    simp only at this
    simp only [this, Set.restrict_apply]
    exact hbound x hx z.1 z.2
  have h₁ : s.EqOn (fun x : X => cfc (f x) a) (fun x : X => cfcL ha (fc x)) := by
    intro x hx
    dsimp
    rw [cfc_apply ..]
    unfold fc
    simp [hx]
  refine .congr_fun ?_ h₁.symm hs
  exact ContinuousLinearMap.integrable_comp _ fc_integrable

open ContinuousMap Classical in
lemma integrable_cfc_set' [TopologicalSpace X] [OpensMeasurableSpace X] {s : Set X}
    (hs : MeasurableSet s) (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A)
    [SecondCountableTopologyEither X C(spectrum 𝕜 a, 𝕜)]
    (hf : Continuous (fun x : s × spectrum 𝕜 a => f x.1 x.2))
    (hbound : ∀ x ∈ s, ∀ z ∈ spectrum 𝕜 a, ‖f x z‖ ≤ ‖bound x‖)
    (hbound_finite_integral : HasFiniteIntegral bound (μ.restrict s)) (ha : p a := by cfc_tac) :
    IntegrableOn (fun x => cfc (f x) a) s μ := by
  let fc : C(s × (spectrum 𝕜 a), 𝕜) := ⟨fun x => f x.1 x.2, hf⟩
  let fc₂ := fc.curry
  refine integrable_cfc_set hs f bound a ?_ ?_ hbound hbound_finite_integral
  · intro x xs
    rw [continuousOn_iff_continuous_restrict]
    exact (fc₂ ⟨x, xs⟩).continuous
  · refine ContinuousOn.aestronglyMeasurable ?_ hs
    rw [continuousOn_iff_continuous_restrict]
    refine fc₂.continuous.congr ?_
    intro ⟨x, hx⟩
    ext
    simp [fc₂, fc, hx]

open ContinuousMap Set in
lemma integrable_cfc (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A)
    (hf₁ : ∀ x, ContinuousOn (f x) (spectrum 𝕜 a))
    (hf₂ : AEStronglyMeasurable (fun x ↦ (⟨_, hf₁ x |>.restrict⟩ : C(spectrum 𝕜 a, 𝕜))) μ)
    (hbound : ∀ x, ∀ z ∈ spectrum 𝕜 a, ‖f x z‖ ≤ ‖bound x‖)
    (hbound_finite_integral : HasFiniteIntegral bound μ) (ha : p a := by cfc_tac) :
    Integrable (fun x => cfc (f x) a) μ := by
  rw [← integrableOn_univ]
  refine integrable_cfc_set MeasurableSet.univ f bound a ?_ ?_ ?_ ?_ ha
  · exact fun x _ => hf₁ x
  · simp [hf₂]
  · exact fun x _ => hbound x
  · simp [hbound_finite_integral]

open ContinuousMap in
lemma integrable_cfc' [TopologicalSpace X] [OpensMeasurableSpace X] (f : X → 𝕜 → 𝕜)
    (bound : X → ℝ) (a : A) [SecondCountableTopologyEither X C(spectrum 𝕜 a, 𝕜)]
    (hf : Continuous (fun x : X × spectrum 𝕜 a => f x.1 x.2))
    (hbound : ∀ x, ∀ z ∈ spectrum 𝕜 a, ‖f x z‖ ≤ ‖bound x‖)
    (hbound_finite_integral : HasFiniteIntegral bound μ) (ha : p a := by cfc_tac) :
    Integrable (fun x => cfc (f x) a) μ := by
  let fc : C(X × (spectrum 𝕜 a), 𝕜) := ⟨fun x => f x.1 x.2, hf⟩
  let fc₂ := fc.curry
  refine integrable_cfc f bound a ?_ ?_ hbound hbound_finite_integral
  · intro x
    rw [continuousOn_iff_continuous_restrict]
    exact (fc₂ x).continuous
  · apply Continuous.aestronglyMeasurable
    exact ContinuousMap.curry ⟨_, hf⟩ |>.continuous

open ContinuousMap Classical in
/-- The continuous functional calculus commutes with integration. -/
lemma cfc_setIntegral [NormedAlgebra ℝ A] {s : Set X} (hs : MeasurableSet s) (f : X → 𝕜 → 𝕜)
    (bound : X → ℝ) (a : A) (hf₁ : ∀ x ∈ s, ContinuousOn (f x) (spectrum 𝕜 a))
    (hf₂ : AEStronglyMeasurable (fun x : X =>
      if h : x ∈ s then (⟨_, (hf₁ x h).restrict⟩ : C(spectrum 𝕜 a, 𝕜)) else 0) (μ.restrict s))
    (hbound : ∀ x ∈ s, ∀ z ∈ spectrum 𝕜 a, ‖f x z‖ ≤ ‖bound x‖)
    (hbound_finite_integral : HasFiniteIntegral bound (μ.restrict s)) (ha : p a := by cfc_tac) :
    cfc (fun r => ∫ x in s, f x r ∂μ) a = ∫ x in s, cfc (f x) a ∂μ := by
  let fc : X → C(spectrum 𝕜 a, 𝕜) := fun x =>
    if h : x ∈ s then ⟨_, (hf₁ x h).restrict⟩ else 0
  have hfc : s.EqOn (fun x r => fc x r) (fun x => (spectrum 𝕜 a).restrict (f x)) := by
    intro x hx
    ext
    simp [fc, hx]
  have fc_integrable : IntegrableOn fc s μ := by
    refine ⟨hf₂, ?_⟩
    refine hbound_finite_integral.mono ?_
    filter_upwards [ae_restrict_mem hs] with x hx
    rw [norm_le _ (norm_nonneg (bound x))]
    intro z
    have := hfc hx
    simp only at this
    simp only [this, Set.restrict_apply]
    exact hbound x hx z.1 z.2
  have ha : p a := ha
  have h₁ : s.EqOn (fun x : X => cfc (f x) a) (fun x : X => cfcL ha (fc x)) := by
    intro x hx
    dsimp
    rw [cfc_apply ..]
    unfold fc
    simp [hx]
  have h₂ : ((spectrum 𝕜 a).restrict
      fun r => ∫ (x : X) in s, f x r ∂μ) = (∫ (x : X) in s, fc x ∂μ).toFun := by
    ext r
    simp only [Set.restrict_apply, toFun_eq_coe, fc, ContinuousMap.integral_apply fc_integrable _]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem hs] with x hx
    simp [fc, hx]
  have hcont₂ : ContinuousOn (fun r => ∫ x in s, f x r ∂μ) (spectrum 𝕜 a) := by
    rw [continuousOn_iff_continuous_restrict]
    convert map_continuous (∫ x in s, fc x ∂μ)
  rw [setIntegral_congr_fun hs h₁, ContinuousLinearMap.integral_comp_comm _ fc_integrable,
      cfcL_apply, cfc_apply ..]
  congr

open ContinuousMap Classical in
/-- The continuous functional calculus commutes with integration. -/
lemma cfc_setIntegral' [NormedAlgebra ℝ A] [TopologicalSpace X] [OpensMeasurableSpace X] {s : Set X}
    (hs : MeasurableSet s) (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A)
    [SecondCountableTopologyEither X C(spectrum 𝕜 a, 𝕜)]
    (hf : Continuous (fun x : s × spectrum 𝕜 a => f x.1 x.2))
    (hbound : ∀ x ∈ s, ∀ z ∈ spectrum 𝕜 a, ‖f x z‖ ≤ ‖bound x‖)
    (hbound_finite_integral : HasFiniteIntegral bound (μ.restrict s)) (ha : p a := by cfc_tac) :
    cfc (fun r => ∫ x in s, f x r ∂μ) a = ∫ x in s, cfc (f x) a ∂μ := by
  let fc : C(s × (spectrum 𝕜 a), 𝕜) := ⟨fun x => f x.1 x.2, hf⟩
  let fc₂ := fc.curry
  refine cfc_setIntegral hs f bound a ?_ ?_ hbound hbound_finite_integral
  · intro x xs
    rw [continuousOn_iff_continuous_restrict]
    exact (fc₂ ⟨x, xs⟩).continuous
  · refine ContinuousOn.aestronglyMeasurable ?_ hs
    rw [continuousOn_iff_continuous_restrict]
    refine fc₂.continuous.congr ?_
    intro ⟨x, hx⟩
    ext
    simp [fc₂, fc, hx]

open ContinuousMap Set in
/-- The continuous functional calculus commutes with integration. -/
lemma cfc_integral [NormedAlgebra ℝ A] (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A)
    (hf₁ : ∀ x, ContinuousOn (f x) (spectrum 𝕜 a))
    (hf₂ : AEStronglyMeasurable (fun x ↦ (⟨_, hf₁ x |>.restrict⟩ : C(spectrum 𝕜 a, 𝕜))) μ)
    (hbound : ∀ x, ∀ z ∈ spectrum 𝕜 a, ‖f x z‖ ≤ ‖bound x‖)
    (hbound_finite_integral : HasFiniteIntegral bound μ) (ha : p a := by cfc_tac) :
    cfc (fun r => ∫ x, f x r ∂μ) a = ∫ x, cfc (f x) a ∂μ := by
  have : cfc (fun r => ∫ x, f x r ∂μ) a = cfc (fun r => ∫ x in univ, f x r ∂μ) a := by
    simp [← setIntegral_univ]
  rw [← setIntegral_univ, this]
  refine cfc_setIntegral MeasurableSet.univ f bound a ?_ ?_ ?_ ?_
  · exact fun x _ => hf₁ x
  · simp [hf₂]
  · exact fun x _ => hbound x
  · simp [hbound_finite_integral]

/-- The continuous functional calculus commutes with integration. -/
lemma cfc_integral' [NormedAlgebra ℝ A] [TopologicalSpace X] [OpensMeasurableSpace X]
    (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A) [SecondCountableTopologyEither X C(spectrum 𝕜 a, 𝕜)]
    (hf : Continuous (fun x : X × spectrum 𝕜 a => f x.1 x.2))
    (hbound : ∀ x, ∀ z ∈ spectrum 𝕜 a, ‖f x z‖ ≤ ‖bound x‖)
    (hbound_finite_integral : HasFiniteIntegral bound μ) (ha : p a := by cfc_tac) :
    cfc (fun r => ∫ x, f x r ∂μ) a = ∫ x, cfc (f x) a ∂μ := by
  let fc : C(X × (spectrum 𝕜 a), 𝕜) := ⟨fun x => f x.1 x.2, hf⟩
  let fc₂ := fc.curry
  refine cfc_integral f bound a ?_ ?_ hbound hbound_finite_integral
  · intro x
    rw [continuousOn_iff_continuous_restrict]
    exact (fc₂ x).continuous
  · apply Continuous.aestronglyMeasurable
    exact ContinuousMap.curry ⟨_, hf⟩ |>.continuous

end unital

section nonunital

variable {X : Type*} {𝕜 : Type*} {A : Type*} {p : A → Prop} [RCLike 𝕜]
  [MeasurableSpace X] {μ : Measure X} [NonUnitalNormedRing A] [StarRing A] [CompleteSpace A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
  [NonUnitalContinuousFunctionalCalculus 𝕜 A p]

lemma cfcₙL_integral [NormedSpace ℝ A] (a : A) (f : X → C(quasispectrum 𝕜 a, 𝕜)₀)
    (hf₁ : Integrable f μ) (ha : p a := by cfc_tac) :
    ∫ x, cfcₙL (a := a) ha (f x) ∂μ = cfcₙL (a := a) ha (∫ x, f x ∂μ) := by
  rw [ContinuousLinearMap.integral_comp_comm _ hf₁]

lemma cfcₙHom_integral [NormedSpace ℝ A] (a : A) (f : X → C(quasispectrum 𝕜 a, 𝕜)₀)
    (hf₁ : Integrable f μ) (ha : p a := by cfc_tac) :
    ∫ x, cfcₙHom (a := a) ha (f x) ∂μ = cfcₙHom (a := a) ha (∫ x, f x ∂μ) :=
  cfcₙL_integral a f hf₁ ha

open ContinuousMapZero Classical in
lemma integrable_cfcₙ_set {s : Set X} (hs : MeasurableSet s) (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A)
    (hf₁ : ∀ x ∈ s, ContinuousOn (f x) (quasispectrum 𝕜 a))
    (hf₂ : ∀ x ∈ s, f x 0 = 0)
    (hf₃ : AEStronglyMeasurable (fun x : X =>
      if h : x ∈ s then
        (⟨⟨_, (hf₁ x h).restrict⟩, by simp [hf₂ x h]⟩ : C(quasispectrum 𝕜 a, 𝕜)₀)
      else 0) (μ.restrict s))
    (hbound : ∀ x ∈ s, ∀ z ∈ quasispectrum 𝕜 a, ‖f x z‖ ≤ ‖bound x‖)
    (hbound_finite_integral : HasFiniteIntegral bound (μ.restrict s)) (ha : p a := by cfc_tac) :
    IntegrableOn (fun x => cfcₙ (f x) a) s μ := by
  have ha : p a := ha
  let fc : X → C(quasispectrum 𝕜 a, 𝕜)₀ := fun x =>
    if h : x ∈ s then ⟨⟨_, (hf₁ x h).restrict⟩, by simp [hf₂ x h]⟩ else 0
  have hfc : s.EqOn (fun x r => fc x r) (fun x => (quasispectrum 𝕜 a).restrict (f x)) := by
    intro x hx
    ext
    simp [fc, hx]
  have fc_integrable : IntegrableOn fc s μ := by
    refine ⟨hf₃, ?_⟩
    refine hbound_finite_integral.mono ?_
    filter_upwards [ae_restrict_mem hs] with x hx
    rw [norm_def, ContinuousMap.norm_le _ (norm_nonneg (bound x))]
    intro z
    have := hfc hx
    simp only at this
    simp only [ContinuousMap.coe_coe, this, Set.restrict_apply, Real.norm_eq_abs, ge_iff_le, fc]
    exact hbound x hx z.1 z.2
  have h₁ : s.EqOn (fun x : X => cfcₙ (f x) a) (fun x : X => cfcₙL ha (fc x)) := by
    intro x hx
    dsimp
    rw [cfcₙ_apply ..]
    unfold fc
    simp [hx]
  refine .congr_fun ?_ h₁.symm hs
  exact ContinuousLinearMap.integrable_comp _ fc_integrable

open ContinuousMap Classical in
lemma integrable_cfcₙ_set' [TopologicalSpace X] [OpensMeasurableSpace X] {s : Set X}
    (hs : MeasurableSet s) (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A)
    [SecondCountableTopologyEither X C(quasispectrum 𝕜 a, 𝕜)₀]
    (hf : Continuous (fun x : s × quasispectrum 𝕜 a => f x.1 x.2))
    (hf₂ : ∀ x ∈ s, f x 0 = 0)
    (hbound : ∀ x ∈ s, ∀ z ∈ quasispectrum 𝕜 a, ‖f x z‖ ≤ ‖bound x‖)
    (hbound_finite_integral : HasFiniteIntegral bound (μ.restrict s)) (ha : p a := by cfc_tac) :
    IntegrableOn (fun x => cfcₙ (f x) a) s μ := by
  let fc : C(s × (quasispectrum 𝕜 a), 𝕜) := ⟨fun x => f x.1 x.2, hf⟩
  let fc₂ : C(s, C(quasispectrum 𝕜 a, 𝕜)₀) :=
    { toFun := fun x => ⟨fc.curry x, by simp [fc, hf₂]⟩
      continuous_toFun := by
        have : Continuous
            (ContinuousMapZero.toContinuousMap ∘ (fun x => ⟨fc.curry x, by simp [fc, hf₂]⟩)) :=
          ContinuousMap.continuous fc.curry
        refine (Topology.IsEmbedding.continuous_iff ?_).mpr this
        apply IsUniformEmbedding.isEmbedding
        exact Isometry.isUniformEmbedding fun x1 ↦ congrFun rfl }
  refine integrable_cfcₙ_set hs f bound a ?_ hf₂ ?_ hbound hbound_finite_integral
  · intro x xs
    rw [continuousOn_iff_continuous_restrict]
    exact (fc₂ ⟨x, xs⟩).continuous
  · refine ContinuousOn.aestronglyMeasurable ?_ hs
    rw [continuousOn_iff_continuous_restrict]
    refine fc₂.continuous.congr ?_
    intro ⟨x, hx⟩
    ext
    simp [fc₂, fc, hx]

open ContinuousMapZero Classical in
/-- The non-unital continuous functional calculus commutes with integration. -/
lemma cfcₙ_setIntegral [NormedSpace ℝ A] {s : Set X} (hs : MeasurableSet s) (f : X → 𝕜 → 𝕜)
    (bound : X → ℝ) (a : A) (hf₁ : ∀ x ∈ s, ContinuousOn (f x) (quasispectrum 𝕜 a))
    (hf₂ : ∀ x ∈ s, f x 0 = 0)
    (hf₃ : AEStronglyMeasurable (fun x : X =>
      if h : x ∈ s then
        (⟨⟨_, (hf₁ x h).restrict⟩, by simp [hf₂ x h]⟩ : C(quasispectrum 𝕜 a, 𝕜)₀)
      else 0) (μ.restrict s))
    (hbound : ∀ x ∈ s, ∀ z ∈ quasispectrum 𝕜 a, ‖f x z‖ ≤ ‖bound x‖)
    (hbound_finite_integral : HasFiniteIntegral bound (μ.restrict s)) (ha : p a := by cfc_tac) :
    cfcₙ (fun r => ∫ x in s, f x r ∂μ) a = ∫ x in s, cfcₙ (f x) a ∂μ := by
  let fc : X → C(quasispectrum 𝕜 a, 𝕜)₀ := fun x =>
    if h : x ∈ s then ⟨⟨_, (hf₁ x h).restrict⟩, by simp [hf₂ x h]⟩ else 0
  have hfc : s.EqOn (fun x r => fc x r) (fun x => (quasispectrum 𝕜 a).restrict (f x)) := by
    intro x hx
    ext
    simp [fc, hx]
  have fc_integrable : IntegrableOn fc s μ := by
    refine ⟨hf₃, ?_⟩
    refine hbound_finite_integral.mono ?_
    filter_upwards [ae_restrict_mem hs] with x hx
    rw [norm_def, ContinuousMap.norm_le _ (norm_nonneg (bound x))]
    intro z
    have := hfc hx
    simp only at this
    simp only [ContinuousMap.coe_coe, this, Set.restrict_apply, Real.norm_eq_abs, ge_iff_le, fc]
    exact hbound x hx z.1 z.2
  have ha : p a := ha
  have h₁ : s.EqOn (fun x : X => cfcₙ (f x) a) (fun x : X => cfcₙL ha (fc x)) := by
    intro x hx
    dsimp
    rw [cfcₙ_apply ..]
    unfold fc
    simp [hx]
  have h₂ : ((quasispectrum 𝕜 a).restrict fun r => ∫ (x : X) in s, f x r ∂μ)
      = (∫ (x : X) in s, fc x ∂μ).toFun := by
    ext r
    change (quasispectrum 𝕜 a).restrict (fun r ↦ ∫ (x : X) in s, f x r ∂μ) r
      = (∫ (x : X) in s, fc x ∂μ) r
    rw [ContinuousMapZero.integral_apply fc_integrable]
    simp only [Set.restrict_apply, fc]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem hs] with x hx
    simp [fc, hx]
  have hcont₂ : ContinuousOn (fun r => ∫ x in s, f x r ∂μ) (quasispectrum 𝕜 a) := by
    rw [continuousOn_iff_continuous_restrict]
    convert map_continuous (∫ x in s, fc x ∂μ)
  have hf0 : (fun r => ∫ (x : X) in s, f x r ∂μ) 0 = 0 := by
    simp only [fc]
    calc ∫ x in s, f x 0 ∂μ = ∫ x in s, 0 ∂μ := setIntegral_congr_fun hs hf₂
      _ = 0 := by simp
  rw [setIntegral_congr_fun hs h₁, ContinuousLinearMap.integral_comp_comm _ fc_integrable,
      cfcₙL_apply, cfcₙ_apply ..]
  congr

open ContinuousMap Classical in
/-- The non-unital continuous functional calculus commutes with integration. -/
lemma cfcₙ_setIntegral' [NormedSpace ℝ A] [TopologicalSpace X] [OpensMeasurableSpace X] {s : Set X}
    (hs : MeasurableSet s) (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A)
    [SecondCountableTopologyEither X C(quasispectrum 𝕜 a, 𝕜)₀]
    (hf : Continuous (fun x : s × quasispectrum 𝕜 a => f x.1 x.2))
    (hf₂ : ∀ x ∈ s, f x 0 = 0)
    (hbound : ∀ x ∈ s, ∀ z ∈ quasispectrum 𝕜 a, ‖f x z‖ ≤ ‖bound x‖)
    (hbound_finite_integral : HasFiniteIntegral bound (μ.restrict s)) (ha : p a := by cfc_tac) :
    cfcₙ (fun r => ∫ x in s, f x r ∂μ) a = ∫ x in s, cfcₙ (f x) a ∂μ := by
  let fc : C(s × (quasispectrum 𝕜 a), 𝕜) := ⟨fun x => f x.1 x.2, hf⟩
  let fc₂ : C(s, C(quasispectrum 𝕜 a, 𝕜)₀) :=
    { toFun := fun x => ⟨fc.curry x, by simp [fc, hf₂]⟩
      continuous_toFun := by
        have : Continuous
            (ContinuousMapZero.toContinuousMap ∘ (fun x => ⟨fc.curry x, by simp [fc, hf₂]⟩)) :=
          ContinuousMap.continuous fc.curry
        refine (Topology.IsEmbedding.continuous_iff ?_).mpr this
        apply IsUniformEmbedding.isEmbedding
        exact Isometry.isUniformEmbedding fun x1 ↦ congrFun rfl }
  refine cfcₙ_setIntegral hs f bound a ?_ hf₂ ?_ hbound hbound_finite_integral
  · intro x xs
    rw [continuousOn_iff_continuous_restrict]
    exact (fc₂ ⟨x, xs⟩).continuous
  · refine ContinuousOn.aestronglyMeasurable ?_ hs
    rw [continuousOn_iff_continuous_restrict]
    refine fc₂.continuous.congr ?_
    intro ⟨x, hx⟩
    ext
    simp [fc₂, fc, hx]

open ContinuousMapZero Set in
/-- The non-unital continuous functional calculus commutes with integration. -/
lemma cfcₙ_integral [NormedSpace ℝ A] (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A)
    (hf₁ : ∀ x, ContinuousOn (f x) (quasispectrum 𝕜 a)) (hf₂ : ∀ x, f x 0 = 0)
    (hf₃ : AEStronglyMeasurable
      (fun x ↦ (⟨⟨_, hf₁ x |>.restrict⟩, by simp [hf₂]⟩ : C(quasispectrum 𝕜 a, 𝕜)₀)) μ)
    (hbound : ∀ x, ∀ z ∈ quasispectrum 𝕜 a, ‖f x z‖ ≤ ‖bound x‖)
    (hbound_finite_integral : HasFiniteIntegral bound μ) (ha : p a := by cfc_tac) :
    cfcₙ (fun r => ∫ x, f x r ∂μ) a = ∫ x, cfcₙ (f x) a ∂μ := by
  have : cfcₙ (fun r => ∫ x, f x r ∂μ) a = cfcₙ (fun r => ∫ x in univ, f x r ∂μ) a := by
    simp [← setIntegral_univ]
  rw [← setIntegral_univ, this]
  refine cfcₙ_setIntegral MeasurableSet.univ f bound a ?_ ?_ ?_ ?_ ?_
  · exact fun x _ => hf₁ x
  · simp [hf₂]
  · simp [hf₃]
  · exact fun x _ => hbound x
  · simp [hbound_finite_integral]

/-- The non-unital continuous functional calculus commutes with integration. -/
lemma cfcₙ_integral' [NormedSpace ℝ A] [TopologicalSpace X] [OpensMeasurableSpace X] (f : X → 𝕜 → 𝕜)
    (bound : X → ℝ) (a : A) [SecondCountableTopologyEither X C(quasispectrum 𝕜 a, 𝕜)₀]
    (hf : Continuous (fun x : X × quasispectrum 𝕜 a => f x.1 x.2))
    (hf₂ : ∀ x, f x 0 = 0)
    (hbound : ∀ x, ∀ z ∈ quasispectrum 𝕜 a, ‖f x z‖ ≤ ‖bound x‖)
    (hbound_finite_integral : HasFiniteIntegral bound μ) (ha : p a := by cfc_tac) :
    cfcₙ (fun r => ∫ x, f x r ∂μ) a = ∫ x, cfcₙ (f x) a ∂μ := by
  let fc : C(X × (quasispectrum 𝕜 a), 𝕜) := ⟨fun x => f x.1 x.2, hf⟩
  let fc₂ : C(X, C(quasispectrum 𝕜 a, 𝕜)₀) :=
    { toFun := fun x => ⟨fc.curry x, by simp [fc, hf₂]⟩
      continuous_toFun := by
        have : Continuous
            (ContinuousMapZero.toContinuousMap ∘ (fun x => ⟨fc.curry x, by simp [fc, hf₂]⟩)) :=
          ContinuousMap.continuous fc.curry
        refine (Topology.IsEmbedding.continuous_iff ?_).mpr this
        apply IsUniformEmbedding.isEmbedding
        exact Isometry.isUniformEmbedding fun x1 ↦ congrFun rfl }
  refine cfcₙ_integral f bound a ?_ hf₂ ?_ hbound hbound_finite_integral
  · intro x
    rw [continuousOn_iff_continuous_restrict]
    exact (fc₂ x).continuous
  · refine Continuous.aestronglyMeasurable ?_
    refine fc₂.continuous.congr ?_
    intro x
    ext
    simp [fc₂, fc]

end nonunital
