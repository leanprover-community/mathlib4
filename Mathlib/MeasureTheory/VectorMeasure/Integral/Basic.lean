/-
Copyright (c) 2025 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.SetToL1
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.VectorMeasure.Integral.L1

/-!

## Main statements

1. Integral is a linear operator on functions, bilinear forms, and vector measures, respectively. For example,

  * `integral_add`              : `∫ a, B (f a + g a) ∂μ = ∫ a, B (f a) ∂μ + ∫ a, B (g a) ∂μ`.
  * `integral_add_pairing`      : `∫ a, (B + C) (f a) ∂μ = ∫ a, B (f a) ∂μ + ∫ a, C (f a) ∂μ`.
  * `integral_add_measure`      : `∫ a, B (f a) ∂(μ + ν) = ∫ a, B (f a) ∂μ + ∫ a, B (f a) ∂ν`.

-/
noncomputable section

open ENNReal Filter Set TopologicalSpace Topology MeasureTheory
open Real VectorMeasure ContinuousLinearMap

namespace VectorMeasure

/-!
## Integral against a vector measure on functions

Define the vector-valued integral on functions generally to be the `L1` vector-valued integral,
for integrable functions, and 0 otherwise/
-/

variable {α E F G 𝕜 : Type*}
  [MeasurableSpace α] [NormedDivisionRing 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

open Classical in
/-- The vector-valued integral against a vector measure. -/
irreducible_def integral (f : α → E) (Bμ : VectorMeasureWithPairing α E F G) : G :=
  if _ : CompleteSpace G then
    if hf : Integrable f Bμ.vectorMeasure.variation.ennrealToMeasure
    then Bμ.integral (hf.toL1 f) else 0
  else 0

@[inherit_doc VectorMeasure.integral]
notation3 "∫ "(...)", "r:60:(scoped f => f)" ∂"Bμ:70 => integral r Bμ

@[inherit_doc VectorMeasure.integral]
notation3 "∫ "(...)" in "s", "r:60:(scoped f => f)" ∂"Bμ:70 =>
  integral r (VectorMeasureWithPairing.restrict Bμ s)

section Properties

variable {f : α → E} {Bμ : VectorMeasureWithPairing α E F G}

theorem integral_eq [hG : CompleteSpace G]
    (hf : Integrable f Bμ.vectorMeasure.variation.ennrealToMeasure) :
    ∫ a, f a ∂Bμ = Bμ.integral (hf.toL1 f) := by
  simp [integral, hG, hf]

theorem integral_eq_setToFun [hG : CompleteSpace G] :
    ∫ a, f a ∂Bμ = setToFun Bμ.vectorMeasure.variation.ennrealToMeasure
    (weightedVectorSMul Bμ.pairing Bμ.vectorMeasure)
    (dominatedFinMeasAdditive_weightedVectorSMul Bμ.pairing Bμ.vectorMeasure) f := by
  simp only [integral, hG]; rfl

theorem L1.integral_eq_integral [hG : CompleteSpace G]
    (f : α →₁[Bμ.vectorMeasure.variation.ennrealToMeasure] E) :
    Bμ.integral f = ∫ a, f a ∂Bμ := by
  simp only [integral_eq_setToFun]
  exact (L1.setToFun_eq_setToL1 (dominatedFinMeasAdditive_weightedVectorSMul
    Bμ.pairing Bμ.vectorMeasure) f).symm

theorem integral_undef (h : ¬Integrable f Bμ.vectorMeasure.variation.ennrealToMeasure) :
    ∫ a, f a ∂Bμ = 0 := by
  by_cases hG : CompleteSpace G
  · simp [integral, hG, h]
  · simp [integral, hG]

theorem Integrable.of_integral_ne_zero (h : ∫ a, f a ∂Bμ ≠ 0) :
    Integrable f Bμ.vectorMeasure.variation.ennrealToMeasure :=
  Not.imp_symm integral_undef h

theorem integral_non_aestronglyMeasurable
    (h : ¬AEStronglyMeasurable f Bμ.vectorMeasure.variation.ennrealToMeasure) :
    ∫ a, f a ∂Bμ = 0 :=
  integral_undef <| not_and_of_not_left _ h

@[simp]
theorem integral_zero : ∫ _ : α, 0 ∂Bμ = 0 := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact setToFun_zero (dominatedFinMeasAdditive_weightedVectorSMul Bμ.pairing Bμ.vectorMeasure)
  · simp [integral, hG]

@[simp]
theorem integral_zero' : integral 0 Bμ = 0 :=
  integral_zero

lemma integral_indicator₂ {β : Type*} (f : β → α → E) (s : Set β) (b : β) :
    ∫ y, s.indicator (f · y) b ∂Bμ = s.indicator (fun x ↦ ∫ y, f x y ∂Bμ) b := by
  by_cases hb : b ∈ s <;> simp [hb]

theorem integrable_of_integral_eq_one {f : α → ℝ} {Bμ : VectorMeasureWithPairing α ℝ ℝ ℝ}
    (h : ∫ a, f a ∂Bμ = 1) : Integrable f Bμ.vectorMeasure.variation.ennrealToMeasure :=
  Integrable.of_integral_ne_zero <| h ▸ one_ne_zero

theorem integral_add {g : α → E} (hf : Integrable f Bμ.vectorMeasure.variation.ennrealToMeasure)
    (hg : Integrable g Bμ.vectorMeasure.variation.ennrealToMeasure) :
    ∫ a, f a + g a ∂Bμ = ∫ a, f a ∂Bμ + ∫ a, g a ∂Bμ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact setToFun_add
      (dominatedFinMeasAdditive_weightedVectorSMul Bμ.pairing Bμ.vectorMeasure) hf hg
  · simp [integral, hG]

theorem integral_add' {g : α → E} (hf : Integrable f Bμ.vectorMeasure.variation.ennrealToMeasure)
    (hg : Integrable g Bμ.vectorMeasure.variation.ennrealToMeasure) :
    ∫ a, (f + g) a ∂Bμ = ∫ a, f a ∂Bμ + ∫ a, g a ∂Bμ :=
  integral_add hf hg

theorem integral_finset_sum {ι} (s : Finset ι) {f : ι → α → E}
    (hf : ∀ i ∈ s, Integrable (f i) Bμ.vectorMeasure.variation.ennrealToMeasure) :
    ∫ a, ∑ i ∈ s, f i a ∂Bμ = ∑ i ∈ s, ∫ a, f i a ∂Bμ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact setToFun_finset_sum
      (dominatedFinMeasAdditive_weightedVectorSMul Bμ.pairing Bμ.vectorMeasure) s hf
  · simp [integral, hG]

@[integral_simps]
theorem integral_neg (f : α → E) : ∫ a, -f a ∂Bμ = -∫ a, f a ∂Bμ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact setToFun_neg (dominatedFinMeasAdditive_weightedVectorSMul Bμ.pairing Bμ.vectorMeasure) f
  · simp [integral, hG]

theorem integral_neg' (f : α → E) : ∫ a, (-f) a ∂Bμ = -∫ a, f a ∂Bμ :=
  integral_neg f

theorem integral_sub {g : α → E} (hf : Integrable f Bμ.vectorMeasure.variation.ennrealToMeasure)
    (hg : Integrable g Bμ.vectorMeasure.variation.ennrealToMeasure) :
    ∫ a, f a - g a ∂Bμ = ∫ a, f a ∂Bμ - ∫ a, g a ∂Bμ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact setToFun_sub
      (dominatedFinMeasAdditive_weightedVectorSMul Bμ.pairing Bμ.vectorMeasure) hf hg
  · simp [integral, hG]

theorem integral_sub' {g : α → E} (hf : Integrable f Bμ.vectorMeasure.variation.ennrealToMeasure)
    (hg : Integrable g Bμ.vectorMeasure.variation.ennrealToMeasure) :
    ∫ a, (f - g) a ∂Bμ = ∫ a, f a ∂Bμ - ∫ a, g a ∂Bμ :=
  integral_sub hf hg

theorem integral_congr_ae {g : α → E} (h : f =ᵐ[Bμ.vectorMeasure.variation.ennrealToMeasure] g) :
    ∫ a, f a ∂Bμ = ∫ a, g a ∂Bμ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact setToFun_congr_ae
      (dominatedFinMeasAdditive_weightedVectorSMul Bμ.pairing Bμ.vectorMeasure) h
  · simp [integral, hG]

lemma integral_congr_ae₂ {β H J : Type*} {_ : MeasurableSpace β}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup J] [NormedSpace ℝ J]
    {Bν : VectorMeasureWithPairing β H J E}
    {f g : α → β → H} (h : ∀ᵐ a ∂Bμ.vectorMeasure.variation.ennrealToMeasure,
      f a =ᵐ[Bν.vectorMeasure.variation.ennrealToMeasure] g a) :
    ∫ a, ∫ b, f a b ∂Bν ∂Bμ = ∫ a, ∫ b, g a b ∂Bν ∂Bμ := by
  apply integral_congr_ae
  filter_upwards [h] with _ ha
  apply integral_congr_ae
  filter_upwards [ha] with _ hb using hb

@[simp]
theorem L1.integral_of_fun_eq_integral'
    (hf : Integrable f Bμ.vectorMeasure.variation.ennrealToMeasure) :
    ∫ a, (AEEqFun.mk f hf.aestronglyMeasurable) a ∂Bμ = ∫ a, f a ∂Bμ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact setToFun_toL1 (dominatedFinMeasAdditive_weightedVectorSMul Bμ.pairing Bμ.vectorMeasure) hf
  · simp [integral, hG]

theorem L1.integral_of_fun_eq_integral
    (hf : Integrable f Bμ.vectorMeasure.variation.ennrealToMeasure) :
    ∫ a, (hf.toL1 f) a ∂Bμ = ∫ a, f a ∂Bμ := by
  simp [hf]

@[continuity]
theorem continuous_integral : Continuous fun f : α →₁[Bμ.vectorMeasure.variation.ennrealToMeasure] E
    => ∫ a, f a ∂Bμ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact continuous_setToFun
      (dominatedFinMeasAdditive_weightedVectorSMul Bμ.pairing Bμ.vectorMeasure)
  · simp [integral, hG, continuous_const]

theorem integral_eq_zero_of_ae
    (hf : f =ᵐ[Bμ.vectorMeasure.variation.ennrealToMeasure] 0) : ∫ a, f a ∂Bμ = 0 := by
  simp [integral_congr_ae hf]

/-- If `F i → f` in `L1`, then `∫ x, F i x ∂Bμ → ∫ x, f x ∂Bμ`. -/
theorem tendsto_integral_of_L1 {ι} (f : α → E)
    (hfi : Integrable f Bμ.vectorMeasure.variation.ennrealToMeasure) {F : ι → α → E} {l : Filter ι}
    (hFi : ∀ᶠ i in l, Integrable (F i) Bμ.vectorMeasure.variation.ennrealToMeasure)
    (hF : Tendsto (fun i => ∫⁻ x, ‖F i x - f x‖ₑ ∂Bμ.vectorMeasure.variation.ennrealToMeasure)
    l (𝓝 0)) :
    Tendsto (fun i => ∫ x, F i x ∂Bμ) l (𝓝 <| ∫ x, f x ∂Bμ) := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact tendsto_setToFun_of_L1
      (dominatedFinMeasAdditive_weightedVectorSMul Bμ.pairing Bμ.vectorMeasure) f hfi hFi hF
  · simp [integral, hG, tendsto_const_nhds]

/-- If `F i → f` in `L1`, then `∫ x, F i x ∂Bμ → ∫ x, f x ∂Bμ`. -/
lemma tendsto_integral_of_L1' {ι} (f : α → E)
    (hfi : Integrable f Bμ.vectorMeasure.variation.ennrealToMeasure) {F : ι → α → E} {l : Filter ι}
    (hFi : ∀ᶠ i in l, Integrable (F i) Bμ.vectorMeasure.variation.ennrealToMeasure)
    (hF : Tendsto (fun i ↦ eLpNorm (F i - f) 1 Bμ.vectorMeasure.variation.ennrealToMeasure)
    l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ x, F i x ∂Bμ) l (𝓝 (∫ x, f x ∂Bμ)) := by
  refine tendsto_integral_of_L1 f hfi hFi ?_
  simp_rw [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] at hF
  exact hF

variable {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]

theorem continuousWithinAt_of_dominated {F : X → α → E} {x₀ : X} {bound : α → ℝ} {s : Set X}
    (hF_meas : ∀ᶠ x in 𝓝[s] x₀,
    AEStronglyMeasurable (F x) Bμ.vectorMeasure.variation.ennrealToMeasure)
    (h_bound : ∀ᶠ x in 𝓝[s] x₀,
    ∀ᵐ a ∂Bμ.vectorMeasure.variation.ennrealToMeasure, ‖F x a‖ ≤ bound a)
    (bound_integrable : Integrable bound Bμ.vectorMeasure.variation.ennrealToMeasure)
    (h_cont : ∀ᵐ a ∂Bμ.vectorMeasure.variation.ennrealToMeasure,
    ContinuousWithinAt (fun x => F x a) s x₀) :
    ContinuousWithinAt (fun x => ∫ a, F x a ∂Bμ) s x₀ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact continuousWithinAt_setToFun_of_dominated
      (dominatedFinMeasAdditive_weightedVectorSMul Bμ.pairing Bμ.vectorMeasure)
      hF_meas h_bound bound_integrable h_cont
  · simp [integral, hG, continuousWithinAt_const]

theorem continuousAt_of_dominated {F : X → α → E} {x₀ : X} {bound : α → ℝ}
    (hF_meas : ∀ᶠ x in 𝓝 x₀,
    AEStronglyMeasurable (F x) Bμ.vectorMeasure.variation.ennrealToMeasure)
    (h_bound : ∀ᶠ x in 𝓝 x₀,
    ∀ᵐ a ∂Bμ.vectorMeasure.variation.ennrealToMeasure, ‖F x a‖ ≤ bound a)
    (bound_integrable : Integrable bound Bμ.vectorMeasure.variation.ennrealToMeasure)
    (h_cont : ∀ᵐ a ∂Bμ.vectorMeasure.variation.ennrealToMeasure,
    ContinuousAt (fun x => F x a) x₀) :
    ContinuousAt (fun x => ∫ a, F x a ∂Bμ) x₀ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact continuousAt_setToFun_of_dominated
      (dominatedFinMeasAdditive_weightedVectorSMul Bμ.pairing Bμ.vectorMeasure)
      hF_meas h_bound bound_integrable h_cont
  · simp [integral, hG, continuousAt_const]

theorem continuousOn_of_dominated {F : X → α → E} {bound : α → ℝ} {s : Set X}
    (hF_meas : ∀ x ∈ s, AEStronglyMeasurable (F x) Bμ.vectorMeasure.variation.ennrealToMeasure)
    (h_bound : ∀ x ∈ s, ∀ᵐ a ∂Bμ.vectorMeasure.variation.ennrealToMeasure, ‖F x a‖ ≤ bound a)
    (bound_integrable : Integrable bound Bμ.vectorMeasure.variation.ennrealToMeasure)
    (h_cont : ∀ᵐ a ∂Bμ.vectorMeasure.variation.ennrealToMeasure, ContinuousOn (fun x => F x a) s) :
    ContinuousOn (fun x => ∫ a, F x a ∂Bμ) s := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact continuousOn_setToFun_of_dominated
      (dominatedFinMeasAdditive_weightedVectorSMul Bμ.pairing Bμ.vectorMeasure)
      hF_meas h_bound bound_integrable h_cont
  · simp [integral, hG, continuousOn_const]

theorem continuous_of_dominated {F : X → α → E} {bound : α → ℝ}
    (hF_meas : ∀ x, AEStronglyMeasurable (F x) Bμ.vectorMeasure.variation.ennrealToMeasure)
    (h_bound : ∀ x, ∀ᵐ a ∂Bμ.vectorMeasure.variation.ennrealToMeasure, ‖F x a‖ ≤ bound a)
    (bound_integrable : Integrable bound Bμ.vectorMeasure.variation.ennrealToMeasure)
    (h_cont : ∀ᵐ a ∂Bμ.vectorMeasure.variation.ennrealToMeasure, Continuous fun x => F x a) :
    Continuous fun x => ∫ a, F x a ∂Bμ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    exact continuous_setToFun_of_dominated
      (dominatedFinMeasAdditive_weightedVectorSMul Bμ.pairing Bμ.vectorMeasure)
      hF_meas h_bound bound_integrable h_cont
  · simp [integral, hG, continuous_const]

@[simp]
theorem integral_const (c : E) [hG : CompleteSpace G]
    [IsFiniteMeasure Bμ.vectorMeasure.variation.ennrealToMeasure] :
    ∫ _ : α, c ∂Bμ = Bμ.pairing c (Bμ.vectorMeasure univ) := by
  simp only [integral, hG]
  exact setToFun_const (dominatedFinMeasAdditive_weightedVectorSMul Bμ.pairing Bμ.vectorMeasure) _

variable {μ ν : VectorMeasure α F}

theorem integral_add_measure (B : E →L[ℝ] F →L[ℝ] G)
    (hμ : Integrable f μ.variation.ennrealToMeasure)
    (hν : Integrable f ν.variation.ennrealToMeasure) :
    ∫ x, f x ∂(VectorMeasureWithPairing.mk B (μ + ν)) =
    ∫ x, f x ∂(VectorMeasureWithPairing.mk B μ) + ∫ x, f x ∂(VectorMeasureWithPairing.mk B ν) := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  have hfi := hμ.add_measure hν
  simp_rw [integral_eq_setToFun]
  have hμν : (μ + ν).variation.ennrealToMeasure ≤
    μ.variation.ennrealToMeasure + ν.variation.ennrealToMeasure :=
    triangle_inequality_ennrealToMeasure μ ν
  have hμν_dfma1 : DominatedFinMeasAdditive
    (μ + ν).variation.ennrealToMeasure
    (weightedVectorSMul B (μ + ν) : Set α → E →L[ℝ] G) ‖B‖ :=
    dominatedFinMeasAdditive_weightedVectorSMul B (μ + ν)
  have hμν_dfma2 : DominatedFinMeasAdditive
    (μ.variation.ennrealToMeasure + ν.variation.ennrealToMeasure)
    (weightedVectorSMul B (μ + ν) : Set α → E →L[ℝ] G) ‖B‖ :=
    by simpa using (DominatedFinMeasAdditive.of_measure_le_smul one_ne_top
      (by simpa using hμν) hμν_dfma1 (norm_nonneg B))
  trans setToFun (μ.variation.ennrealToMeasure + ν.variation.ennrealToMeasure)
    (weightedVectorSMul B (μ + ν)) hμν_dfma2 f
  · refine (setToFun_congr_measure_of_integrable 1 one_ne_top (by simpa using hμν)
      hμν_dfma2 hμν_dfma1 f hfi).symm
  · have hμ_dfma : DominatedFinMeasAdditive
      (μ.variation.ennrealToMeasure + ν.variation.ennrealToMeasure)
      (weightedVectorSMul B μ : Set α → E →L[ℝ] G) ‖B‖ :=
        DominatedFinMeasAdditive.add_measure_right
        μ.variation.ennrealToMeasure ν.variation.ennrealToMeasure
        (dominatedFinMeasAdditive_weightedVectorSMul B μ) (norm_nonneg B)
    have hν_dfma : DominatedFinMeasAdditive
      (μ.variation.ennrealToMeasure + ν.variation.ennrealToMeasure)
      (weightedVectorSMul B ν : Set α → E →L[ℝ] G) ‖B‖ :=
        DominatedFinMeasAdditive.add_measure_left
        μ.variation.ennrealToMeasure ν.variation.ennrealToMeasure
        (dominatedFinMeasAdditive_weightedVectorSMul B ν) (norm_nonneg B)
    rw [← setToFun_congr_measure_of_add_right hμ_dfma
      (dominatedFinMeasAdditive_weightedVectorSMul B μ) f hfi,
      ← setToFun_congr_measure_of_add_left hν_dfma
      (dominatedFinMeasAdditive_weightedVectorSMul B ν) f hfi]
    refine setToFun_add_left' hμ_dfma hν_dfma _ (fun s _ hμνs =>
      (congr_fun (weightedVectorSMul_add_measure B μ ν) s)) f

theorem integral_neg_measure (B : E →L[ℝ] F →L[ℝ] G) :
    ∫ x, f x ∂(VectorMeasureWithPairing.mk B (-μ))
    = - ∫ x, f x ∂(VectorMeasureWithPairing.mk B μ) := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  have hBμ := dominatedFinMeasAdditive_weightedVectorSMul_neg B μ
  have lem1 : setToFun (-μ).variation.ennrealToMeasure (weightedVectorSMul B (-μ))
    (dominatedFinMeasAdditive_weightedVectorSMul B (-μ)) f = setToFun μ.variation.ennrealToMeasure
    (weightedVectorSMul B (-μ)) hBμ f := by
    congr 2; exact variation_neg μ
  rw [weightedVectorSMul_neg_measure] at hBμ
  have lem2 : setToFun μ.variation.ennrealToMeasure (weightedVectorSMul B (-μ))
    (dominatedFinMeasAdditive_weightedVectorSMul_neg B μ) f = setToFun μ.variation.ennrealToMeasure
    (-weightedVectorSMul B μ) hBμ f := by
    congr 2; exact (weightedVectorSMul_neg_measure B μ)
  simp [integral_eq_setToFun, lem1, lem2]; rw [← neg_one_smul (R := ℝ) (M := G)]
  refine setToFun_smul_left' (dominatedFinMeasAdditive_weightedVectorSMul B μ) hBμ (-1) ?_ f
  intro; simp

theorem integral_sub_measure (B : E →L[ℝ] F →L[ℝ] G)
    (hμ : Integrable f μ.variation.ennrealToMeasure)
    (hν : Integrable f ν.variation.ennrealToMeasure) :
    ∫ x, f x ∂(VectorMeasureWithPairing.mk B (μ - ν)) =
    ∫ x, f x ∂(VectorMeasureWithPairing.mk B μ) - ∫ x, f x ∂(VectorMeasureWithPairing.mk B ν) := by
  have hνn : Integrable f (- ν).variation.ennrealToMeasure := by
    simp [variation_neg]; exact hν
  simp [sub_eq_add_neg, integral_add_measure B hμ hνn, integral_neg_measure]

theorem integral_add_pairing (B C : E →L[ℝ] F →L[ℝ] G) :
    ∫ x, f x ∂(VectorMeasureWithPairing.mk (B + C) μ) =
    ∫ x, f x ∂(VectorMeasureWithPairing.mk B μ) + ∫ x, f x ∂(VectorMeasureWithPairing.mk C μ) := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  simp [integral_eq_setToFun, weightedVectorSMul_add_pairing, ← setToFun_add_left]
  apply setToFun_congr_left; simp

theorem integral_neg_pairing (B : E →L[ℝ] F →L[ℝ] G) :
    ∫ x, f x ∂(VectorMeasureWithPairing.mk (-B) μ)
    = - ∫ x, f x ∂(VectorMeasureWithPairing.mk B μ) := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  simp [integral_eq_setToFun, weightedVectorSMul_neg_pairing]
  rw [← neg_one_smul (R := ℝ) (M := G)]
  have hBμ1 := (dominatedFinMeasAdditive_weightedVectorSMul B μ)
  have hBμ2 := (dominatedFinMeasAdditive_weightedVectorSMul_neg B μ)
  rw [weightedVectorSMul_neg_measure] at hBμ2
  refine setToFun_smul_left' hBμ1 hBμ2 (-1) ?_ f
  intro; simp

theorem integral_sub_pairing (B C : E →L[ℝ] F →L[ℝ] G) :
    ∫ x, f x ∂(VectorMeasureWithPairing.mk (B - C) μ) =
    ∫ x, f x ∂(VectorMeasureWithPairing.mk B μ) - ∫ x, f x ∂(VectorMeasureWithPairing.mk C μ) := by
  simp [sub_eq_add_neg, integral_add_pairing B, integral_neg_pairing]

@[simp]
theorem integral_zero_measure (B : E →L[ℝ] F →L[ℝ] G) (f : α → E) :
    ∫ x, f x ∂(VectorMeasureWithPairing.mk B (0 : VectorMeasure α F)) = 0 := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    refine setToFun_measure_zero (dominatedFinMeasAdditive_weightedVectorSMul B 0) ?_
    simp [variation_zero]
  · simp [integral, hG]

@[simp]
theorem integral_zero_pairing (μ : VectorMeasure α F) (f : α → E) :
    ∫ x, f x ∂(VectorMeasureWithPairing.mk (0 : E →L[ℝ] F →L[ℝ] G) μ) = 0 := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG]
    by_cases hfi : Integrable f μ.variation.ennrealToMeasure
    · simp only [↓reduceDIte, hfi]
      apply L1.setToL1_zero_left' (dominatedFinMeasAdditive_weightedVectorSMul 0 μ); simp
    · simp [hfi]
  · simp [integral, hG]

@[simp]
theorem setIntegral_measure_zero {s : Set α}
    (hs : Bμ.vectorMeasure.variation.ennrealToMeasure s = 0) (f : α → E) :
    ∫ x in s, f x ∂Bμ = 0 := by
  have : Bμ.vectorMeasure.variation s = 0 := by
    by_cases hm : MeasurableSet s
    · rw [← ennrealToMeasure_apply hm]; exact hs
    · exact Bμ.vectorMeasure.variation.not_measurable' hm
  have : (Bμ.vectorMeasure.restrict s).variation = 0 := by
    simp only [restrict_comm_variation, ← univ_eq_zero]
    simp only [VectorMeasure.restrict]
    by_cases hsm : MeasurableSet s
    · simp [hsm, this]
    · simp [hsm]
  have : Bμ.vectorMeasure.restrict s = 0 :=
    eq_zero_of_zero_variation (Bμ.vectorMeasure.restrict s) this
  have : Bμ.restrict s = VectorMeasureWithPairing.mk Bμ.pairing 0 := by
    simp [VectorMeasureWithPairing.restrict]
    exact this
  exact this ▸ integral_zero_measure Bμ.pairing f

lemma integral_of_isEmpty [IsEmpty α] : ∫ x, f x ∂Bμ = 0 := by
  have lem := Bμ.vectorMeasure.eq_zero_of_isEmpty ▸ integral_zero_measure Bμ.pairing f
  rw [lem]

theorem integral_finset_sum_measure {ι} {f : α → E}
    {μ : ι → VectorMeasure α F} {s : Finset ι} (B : E →L[ℝ] F →L[ℝ] G)
    (hf : ∀ i ∈ s, Integrable f (μ i).variation.ennrealToMeasure) :
    ∫ a, f a ∂(VectorMeasureWithPairing.mk B (∑ i ∈ s, (μ i))) =
    ∑ i ∈ s, ∫ a, f a ∂(VectorMeasureWithPairing.mk B (μ i)) := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons _ t h ih =>
    rw [Finset.forall_mem_cons] at hf
    rw [Finset.sum_cons, Finset.sum_cons, ← ih hf.2]
    refine integral_add_measure B hf.1 ?_
    apply Integrable.mono_measure
    · exact (integrable_finset_sum_measure.2 hf.2)
    · refine Finset.le_sum_of_subadditive (fun (μ : VectorMeasure α F)
        => μ.variation.ennrealToMeasure) (by simp) ?_ t μ
      intro x y; exact triangle_inequality_ennrealToMeasure x y

theorem integral_finset_sum_pairing {ι} (B : ι → E →L[ℝ] F →L[ℝ] G) {s : Finset ι} :
    ∫ a, f a ∂(VectorMeasureWithPairing.mk (∑ i ∈ s, B i) μ) =
    ∑ i ∈ s, ∫ a, f a ∂(VectorMeasureWithPairing.mk (B i) μ) := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons i t h ih =>
    rw [Finset.sum_cons, Finset.sum_cons, ← ih]
    exact integral_add_pairing (B i) (∑ i ∈ t, B i)

@[simp]
theorem integral_smul_measure (B : E →L[ℝ] F →L[ℝ] G) (c : ℝ) :
    ∫ x, f x ∂(VectorMeasureWithPairing.mk B (c • μ))
    = c • ∫ x, f x ∂(VectorMeasureWithPairing.mk B μ) := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  simp [integral_eq_setToFun, ← setToFun_smul_left, weightedVectorSMul_smul_measure,
    variation_ennrealToMeasure_smul]; symm
  apply setToFun_congr_smul_measure
  simp

@[simp]
theorem integral_smul_pairing (B : E →L[ℝ] F →L[ℝ] G) (c : ℝ) :
    ∫ x, f x ∂(VectorMeasureWithPairing.mk (c • B) μ)
    = c • ∫ x, f x ∂(VectorMeasureWithPairing.mk B μ) := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  simp_rw [integral_eq_setToFun, ← setToFun_smul_left, weightedVectorSMul_smul_pairing]
  congr
  simp [norm_smul]

end Properties

end VectorMeasure
