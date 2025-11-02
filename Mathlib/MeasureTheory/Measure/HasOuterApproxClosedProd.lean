/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Characterization of a finite measure by the integrals of products of bounded functions

Given two finite families of Borel spaces `(i : ι) → X i` and `(j : κ) → Y j` satisfying
`HasOuterApproxClosed`, a finite measure `μ` over `(Π i, X i) × (Π j, Y j)` is determined by
the values `∫ p, (Π i, f i (p.1 i)) * (Π j, g j (p.2 j)) ∂μ`, for
`f : (i : ι) → X i → ℝ` and `g : (j : κ) → Y j → ℝ`
any families of bounded continuous functions.

In particular, If `μ` and `ν` and two finite measures over `Π i, X i` and `Π j, Y j` respectively,
then their product is the only finite measure `ξ` over `(Π i, X i) × (Π j, Y j)`
such that for any two families bounded continuous functions
`f : (i : ι) → X i → ℝ` and `g : (j : κ) → Y j → ℝ` we have
`∫ p, (Π i, f i (p.1 i)) * (Π j, g j (p.2 j)) ∂ξ =
(∫ x, Π i, f i (x i) ∂μ) * (∫ y, Π j, g j (y j) ∂ν)`.

We specialize these results to the cases where one of the families contains only one type.

# Main statements

* `ext_of_integral_prod_mul_prod_boundedContinuousFunction`: A finite measure on a product space is
  characterized by the integrals of products of real bounded continuous functions.
* `eq_prod_of_integral_prod_mul_prod_boundedContinuousFunction`: The product of two finite measures
  `μ` and `ν` is the only finite measure `ξ` such that for all families of real bounded continuous
  functions `f` and `g` we have
  `∫ p, (Π i, f i (p.1 i)) * (Π j, g j (p.2 j)) ∂ξ =
  (∫ x, Π i, f i (x i) ∂μ) * (∫ y, Π j, g j (y j) ∂ν)`.

# Tags

bounded continuous function, product measure
-/

open BoundedContinuousFunction MeasureTheory Topology Filter Set ENNReal NNReal MeasurableSpace
open scoped Topology ENNReal NNReal

namespace Measure

variable {ι κ Z T : Type*} [Fintype ι] [Fintype κ] {X : ι → Type*} {Y : κ → Type*}
  {mX : ∀ i, MeasurableSpace (X i)} [∀ i, TopologicalSpace (X i)] [∀ i, BorelSpace (X i)]
  [∀ i, HasOuterApproxClosed (X i)]
  {mY : ∀ j, MeasurableSpace (Y j)} [∀ j, TopologicalSpace (Y j)] [∀ j, BorelSpace (Y j)]
  [∀ j, HasOuterApproxClosed (Y j)]
  {mZ : MeasurableSpace Z} [TopologicalSpace Z] [BorelSpace Z] [HasOuterApproxClosed Z]
  {mT : MeasurableSpace T} [TopologicalSpace T] [BorelSpace T] [HasOuterApproxClosed T]

/-- A finite measure on a product space is characterized by the integrals of products of nonnegative
bounded continuous functions. -/
lemma ext_of_lintegral_prod_mul_prod_boundedContinuousFunction
    {μ ν : Measure ((Π i, X i) × (Π j, Y j))} [IsFiniteMeasure μ]
    (h : ∀ (f : (i : ι) → X i →ᵇ ℝ≥0) (g : (j : κ) → Y j →ᵇ ℝ≥0),
      ∫⁻ p, (∏ i, f i (p.1 i)) * ∏ j, g j (p.2 j) ∂μ =
      ∫⁻ p, (∏ i, f i (p.1 i)) * ∏ j, g j (p.2 j) ∂ν) :
    μ = ν := by
  have hμν : μ univ = ν univ := by convert h 1 1 <;> simp
  have : IsFiniteMeasure ν := ⟨by simp [← hμν]⟩
  let π : Set (Set ((Π i, X i) × (Π j, Y j))) :=
    Set.image2 (fun s t ↦ s ×ˢ t) (Set.univ.pi '' (Set.univ.pi fun _ ↦ {s | IsClosed s}))
      (Set.univ.pi '' (Set.univ.pi fun _ ↦ {t | IsClosed t}))
  have hπ1 : IsPiSystem π := by
    rintro - ⟨-, ⟨s₁, hs₁, rfl⟩, -, ⟨t₁, ht₁, rfl⟩, rfl⟩ -
      ⟨-, ⟨s₂, hs₂, rfl⟩, -, ⟨t₂, ht₂, rfl⟩, rfl⟩ -
    refine ⟨_, ⟨fun i ↦ s₁ i ∩ s₂ i, ?_, rfl⟩, _, ⟨fun j ↦ t₁ j ∩ t₂ j, ?_, rfl⟩, ?_⟩
    · simp only [Set.mem_pi, mem_univ, mem_setOf_eq, forall_const] at hs₁ hs₂ ⊢
      exact fun i ↦ (hs₁ i).inter (hs₂ i)
    · simp only [Set.mem_pi, mem_univ, mem_setOf_eq, forall_const] at ht₁ ht₂ ⊢
      exact fun j ↦ (ht₁ j).inter (ht₂ j)
    simp [Set.pi_inter_distrib, Set.prod_inter_prod]
  have hπ2 : Prod.instMeasurableSpace = generateFrom π := by
    rw [← generateFrom_eq_prod (C := Set.univ.pi '' (Set.univ.pi fun _ ↦ {s | IsClosed s}))
      (D := Set.univ.pi '' (Set.univ.pi fun _ ↦ {t | IsClosed t}))]
    · rw [← generateFrom_eq_pi (C := fun _ ↦ {s | IsClosed s})]
      · simp [BorelSpace.measurable_eq, borel_eq_generateFrom_isClosed]
      · exact fun _ ↦ ⟨fun _ ↦ Set.univ, fun _ ↦ isClosed_univ, iUnion_const _⟩
    · rw [← generateFrom_eq_pi (C := fun _ ↦ {t | IsClosed t})]
      · simp [BorelSpace.measurable_eq, borel_eq_generateFrom_isClosed]
      · exact fun _ ↦ ⟨fun _ ↦ Set.univ, fun _ ↦ isClosed_univ, iUnion_const _⟩
    · exact ⟨fun _ ↦ Set.univ, fun _ ↦ ⟨fun _ ↦ Set.univ, by simp, by simp⟩, iUnion_const _⟩
    · exact ⟨fun _ ↦ Set.univ, fun _ ↦ ⟨fun _ ↦ Set.univ, by simp, by simp⟩, iUnion_const _⟩
  refine ext_of_generate_finite π hπ2 hπ1 ?_ hμν
  rintro - ⟨-, ⟨s, hs, rfl⟩, -, ⟨t, ht, rfl⟩, rfl⟩
  simp only [Set.mem_pi, mem_univ, mem_setOf_eq, forall_const] at hs ht
  have (p : (Π i, X i) × (Π j, Y j)) := ENNReal.continuous_coe.tendsto _ |>.comp <|
    (tendsto_finset_prod Finset.univ (fun i _ ↦ tendsto_pi_nhds.1
      (HasOuterApproxClosed.tendsto_apprSeq (hs i)) (p.1 i))).mul
    (tendsto_finset_prod Finset.univ (fun j _ ↦ tendsto_pi_nhds.1
      (HasOuterApproxClosed.tendsto_apprSeq (ht j)) (p.2 j)))
  have hp1 (x : Π i, X i) : ∏ i, (s i).indicator (fun _ ↦ (1 : ℝ≥0)) (x i) =
      (Set.univ.pi s).indicator 1 x := by
    simp only [Set.indicator, Set.mem_pi, mem_univ, forall_const, Pi.ofNat_apply]
    split_ifs with hy
    · simp only [Set.mem_pi, mem_univ, forall_const] at hy
      exact Finset.prod_eq_one (by simpa)
    · simpa [Finset.prod_eq_zero_iff] using hy
  have hp2 (y : Π j, Y j) : ∏ j, (t j).indicator (fun _ ↦ (1 : ℝ≥0)) (y j) =
      (Set.univ.pi t).indicator 1 y := by
    simp only [Set.indicator, Set.mem_pi, mem_univ, forall_const, Pi.ofNat_apply]
    split_ifs with hy
    · simp only [Set.mem_pi, mem_univ, forall_const] at hy
      exact Finset.prod_eq_one (by simpa)
    · simpa [Finset.prod_eq_zero_iff] using hy
  simp_rw [hp1, hp2, ← Set.indicator_prod_one, Prod.eta] at this
  have h1 : Tendsto (fun n ↦ ∫⁻ p, ((∏ i, (hs i).apprSeq n (p.1 i)) *
        ∏ j, (ht j).apprSeq n (p.2 j) : ℝ≥0) ∂μ)
      atTop (𝓝 (∫⁻ p, (((Set.univ.pi s) ×ˢ (Set.univ.pi t)).indicator 1 p : ℝ≥0) ∂μ)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence 1
      (Eventually.of_forall <| by fun_prop) (Eventually.of_forall fun n ↦ ae_of_all _ fun ω ↦ ?_)
      (by simp) (ae_of_all _ this)
    grw [Finset.prod_le_one (by simp), Finset.prod_le_one (by simp)]
    · simp
    · exact fun j _ ↦ HasOuterApproxClosed.apprSeq_apply_le_one (ht j) _ _
    · exact fun i _ ↦ HasOuterApproxClosed.apprSeq_apply_le_one (hs i) _ _
  have h2 : Tendsto (fun n ↦ ∫⁻ p, ((∏ i, (hs i).apprSeq n (p.1 i)) *
        ∏ j, (ht j).apprSeq n (p.2 j) : ℝ≥0) ∂μ)
      atTop (𝓝 (∫⁻ p, (((Set.univ.pi s) ×ˢ (Set.univ.pi t)).indicator 1 p : ℝ≥0) ∂ν)) := by
    simp_rw [coe_mul, h]
    refine tendsto_lintegral_filter_of_dominated_convergence 1
      (Eventually.of_forall <| by fun_prop) (Eventually.of_forall fun _ ↦ ae_of_all _ fun _ ↦ ?_)
      (by simp) (ae_of_all _ this)
    grw [Finset.prod_le_one (by simp), Finset.prod_le_one (by simp)]
    · simp
    · exact fun j _ ↦ HasOuterApproxClosed.apprSeq_apply_le_one (ht j) _ _
    · exact fun i _ ↦ HasOuterApproxClosed.apprSeq_apply_le_one (hs i) _ _
  convert tendsto_nhds_unique h1 h2 <;>
    simp [(MeasurableSet.univ_pi (fun i ↦ (hs i).measurableSet)).prod
      (.univ_pi (fun j ↦ (ht j).measurableSet))]

/-- A finite measure on a product space is characterized by the integrals of products of real
bounded continuous functions. -/
lemma ext_of_integral_prod_mul_prod_boundedContinuousFunction
    {μ ν : Measure ((Π i, X i) × (Π j, Y j))} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (f : (i : ι) → X i →ᵇ ℝ) (g : (j : κ) → Y j →ᵇ ℝ),
      ∫ p, (∏ i, f i (p.1 i)) * ∏ j, g j (p.2 j) ∂μ =
      ∫ p, (∏ i, f i (p.1 i)) * ∏ j, g j (p.2 j) ∂ν) :
    μ = ν := by
  refine ext_of_lintegral_prod_mul_prod_boundedContinuousFunction fun f g ↦ ?_
  rw [← toReal_eq_toReal_iff']
  · simp only [coe_finset_prod]
    have {μ : Measure ((Π i, X i) × Π j, Y j)} :
        (∫⁻ p, (∏ i, (f i (p.1 i) : ℝ≥0∞)) * ∏ j, (g j (p.2 j) : ℝ≥0∞) ∂μ).toReal =
          ∫ p, (∏ i, (f i (p.1 i)).toReal) * ∏ j, (g j (p.2 j)).toReal ∂μ := by
      rw [integral_eq_lintegral_of_nonneg_ae]
      · simp [Finset.prod_nonneg, ofReal_prod_of_nonneg]
      · exact Eventually.of_forall fun _ ↦ by positivity
      exact AEStronglyMeasurable.mul
        (Finset.aestronglyMeasurable_fun_prod _ fun _ _ ↦
          continuous_coe.aestronglyMeasurable.comp_measurable (by fun_prop))
        (Finset.aestronglyMeasurable_fun_prod _ fun _ _ ↦
          continuous_coe.aestronglyMeasurable.comp_measurable (by fun_prop))
    simp_rw [this]
    exact h (fun i ↦ ⟨⟨fun x ↦ (f i x), by fun_prop⟩, (f i).map_bounded'⟩)
      (fun j ↦ ⟨⟨fun y ↦ (g j y), by fun_prop⟩, (g j).map_bounded'⟩)
  · convert (lintegral_lt_top_of_nnreal μ
      ((∏ i, (f i).compContinuous ⟨Function.eval i ∘ Prod.fst, by fun_prop⟩) *
      (∏ j, (g j).compContinuous ⟨Function.eval j ∘ Prod.snd, by fun_prop⟩))).ne
    simp
  · convert (lintegral_lt_top_of_nnreal ν
      ((∏ i, (f i).compContinuous ⟨Function.eval i ∘ Prod.fst, by fun_prop⟩) *
      (∏ j, (g j).compContinuous ⟨Function.eval j ∘ Prod.snd, by fun_prop⟩))).ne
    simp

lemma ext_of_integral_prod_mul_prod_boundedContinuousFunction'
    {μ ν : Measure ((Π i, X i) × (Π j, Y j))} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (f : (Π i, X i) →ᵇ ℝ) (g : (Π j, Y j) →ᵇ ℝ),
      ∫ p, f p.1 * g p.2 ∂μ = ∫ p, f p.1 * g p.2 ∂ν) :
    μ = ν := by
  refine ext_of_integral_prod_mul_prod_boundedContinuousFunction fun f g ↦ ?_
  convert h (∏ i, (f i).compContinuous ⟨Function.eval i, by fun_prop⟩)
    (∏ j, (g j).compContinuous ⟨Function.eval j, by fun_prop⟩) <;> simp

/-- The product of two finite measures `μ` and `ν` is the only finite measure `ξ` such that
for all families of real bounded continuous functions `f` and `g` we have
`∫ p, (Π i, f i (p.1 i)) * (Π j, g j (p.2 j)) ∂ξ =
(∫ x, Π i, f i (x i) ∂μ) * (∫ y, Π j, g j (y j) ∂ν)`. -/
lemma eq_prod_of_integral_prod_mul_prod_boundedContinuousFunction {μ : Measure (Π i, X i)}
    {ν : Measure (Π j, Y j)} {ξ : Measure ((Π i, X i) × (Π j, Y j))}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ]
    (h : ∀ (f : (i : ι) → X i →ᵇ ℝ) (g : (j : κ) → Y j →ᵇ ℝ),
      ∫ p, (∏ i, f i (p.1 i)) * (∏ j, g j (p.2 j)) ∂ξ =
      (∫ x, ∏ i, f i (x i) ∂μ) * (∫ y, ∏ j, g j (y j) ∂ν)) :
    ξ = μ.prod ν :=
  ext_of_integral_prod_mul_prod_boundedContinuousFunction fun f g ↦ by rw [h, ← integral_prod_mul]

lemma eq_prod_of_integral_prod_mul_prod_boundedContinuousFunction' {μ : Measure (Π i, X i)}
    {ν : Measure (Π j, Y j)} {ξ : Measure ((Π i, X i) × (Π j, Y j))}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ]
    (h : ∀ (f : (Π i, X i) →ᵇ ℝ) (g : (Π j, Y j) →ᵇ ℝ),
      ∫ p, f p.1 * g p.2 ∂ξ = (∫ x, f x ∂μ) * (∫ y, g y ∂ν)) :
    ξ = μ.prod ν :=
  ext_of_integral_prod_mul_prod_boundedContinuousFunction' fun f g ↦ by rw [h, ← integral_prod_mul]

lemma ext_of_integral_prod_mul_boundedContinuousFunction {μ ν : Measure ((Π i, X i) × T)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (f : (i : ι) → X i →ᵇ ℝ) (g : T →ᵇ ℝ),
      ∫ p, (∏ i, f i (p.1 i)) * g p.2 ∂μ = ∫ p, (∏ i, f i (p.1 i)) * g p.2 ∂ν) :
    μ = ν := by
  let e : ((Π i, X i) × T) ≃ᵐ ((Π i, X i) × (Unit → T)) :=
    { toFun p := ⟨fun i ↦ p.1 i, fun _ ↦ p.2⟩
      invFun p := ⟨fun i ↦ p.1 i, p.2 ()⟩
      left_inv p := by simp
      right_inv p := by simp
      measurable_toFun := by simp; fun_prop
      measurable_invFun := by simp; fun_prop }
  rw [← e.map_measurableEquiv_injective.eq_iff]
  refine ext_of_integral_prod_mul_prod_boundedContinuousFunction fun f g ↦ ?_
  rw [integral_map_equiv, integral_map_equiv]
  simpa [e] using h f (g ())

lemma ext_of_integral_prod_mul_boundedContinuousFunction' {μ ν : Measure ((Π i, X i) × T)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (f : (Π i, X i) →ᵇ ℝ) (g : T →ᵇ ℝ),
      ∫ p, f p.1 * g p.2 ∂μ = ∫ p, f p.1 * g p.2 ∂ν) :
    μ = ν := by
  refine ext_of_integral_prod_mul_boundedContinuousFunction fun f g ↦ ?_
  convert h (∏ i, (f i).compContinuous ⟨Function.eval i, by fun_prop⟩) g <;> simp

lemma eq_prod_of_integral_prod_mul_boundedContinuousFunction {μ : Measure (Π i, X i)}
    {ν : Measure T} {ξ : Measure ((Π i, X i) × T)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ]
    (h : ∀ (f : (i : ι) → X i →ᵇ ℝ) (g : T →ᵇ ℝ),
      ∫ p, (∏ i, f i (p.1 i)) * g p.2 ∂ξ = (∫ x, ∏ i, f i (x i) ∂μ) * (∫ t, g t ∂ν)) :
    ξ = μ.prod ν :=
  ext_of_integral_prod_mul_boundedContinuousFunction fun f g ↦ by rw [h, ← integral_prod_mul]

lemma eq_prod_of_integral_prod_mul_boundedContinuousFunction' {μ : Measure (Π i, X i)}
    {ν : Measure T} {ξ : Measure ((Π i, X i) × T)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ]
    (h : ∀ (f : (Π i, X i) →ᵇ ℝ) (g : T →ᵇ ℝ),
      ∫ p, f p.1 * g p.2 ∂ξ = (∫ x, f x ∂μ) * (∫ t, g t ∂ν)) :
    ξ = μ.prod ν :=
  ext_of_integral_prod_mul_boundedContinuousFunction' fun f g ↦ by rw [h, ← integral_prod_mul]

lemma ext_of_integral_mul_prod_boundedContinuousFunction {μ ν : Measure (Z × (Π j, Y j))}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (f : Z →ᵇ ℝ) (g : (j : κ) → Y j →ᵇ ℝ),
      ∫ p, f p.1 * ∏ j, g j (p.2 j) ∂μ = ∫ p, f p.1 * ∏ j, g j (p.2 j) ∂ν) :
    μ = ν := by
  let e : (Z × (Π i, Y i)) ≃ᵐ ((Π i, Y i) × Z) :=
    { toEquiv := Equiv.prodComm _ _
      measurable_toFun := measurable_swap
      measurable_invFun := measurable_swap }
  rw [← e.map_measurableEquiv_injective.eq_iff]
  refine ext_of_integral_prod_mul_boundedContinuousFunction fun f g ↦ ?_
  rw [integral_map_equiv, integral_map_equiv]
  simpa [e, mul_comm] using h g f

lemma ext_of_integral_mul_prod_boundedContinuousFunction' {μ ν : Measure (Z × (Π i, Y i))}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (f : Z →ᵇ ℝ) (g : (Π j, Y j) →ᵇ ℝ), ∫ p, f p.1 * g p.2 ∂μ = ∫ p, f p.1 * g p.2 ∂ν) :
    μ = ν := by
  refine ext_of_integral_mul_prod_boundedContinuousFunction fun f g ↦ ?_
  convert h f (∏ j, (g j).compContinuous ⟨Function.eval j, by fun_prop⟩) <;> simp

lemma eq_prod_of_integral_mul_prod_boundedContinuousFunction {μ : Measure Z}
    {ν : Measure (Π j, Y j)} {ξ : Measure (Z × (Π j, Y j))}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ]
    (h : ∀ (f : Z →ᵇ ℝ) (g : (j : κ) → Y j →ᵇ ℝ),
      ∫ p, f p.1 * (∏ j, g j (p.2 j)) ∂ξ = (∫ z, f z ∂μ) * (∫ y, ∏ j, g j (y j) ∂ν)) :
    ξ = μ.prod ν :=
  ext_of_integral_mul_prod_boundedContinuousFunction fun f g ↦ by rw [h, ← integral_prod_mul]

lemma eq_prod_of_integral_mul_prod_boundedContinuousFunction' {μ : Measure Z}
    {ν : Measure (Π j, Y j)} {ξ : Measure (Z × (Π j, Y j))}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ]
    (h : ∀ (f : Z →ᵇ ℝ) (g : (Π j, Y j) →ᵇ ℝ),
      ∫ p, f p.1 * g p.2 ∂ξ = (∫ z, f z ∂μ) * (∫ y, g y ∂ν)) :
    ξ = μ.prod ν :=
  ext_of_integral_mul_prod_boundedContinuousFunction' fun f g ↦ by rw [h, ← integral_prod_mul]

/-- A finite measure on a product space is characterized by the integrals of products of real and
bounded continuous functions. -/
lemma ext_of_integral_mul_boundedContinuousFunction {μ ν : Measure (Z × T)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (f : Z →ᵇ ℝ) (g : T →ᵇ ℝ), ∫ p, f p.1 * g p.2 ∂μ = ∫ p, f p.1 * g p.2 ∂ν) :
    μ = ν := by
  let e : (Z × T) ≃ᵐ ((Unit → Z) × (Unit → T)) :=
    { toFun p := ⟨fun _ ↦ p.1, fun _ ↦ p.2⟩
      invFun p := ⟨p.1 (), p.2 ()⟩
      left_inv p := by simp
      right_inv p := by simp
      measurable_toFun := by simp; fun_prop
      measurable_invFun := by simp; fun_prop }
  rw [← e.map_measurableEquiv_injective.eq_iff]
  refine ext_of_integral_prod_mul_prod_boundedContinuousFunction fun f g ↦ ?_
  rw [integral_map_equiv, integral_map_equiv]
  simpa [e] using h (f ()) (g ())

/-- The product of two finite measures μ and ν is the only finite measure ξ such that for all real
bounded continuous functions f and g we have ∫ z, f z.1 * g z.2 ∂ξ = ∫ x, f x ∂μ * ∫ y, g y ∂ν. -/
lemma eq_prod_of_integral_mul_boundedContinuousFunction {μ : Measure Z}
    {ν : Measure T} {ξ : Measure (Z × T)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ]
    (h : ∀ (f : Z →ᵇ ℝ) (g : T →ᵇ ℝ), ∫ p, f p.1 * g p.2 ∂ξ = (∫ z, f z ∂μ) * (∫ t, g t ∂ν)) :
    ξ = μ.prod ν :=
  ext_of_integral_mul_boundedContinuousFunction fun f g ↦ by rw [h, ← integral_prod_mul]

end Measure
