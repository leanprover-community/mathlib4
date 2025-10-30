/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Characterization of a finite measure by the integrals of products of bounded functions

Given two Borel spaces `X` and `Y` satisfying `HasOuterApproxClosed`, a finite measure `μ`
over `X × Y` is determined by the values `∫ z, f z.1 * g z.2 ∂μ`, for `f : X → ℝ` and `g : Y → ℝ`
any bounded continuous functions.

In particular, If `μ` and `ν` and two finite measures over `X` and `Y` respectively, then their
product is the only finite measure `ξ` over `X × Y` such that for any two bounded continuous
functions `f : X → ℝ` and `g : Y → ℝ` we have
`∫ z, f z.1 * g z.2 ∂ξ = (∫ x, f x ∂μ) * (∫ y, g y ∂ν)`.

# Main statements

* `ext_of_integral_mul_boundedContinuousFunction`: A finite measure on a product space is
  characterized by the integrals of products of real bounded continuous functions.
* `eq_prod_of_integral_mul_boundedContinuousFunction`: The product of two finite measures `μ` and
  `ν` is the only finite measure `ξ` such that for all real bounded continuous functions
  `f` and `g` we have `∫ z, f z.1 * g z.2 ∂ξ = ∫ x, f x ∂μ * ∫ y, g y ∂ν`.

# Tags

bounded continuous function, product measure
-/

open BoundedContinuousFunction MeasureTheory Topology Filter Set ENNReal NNReal MeasurableSpace
open scoped Topology ENNReal NNReal

namespace Measure

variable {X Y : Type*}
  {mX : MeasurableSpace X} [TopologicalSpace X] [BorelSpace X] [HasOuterApproxClosed X]
  {mY : MeasurableSpace Y} [TopologicalSpace Y] [BorelSpace Y] [HasOuterApproxClosed Y]
  {μ ν : Measure (X × Y)}

/-- A finite measure on a product space is characterized by the integrals of products of
bounded nonnegative continuous functions. -/
lemma ext_of_lintegral_mul_boundedContinuousFunction [IsFiniteMeasure μ]
    (h : ∀ (f : X →ᵇ ℝ≥0) (g : Y →ᵇ ℝ≥0),
      ∫⁻ z, f z.1 * g z.2 ∂μ = ∫⁻ z, f z.1 * g z.2 ∂ν) :
    μ = ν := by
  have hμν : μ univ = ν univ := by convert h 1 1 <;> simp
  have : IsFiniteMeasure ν := ⟨by simp [← hμν]⟩
  let π : Set (Set (X × Y)) :=
    {s | ∃ (F : Set X) (G : Set Y), IsClosed F ∧ IsClosed G ∧ s = F ×ˢ G}
  have hπ1 : IsPiSystem π := by
    rintro - ⟨s₁, s₂, hs₁, hs₂, rfl⟩ - ⟨t₁, t₂, ht₁, ht₂, rfl⟩ -
    exact ⟨s₁ ∩ t₁, s₂ ∩ t₂, hs₁.inter ht₁, hs₂.inter ht₂, Set.prod_inter_prod⟩
  have hπ2 : mX.prod mY = generateFrom π := by
    refine le_antisymm ?_ (generateFrom_le ?_)
    · simp_rw [BorelSpace.measurable_eq, borel_eq_generateFrom_isClosed, MeasurableSpace.prod,
        comap_generateFrom]
      refine sup_le (generateFrom_le ?_) (generateFrom_le ?_)
      · rintro - ⟨s, hs, rfl⟩
        exact measurableSet_generateFrom ⟨s, Set.univ, hs, isClosed_univ, by rw [Set.prod_univ]⟩
      · rintro - ⟨t, ht, rfl⟩
        exact measurableSet_generateFrom ⟨Set.univ, t, isClosed_univ, ht, by rw [Set.univ_prod]⟩
    · rintro - ⟨s₁, s₂, hs₁, hs₂, rfl⟩
      exact hs₁.measurableSet.prod hs₂.measurableSet
  refine ext_of_generate_finite π hπ2 hπ1 ?_ hμν
  rintro - ⟨s₁, s₂, hs₁, hs₂, rfl⟩
  have (z : X × Y) := ENNReal.continuous_coe.tendsto _ |>.comp <|
    (tendsto_pi_nhds.1 (HasOuterApproxClosed.tendsto_apprSeq hs₁) z.1).mul
    (tendsto_pi_nhds.1 (HasOuterApproxClosed.tendsto_apprSeq hs₂) z.2)
  simp_rw [show (fun _ ↦ 1 : X → ℝ≥0) = 1 from rfl, show (fun _ ↦ 1 : Y → ℝ≥0) = 1 from rfl,
    ← Set.indicator_prod_one] at this
  have h1 : Tendsto (fun n ↦ ∫⁻ z, (hs₁.apprSeq n z.1 * hs₂.apprSeq n z.2 : ℝ≥0) ∂μ)
      atTop (𝓝 (∫⁻ z, ((s₁ ×ˢ s₂).indicator 1 z : ℝ≥0) ∂μ)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence 1
      (Eventually.of_forall <| by fun_prop) (Eventually.of_forall fun n ↦ ae_of_all _ fun ω ↦ ?_)
      (by simp) (ae_of_all _ this)
    grw [HasOuterApproxClosed.apprSeq_apply_le_one, HasOuterApproxClosed.apprSeq_apply_le_one]
    simp
  have h2 : Tendsto (fun n ↦ ∫⁻ z, (hs₁.apprSeq n z.1 * hs₂.apprSeq n z.2 : ℝ≥0) ∂μ)
      atTop (𝓝 (∫⁻ z, ((s₁ ×ˢ s₂).indicator 1 z : ℝ≥0) ∂ν)) := by
    simp_rw [coe_mul, h]
    refine tendsto_lintegral_filter_of_dominated_convergence 1
      (Eventually.of_forall <| by fun_prop) (Eventually.of_forall fun n ↦ ae_of_all _ fun ω ↦ ?_)
      (by simp) (ae_of_all _ this)
    grw [HasOuterApproxClosed.apprSeq_apply_le_one, HasOuterApproxClosed.apprSeq_apply_le_one]
    simp
  convert tendsto_nhds_unique h1 h2 <;> simp [hs₁.measurableSet.prod hs₂.measurableSet]

/-- A finite measure on a product space is characterized by the integrals of products of
real and bounded continuous functions. -/
lemma ext_of_integral_mul_boundedContinuousFunction [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (f : X →ᵇ ℝ) (g : Y →ᵇ ℝ),
      ∫ z, f z.1 * g z.2 ∂μ = ∫ z, f z.1 * g z.2 ∂ν) :
    μ = ν := by
  refine ext_of_lintegral_mul_boundedContinuousFunction fun f g ↦ ?_
  apply (toReal_eq_toReal_iff' (lintegral_lt_top_of_nnreal μ
    ((f.compContinuous ⟨@Prod.fst X Y, continuous_fst⟩) *
      (g.compContinuous ⟨@Prod.snd X Y, continuous_snd⟩))).ne
    (lintegral_lt_top_of_nnreal ν
    ((f.compContinuous ⟨@Prod.fst X Y, continuous_fst⟩) *
      (g.compContinuous ⟨@Prod.snd X Y, continuous_snd⟩))).ne).1
  simp only [BoundedContinuousFunction.coe_mul, coe_compContinuous, ContinuousMap.coe_mk,
    Pi.mul_apply, Function.comp_apply, ENNReal.coe_mul]
  have {μ : Measure (X × Y)} :
      (∫⁻ z, f z.1 * g z.2 ∂μ).toReal = ∫ z, (f z.1).toReal * (g z.2).toReal ∂μ := by
    rw [integral_eq_lintegral_of_nonneg_ae]
    · simp
    · exact Eventually.of_forall fun _ ↦ by positivity
    exact AEStronglyMeasurable.mul
      (continuous_coe.aestronglyMeasurable.comp_measurable (by fun_prop))
      (continuous_coe.aestronglyMeasurable.comp_measurable (by fun_prop))
  simp_rw [this]
  exact h ⟨⟨fun x ↦ (f x), by fun_prop⟩, f.map_bounded'⟩
    ⟨⟨fun x ↦ (g x), by fun_prop⟩, g.map_bounded'⟩

variable {μ : Measure X} [IsFiniteMeasure μ] {ν : Measure Y} [IsFiniteMeasure ν]
  {ξ : Measure (X × Y)} [IsFiniteMeasure ξ]

/-- The product of two finite measures `μ` and `ν` is the only finite measure `ξ` such that
for all real bounded continuous functions `f` and `g` we have
`∫ z, f z.1 * g z.2 ∂ξ = ∫ x, f x ∂μ * ∫ y, g y ∂ν`. -/
lemma eq_prod_of_integral_mul_boundedContinuousFunction
    (h : ∀ (f : X →ᵇ ℝ) (g : Y →ᵇ ℝ),
      ∫ z, f z.1 * g z.2 ∂ξ = (∫ x, f x ∂μ) * (∫ y, g y ∂ν)) :
    ξ = μ.prod ν :=
  ext_of_integral_mul_boundedContinuousFunction fun f g ↦ by rw [h, integral_prod_mul]

variable {X ι : Type*} [Fintype ι] {Y : ι → Type*}
  {mX : MeasurableSpace X} [TopologicalSpace X] [BorelSpace X] [HasOuterApproxClosed X]
  {mY : ∀ i, MeasurableSpace (Y i)} [∀ i, TopologicalSpace (Y i)] [∀ i, BorelSpace (Y i)]
  [∀ i, HasOuterApproxClosed (Y i)] {μ ν : Measure (X × (Π i, Y i))}

lemma omg [IsFiniteMeasure μ]
    (h : ∀ (f : X →ᵇ ℝ≥0) (g : (i : ι) → Y i →ᵇ ℝ≥0),
      ∫⁻ z, f z.1 * ∏ i, g i (z.2 i) ∂μ = ∫⁻ z, f z.1 * ∏ i, g i (z.2 i) ∂ν) :
    μ = ν := by
  have hμν : μ univ = ν univ := by convert h 1 1 <;> simp
  have : IsFiniteMeasure ν := ⟨by simp [← hμν]⟩
  let π : Set (Set (X × (Π i, Y i))) :=
    {s | ∃ (F : Set X) (G : (i : ι) → Set (Y i)), IsClosed F ∧ (∀ i, IsClosed (G i)) ∧
      s = F ×ˢ (Set.univ.pi G)}
  have hπ1 : IsPiSystem π := by
    rintro - ⟨s₁, s₂, hs₁, hs₂, rfl⟩ - ⟨t₁, t₂, ht₁, ht₂, rfl⟩ -
    refine ⟨s₁ ∩ t₁, fun i ↦ s₂ i ∩ t₂ i, hs₁.inter ht₁, fun i ↦ (hs₂ i).inter (ht₂ i), ?_⟩
    rw [Set.prod_inter_prod, ← Set.pi_inter_distrib]
  have hπ2 : mX.prod (.pi (m := mY)) = generateFrom π := by
    refine le_antisymm ?_ (generateFrom_le ?_)
    · simp_rw [MeasurableSpace.pi, BorelSpace.measurable_eq, borel_eq_generateFrom_isClosed,
        MeasurableSpace.prod, MeasurableSpace.comap_iSup, comap_generateFrom]
      refine sup_le (generateFrom_le ?_) (iSup_le  fun i ↦ generateFrom_le ?_)
      · rintro - ⟨s, hs, rfl⟩
        exact measurableSet_generateFrom ⟨s, fun _ ↦ Set.univ, hs, fun _ ↦ isClosed_univ,
          by simp [Set.prod_univ]⟩
      · rintro - ⟨-, ⟨s, hs, rfl⟩, rfl⟩
        classical
        refine measurableSet_generateFrom
          ⟨Set.univ, fun j ↦ if hj : j = i then hj ▸ s else Set.univ, isClosed_univ, fun j ↦ ?_, ?_⟩
        · obtain rfl | hj := eq_or_ne j i
          · simpa
          · simp [hj]
        · rw [← Set.univ_prod]
          congr with y
          simp only [mem_preimage, Set.mem_pi, mem_univ, forall_const]
          refine ⟨fun h j ↦ ?_, fun h ↦ ?_⟩
          · obtain rfl | hj := eq_or_ne j i
            · simpa
            · simp [hj]
          · convert h i
            simp
    · rintro - ⟨s₁, s₂, hs₁, hs₂, rfl⟩
      exact hs₁.measurableSet.prod (.univ_pi (fun i ↦ (hs₂ i).measurableSet))
  refine ext_of_generate_finite π hπ2 hπ1 ?_ hμν
  rintro - ⟨s₁, s₂, hs₁, hs₂, rfl⟩
  have (z : X × (Π i, Y i)) := ENNReal.continuous_coe.tendsto _ |>.comp <|
    (tendsto_pi_nhds.1 (HasOuterApproxClosed.tendsto_apprSeq hs₁) z.1).mul
    (tendsto_finset_prod Finset.univ (fun i _ ↦ tendsto_pi_nhds.1
      (HasOuterApproxClosed.tendsto_apprSeq (hs₂ i)) (z.2 i)))
  have hp (y : Π i, Y i) : ∏ i, (s₂ i).indicator (fun _ ↦ (1 : ℝ≥0)) (y i) =
      (Set.univ.pi s₂).indicator 1 y := by
    simp only [Set.indicator, Set.mem_pi, mem_univ, forall_const, Pi.ofNat_apply]
    split_ifs with hy
    · simp only [Set.mem_pi, mem_univ, forall_const] at hy
      exact Finset.prod_eq_one (by simpa)
    · simpa [Finset.prod_eq_zero_iff] using hy
  simp_rw [show (fun _ ↦ 1 : X → ℝ≥0) = 1 from rfl, hp, ← Set.indicator_prod_one] at this
  have h1 : Tendsto (fun n ↦ ∫⁻ z, (hs₁.apprSeq n z.1 * ∏ i, (hs₂ i).apprSeq n (z.2 i) : ℝ≥0) ∂μ)
      atTop (𝓝 (∫⁻ z, ((s₁ ×ˢ (Set.univ.pi s₂)).indicator 1 z : ℝ≥0) ∂μ)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence 1
      (Eventually.of_forall <| by fun_prop) (Eventually.of_forall fun n ↦ ae_of_all _ fun ω ↦ ?_)
      (by simp) (ae_of_all _ this)
    grw [HasOuterApproxClosed.apprSeq_apply_le_one, Finset.prod_le_one]
    · simp
    · simp
    · exact fun i _ ↦ HasOuterApproxClosed.apprSeq_apply_le_one (hs₂ i) _ _
  have h2 : Tendsto (fun n ↦ ∫⁻ z, (hs₁.apprSeq n z.1 * ∏ i, (hs₂ i).apprSeq n (z.2 i) : ℝ≥0) ∂μ)
      atTop (𝓝 (∫⁻ z, ((s₁ ×ˢ (Set.univ.pi s₂)).indicator 1 z : ℝ≥0) ∂ν)) := by
    simp_rw [coe_mul, h]
    refine tendsto_lintegral_filter_of_dominated_convergence 1
      (Eventually.of_forall <| by fun_prop) (Eventually.of_forall fun n ↦ ae_of_all _ fun ω ↦ ?_)
      (by simp) (ae_of_all _ this)
    grw [HasOuterApproxClosed.apprSeq_apply_le_one, Finset.prod_le_one]
    · simp
    · simp
    · exact fun i _ ↦ HasOuterApproxClosed.apprSeq_apply_le_one (hs₂ i) _ _
  convert tendsto_nhds_unique h1 h2 <;>
    simp [hs₁.measurableSet.prod (.univ_pi (fun i ↦ (hs₂ i).measurableSet))]

lemma omg' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (f : X →ᵇ ℝ) (g : (i : ι) → Y i →ᵇ ℝ),
      ∫ z, f z.1 * ∏ i, g i (z.2 i) ∂μ = ∫ z, f z.1 * ∏ i, g i (z.2 i) ∂ν) :
    μ = ν := by
  refine omg fun f g ↦ ?_
  rw [← toReal_eq_toReal_iff']
  · simp only [coe_finset_prod]
    have {μ : Measure (X × Π i, Y i)} :
        (∫⁻ z, f z.1 * ∏ i, (g i (z.2 i) : ℝ≥0∞) ∂μ).toReal =
          ∫ z, (f z.1).toReal * ∏ i, (g i (z.2 i)).toReal ∂μ := by
      rw [integral_eq_lintegral_of_nonneg_ae]
      · simp [ofReal_prod_of_nonneg]
      · exact Eventually.of_forall fun _ ↦ by positivity
      exact AEStronglyMeasurable.mul
        (continuous_coe.aestronglyMeasurable.comp_measurable (by fun_prop))
        (Finset.aestronglyMeasurable_fun_prod _ fun i _ ↦
          continuous_coe.aestronglyMeasurable.comp_measurable (by fun_prop))
    simp_rw [this]
    exact h ⟨⟨fun x ↦ (f x), by fun_prop⟩, f.map_bounded'⟩
      (fun i ↦ ⟨⟨fun y ↦ (g i y), by fun_prop⟩, (g i).map_bounded'⟩)
  · simp_rw [← coe_mul]
    convert (lintegral_lt_top_of_nnreal μ
      ((f.compContinuous ⟨@Prod.fst X (Π i, Y i), continuous_fst⟩) *
      (∏ i, (g i).compContinuous ⟨Function.eval i ∘ @Prod.snd X _, by fun_prop⟩))).ne
    simp only [BoundedContinuousFunction.coe_mul, coe_compContinuous, ContinuousMap.coe_mk,
      Pi.mul_apply, Function.comp_apply, mul_eq_mul_left_iff]

  -- apply (toReal_eq_toReal_iff' (lintegral_lt_top_of_nnreal μ
  --   ((f.compContinuous ⟨@Prod.fst X (Π i, Y i), continuous_fst⟩) *
  --     (∏ i, (g i).compContinuous ⟨Function.eval i ∘ @Prod.snd X _, ?_⟩))).ne
  --   (lintegral_lt_top_of_nnreal ν
  --   ((f.compContinuous ⟨@Prod.fst X (Π i, Y i), continuous_fst⟩) *
  --     (∏ i, (g i).compContinuous ⟨Function.eval i ∘ @Prod.snd X _, ?_⟩))).ne).1

end Measure
