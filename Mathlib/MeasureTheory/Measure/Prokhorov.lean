/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Integral.Regular
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Prokhorov theorem

We prove statements about the compactness of sets of finite measures or probability measures,
notably several versions of Prokhorov theorem on tight sets of probability measures.

## Main statements

* `instCompactSpaceProbabilityMeasure` proves that the space of probability measures on a compact
  space is itself compact
* `isCompact_setOf_probabilityMeasure_mass_eq_compl_isCompact_le`: Given a sequence of compact
  sets `Kₙ` and a sequence `uₙ` tending to zero, the probability measures giving mass at most `uₙ`
  to the complement of `Kₙ` form a compact set.
* `isCompact_closure_of_isTightMeasureSet`: Given a tight set of probability measures, its closure
  is compact.

Versions are also given for finite measures.

## Implementation

We do not assume second-countability or metrizability.

For the compactness of the space of probability measures in a compact space, we argue that every
ultrafilter converges, using the Riesz-Markov-Kakutani theorem to construct the limiting measure
in terms of its integrals against continuous functions.

For Prokhorov theorem `isCompact_setOf_probabilityMeasure_mass_eq_compl_isCompact_le`,
we rely on the compactness of the space of measures inside each compact set to get convergence
of the restriction there, and argue that the full measure converges to the sum of the individual
limits of the disjointed components. There is a subtlety that the space of finite measures
giving mass `uₙ` to `Kₙᶜ` doesn't have to be closed in our general setting, but we only need to
find *a* limit satisfying this condition. To ensure this, we need a technical condition
(monotonicity of `K` or normality of the space). In the first case, the bound follows readily
from the construction. In the second case, we modify the individual limits
(again using Riesz-Markov-Kakutani) to make sure that they are inner-regular, and then one can
check the condition.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

open scoped ENNReal NNReal CompactlySupported
open Filter Function Set Topology TopologicalSpace MeasureTheory BoundedContinuousFunction
  MeasureTheory.FiniteMeasure

variable {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [T2Space E] [BorelSpace E]

variable (E) in
/-- In a compact space, the set of finite measures with mass at most `C` is compact. -/
theorem isCompact_setOf_finiteMeasure_le_of_compactSpace [CompactSpace E] (C : ℝ≥0) :
    IsCompact {μ : FiniteMeasure E | μ.mass ≤ C} := by
  /- To prove the compactness, we will show that any sequence has a converging subsequence, in
  ultrafilters terms as things are not second countable. The integral against any bounded continuous
  function has a limit along the ultrafilter, by compactness of real intervals and the mass control.
  The limit is a monotone linear form. By the Riesz-Markov-Kakutani theorem, it comes from a
  measure. This measure is finite, of mass at most `C`. It provides the desired limit
  for the ultrafilter. -/
  apply isCompact_iff_ultrafilter_le_nhds'.2 (fun f hf ↦ ?_)
  have L (g : C_c(E, ℝ)) :
      ∃ x ∈ Icc (-C * ‖g.toBoundedContinuousFunction‖) (C * ‖g.toBoundedContinuousFunction‖),
      Tendsto (fun (μ : FiniteMeasure E) ↦ ∫ x, g x ∂μ) f (𝓝 x) := by
    simp only [Tendsto, ← Ultrafilter.coe_map]
    apply IsCompact.ultrafilter_le_nhds' isCompact_Icc
    simp only [neg_mul, Ultrafilter.mem_map]
    filter_upwards [hf] with μ hμ
    simp only [mem_preimage, mem_Icc]
    refine ⟨?_, ?_⟩
    · calc - (C * ‖g.toBoundedContinuousFunction‖)
      _ ≤ ∫ (x : E), - ‖g.toBoundedContinuousFunction‖ ∂μ := by
        simp only [integral_const, smul_eq_mul, mul_neg, neg_le_neg_iff]
        gcongr
        exact hμ
      _ ≤ ∫ x, g x ∂μ := by
        gcongr
        · simp
        · exact g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
        · intro x
          apply neg_le_of_abs_le
          exact g.toBoundedContinuousFunction.norm_coe_le_norm x
    · calc ∫ x, g x ∂μ
      _ ≤ ∫ (x : E), ‖g.toBoundedContinuousFunction‖ ∂μ := by
        gcongr
        · exact g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
        · simp
        · intro x
          apply le_of_abs_le
          exact g.toBoundedContinuousFunction.norm_coe_le_norm x
      _ ≤ C * ‖g.toBoundedContinuousFunction‖ := by
        simp only [integral_const, smul_eq_mul]
        gcongr
        exact hμ
  choose Λ h₀Λ hΛ using L
  let Λ' : C_c(E, ℝ) →ₚ[ℝ] ℝ :=
  { toFun := Λ
    map_add' g g' := by
      have : Tendsto (fun (μ : FiniteMeasure E) ↦ ∫ x, g x + g' x ∂μ) f (𝓝 (Λ g + Λ g')) := by
        convert (hΛ g).add (hΛ g')
        rw [integral_add]
        · exact g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
        · exact g'.continuous.integrable_of_hasCompactSupport g'.hasCompactSupport
      exact tendsto_nhds_unique (hΛ (g + g')) this
    map_smul' c g := by
      have : Tendsto (fun (μ : FiniteMeasure E) ↦ ∫ x, c • g x ∂μ) f (𝓝 (c • Λ g)) := by
        convert (hΛ g).const_smul c
        rw [integral_smul]
      exact tendsto_nhds_unique (hΛ (c • g)) this
    monotone' g g' hgg' := by
      apply le_of_tendsto_of_tendsto' (hΛ g) (hΛ g') (fun μ ↦ ?_)
      apply integral_mono _ _ hgg'
      · exact g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
      · exact g'.continuous.integrable_of_hasCompactSupport g'.hasCompactSupport }
  let μlim := RealRMK.rieszMeasure Λ'
  have μlim_le : μlim univ ≤ ENNReal.ofReal C := by
    let o : C_c(E, ℝ) :=
    { toFun := 1
      hasCompactSupport' := HasCompactSupport.of_compactSpace 1 }
    have : μlim univ ≤ ENNReal.ofReal (Λ' o) := RealRMK.rieszMeasure_le_of_eq_one Λ'
      (fun x ↦ by simp [o]) isCompact_univ (fun x ↦ by simp [o])
    apply this.trans
    gcongr
    apply le_of_tendsto (hΛ o)
    filter_upwards [hf] with μ hμ using by simpa [o] using hμ
  let μlim' : FiniteMeasure E := ⟨μlim, ⟨μlim_le.trans_lt (by simp)⟩⟩
  refine ⟨μlim', ?_, ?_⟩
  · simp only [mem_setOf_eq, FiniteMeasure.mk_apply, μlim', FiniteMeasure.mass]
    rw [show C = (ENNReal.ofReal ↑C).toNNReal by simp]
    exact ENNReal.toNNReal_mono (by simp) μlim_le
  change Tendsto id f (𝓝 μlim')
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto (fun g ↦ ?_)
  let g' : C_c(E, ℝ) :=
  { toFun := g
    hasCompactSupport' := HasCompactSupport.of_compactSpace _ }
  convert hΛ g'
  change ∫ (x : E), g' x ∂μlim' = Λ g'
  simp only [FiniteMeasure.toMeasure_mk, RealRMK.integral_rieszMeasure, μlim', μlim]
  rfl

variable (E) in
/-- In a compact space, the set of finite measures with mass `C` is compact. -/
lemma isCompact_setOf_finiteMeasure_eq_of_compactSpace [CompactSpace E] (C : ℝ≥0) :
    IsCompact {μ : FiniteMeasure E | μ.mass = C} := by
  have : {μ : FiniteMeasure E | μ.mass = C} = {μ | μ.mass ≤ C} ∩ {μ | μ.mass = C} := by grind
  rw [this]
  apply IsCompact.inter_right (isCompact_setOf_finiteMeasure_le_of_compactSpace E C)
  exact isClosed_eq (by fun_prop) (by fun_prop)

/-- In a compact space, the space of probability measures is also compact. -/
instance [CompactSpace E] : CompactSpace (ProbabilityMeasure E) := by
  constructor
  apply (ProbabilityMeasure.toFiniteMeasure_isEmbedding E).isCompact_iff.2
  simpa using isCompact_setOf_finiteMeasure_eq_of_compactSpace E 1

/-- The set of finite measures of mass at most `C` supported on a given compact set `K` is
compact. -/
lemma isCompact_setOf_finiteMeasure_le_of_isCompact
    (C : ℝ≥0) {K : Set E} (hK : IsCompact K) :
    IsCompact {μ : FiniteMeasure E | μ.mass ≤ C ∧ μ Kᶜ = 0} := by
  let f : K → E := Subtype.val
  have hf : IsClosedEmbedding f := IsClosedEmbedding.subtypeVal hK.isClosed
  have rf : range f = K := Subtype.range_val
  let F : FiniteMeasure K → FiniteMeasure E := fun μ ↦ μ.map f
  let T : Set (FiniteMeasure K) := {μ | μ.mass ≤ C}
  have : {μ : FiniteMeasure E | μ.mass ≤ C ∧ μ Kᶜ = 0} = F '' T := by
    apply Subset.antisymm
    · intro μ hμ
      simp only [mem_image]
      refine ⟨μ.comap f, (FiniteMeasure.mass_comap_le _ _).trans hμ.1, ?_⟩
      ext s hs
      simp only [toMeasure_map, F]
      rw [Measure.map_apply measurable_subtype_coe hs]
      simp only [toMeasure_comap]
      rw [Measure.comap_apply _ (Subtype.val_injective), image_preimage_eq_inter_range]
      · rw [← Measure.restrict_apply hs, Measure.restrict_eq_self_of_ae_mem]
        apply (null_iff_toMeasure_null (↑μ) (range f)ᶜ).mp
        rw [rf]
        exact hμ.2
      · exact fun t ht ↦ hf.measurableEmbedding.measurableSet_image' ht
      · exact hf.continuous.measurable hs
    · simp only [null_iff_toMeasure_null, image_subset_iff, preimage_setOf_eq, toMeasure_map,
        setOf_subset_setOf, F, T]
      intro μ hμ
      rw [Measure.map_apply hf.continuous.measurable hK.measurableSet.compl]
      refine ⟨(mass_map_le _ _).trans hμ, by simp [f]⟩
  rw [this]
  apply IsCompact.image _ (by fun_prop)
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact isCompact_setOf_finiteMeasure_le_of_compactSpace _ _

/-- **Prokhorov theorem**: Given a sequence of compact sets `Kₙ` and a sequence `uₙ` tending
to zero, the finite measures of mass at most `C` giving mass at most `uₙ` to the complement of `Kₙ`
form a compact set. -/
lemma isCompact_setOf_finiteMeasure_mass_le_compl_isCompact_le
    {u : ℕ → ℝ≥0} {K : ℕ → Set E} (C : ℝ≥0)
    (hu : Tendsto u atTop (𝓝 0)) (hK : ∀ n, IsCompact (K n)) (h : NormalSpace E ∨ Monotone K) :
    IsCompact {μ : FiniteMeasure E | μ.mass ≤ C ∧ ∀ n, μ (K n)ᶜ ≤ u n} := by
  /- Consider a sequence of measures with mass at most `C` and giving mass at most `uₙ` to `Kₙᶜ`,
  for which we want to find a converging subsequence.
  We want to write `⋃ n, Kₙ` as the disjoint union of `disjointed K n`, restrict the measures to
  each of these sets (which is contained in the compact set `Kₙ`), extract a converging subsequence
  there, to a limit `νₙ`, and then argue that the sequence converges to `μ := ∑ νₙ`.
  We will implement this rough idea, but there are two technical complications.
  First, we should not use a sequence and subsequences, but a ultrafilter as things are not second
  countable.
  Second, it is not obvious that the limit will satisfy the inequality `μ (Kₙᶜ) ≤ uₙ`, as this is
  not a closed condition in the space of measures in general (note that we are not assuming that
  our space is metrizable). To check this inequality, we need the technical condition that the
  space is normal or the sequence `K` is monotone. When the space is normal, the inequality can be
  proved from the weak convergence if we can ensure additionally that `μ` is
  inner regular. We will guarantee this by making sure each `νₙ` is inner regular. When the
  sequence `K` is monotone, on the other hand, the bound readily follows from the construction.
  -/
  -- We can decompose a measure as a sum of restrictions to `disjointed K n`, finite version.
  have I (μ : FiniteMeasure E) (n : ℕ) :
      ∑ i ∈ Finset.range (n + 1), μ.restrict (disjointed K i) = μ.restrict (partialSups K n) := by
    rw [← biUnion_range_succ_disjointed, FiniteMeasure.restrict_biUnion_finset]
    · exact (disjoint_disjointed K).set_pairwise _
    · exact MeasurableSet.disjointed (fun i ↦ (hK i).measurableSet)
  have A n : IsCompact (partialSups K n) := by
    simpa [partialSups_eq_accumulate] using isCompact_accumulate hK _
  -- start with a ultrafilter `f`, for which we want to prove convergence.
  apply isCompact_iff_ultrafilter_le_nhds'.2 (fun f hf ↦ ?_)
  -- the restrictions to `disjointed K n` converge along the ultrafilter, and moreover we can
  -- choose the limit to be inner regular.
  have M n : ∃ (ν : FiniteMeasure E), Measure.InnerRegular (ν : Measure E) ∧
      ν (partialSups K n)ᶜ = 0 ∧
      Tendsto (fun (ρ : FiniteMeasure E) ↦ ρ.restrict (disjointed K n)) f (𝓝 ν) := by
    -- the existence of a limit follows from the fact that these measures are supported in
    -- the compact set `partialSups K n`.
    obtain ⟨ν, hν, ν_lim⟩ : ∃ ν ∈ {ρ : FiniteMeasure E | ρ.mass ≤ C ∧ ρ (partialSups K n)ᶜ = 0},
        Tendsto (fun (ρ : FiniteMeasure E) ↦ ρ.restrict (disjointed K n)) f (𝓝 ν) := by
      simp only [Tendsto]
      rw [← Ultrafilter.coe_map]
      apply IsCompact.ultrafilter_le_nhds'
        (isCompact_setOf_finiteMeasure_le_of_isCompact C (A n))
      simp only [null_iff_toMeasure_null, Ultrafilter.mem_map, preimage_setOf_eq]
      filter_upwards [hf] with ρ hρ
      simp only [restrict_mass, restrict_measure_eq,
        Measure.restrict_apply (A n).measurableSet.compl]
      refine ⟨(apply_le_mass ρ _).trans hρ.1, ?_⟩
      convert measure_empty (μ := (ρ : Measure E))
      apply disjoint_iff.1
      apply disjoint_compl_left.mono_right
      exact le_trans sdiff_le (le_partialSups _ _)
    -- We can find an inner regular measure which coincides with the above limit wrt
    -- integration of bounded continuous functions.
    obtain ⟨ν', ν'_reg, ν'_fin, ν'K, hν'⟩ : ∃ ν', ν'.InnerRegular ∧ IsFiniteMeasure ν' ∧
        ν' (partialSups K n)ᶜ = 0 ∧ ∀ (g : E →ᵇ ℝ), ∫ x, g x ∂ν = ∫ x, g x ∂ν' := by
      apply Measure.exists_innerRegular_eq_of_isCompact _ (A n)
      rw [← MeasureTheory.FiniteMeasure.null_iff_toMeasure_null]
      exact hν.2
    -- This inner regular measure is also a limit for our ultrafilter
    let μ : FiniteMeasure E := ⟨ν', ν'_fin⟩
    refine ⟨μ, ν'_reg, by simp [μ, ν'K], ?_⟩
    apply tendsto_of_forall_integral_tendsto (fun g ↦ ?_)
    convert tendsto_iff_forall_integral_tendsto.1 ν_lim g using 2
    exact (hν' g).symm
  -- let `νₙ` be such nice limits on `disjointed K n`.
  choose! ν ν_reg νK hν using M
  -- their sum is a finite measure, of mass at most `C`.
  have B : (Measure.sum (fun n ↦ (ν n : Measure E))) univ ≤ C := by
    -- this follows from the corresponding result for finite sums, where we can use the
    -- continuity of the mass of a finite measure under weak convergence.
    simp only [MeasurableSet.univ, Measure.sum_apply]
    have : Tendsto (fun n ↦ ∑ i ∈ Finset.range (n + 1), (ν i : Measure E) univ) atTop
        (𝓝 (∑' i, (ν i : Measure E) univ)) :=
      (ENNReal.tendsto_nat_tsum _).comp (tendsto_add_atTop_nat 1)
    apply le_of_tendsto' this (fun n ↦ ?_)
    have : ∑ i ∈ Finset.range (n + 1), (ν i : Measure E) univ
        = (∑ i ∈ Finset.range (n + 1), ν i).toMeasure univ := by simp
    rw [this]
    suffices (∑ i ∈ Finset.range (n + 1), ν i).mass ≤ C by
      convert ENNReal.coe_le_coe.2 this
      simp
    have : Tendsto (fun (μ : FiniteMeasure E) ↦
        (∑ i ∈ Finset.range (n + 1), μ.restrict (disjointed K i)).mass) f
        (𝓝 ((∑ i ∈ Finset.range (n + 1), ν i).mass)) := by
      apply Tendsto.mass
      exact tendsto_finset_sum _ (fun i hi ↦ hν i)
    apply le_of_tendsto this
    filter_upwards [hf] with μ hμ
    rw [I, restrict_mass]
    exact le_trans (apply_mono _ (subset_univ _)) hμ.1
  -- Let `μ` be the limiting measure
  let μ : FiniteMeasure E := ⟨Measure.sum (fun n ↦ (ν n : Measure E)), ⟨B.trans_lt (by simp)⟩⟩
  -- first, we show that it is indeed a limit of the ultrafilter
  have L : Tendsto id f (𝓝 μ) := by
    -- We need to check the convergence of the integral of a bounded continuous function.
    -- Finite sums of restrictions to `disjointed K n` converge obviously to finite sums of `νₙ`,
    -- but we need to control the infinite sums. For this, we split `ε` in 3, argue that for `μ`
    -- this is the limit of finite sums, and inside the space we can uniformly truncate the sum
    -- also as the tail is controlled by `uₙ`. Once we have fixed a truncation level satisfying
    -- both conditions, we can rely on the finite sum convergence to conclude.
    apply tendsto_of_forall_integral_tendsto (fun g ↦ ?_)
    rw [Metric.tendsto_nhds]
    intro ε εpos
    -- first, control truncation of the finite sums for the limiting measure
    have I1 : ∀ᶠ n in atTop,
        dist (∫ x, g x ∂(∑ i ∈ Finset.range (n + 1), ν i)) (∫ x, g x ∂μ) < ε / 3 := by
      have : Tendsto (fun n ↦ ∫ x, g x ∂(∑ i ∈ Finset.range n, ν i)) atTop (𝓝 (∫ x, g x ∂μ)) := by
        simp only [FiniteMeasure.toMeasure_mk, μ]
        rw [integral_sum_measure (g.integrable (μ := μ))]
        simp_rw [integral_finset_sum_measure (fun i hi ↦ g.integrable _)]
        apply Summable.tendsto_sum_tsum_nat
        apply (hasSum_integral_measure _).summable
        exact g.integrable (μ := μ)
      exact Metric.tendsto_nhds.1 (this.comp (tendsto_add_atTop_nat 1)) _ (by positivity)
    -- second, truncation threshold in terms of tails `uₙ` (the relevance of this condition will
    -- appear below).
    have I2 : ∀ᶠ n in atTop, ‖g‖ * u n < ε / 3 := by
      have := (NNReal.tendsto_coe.2 hu).const_mul (‖g‖)
      simp only [NNReal.coe_zero, mul_zero] at this
      exact (tendsto_order.1 this).2 (ε / 3) (by positivity)
    -- fix a large `n` satisfying both truncation conditions
    rcases (I1.and I2).exists with ⟨n, hn, h'n⟩
    -- the finite sums up to the fixed `n` converge to the limit, by convergence of individual
    -- summands
    have : Tendsto (fun (ρ : FiniteMeasure E) ↦
        ∫ x, g x ∂(∑ i ∈ Finset.range (n + 1), ρ.restrict (disjointed K i) : FiniteMeasure E)) f
        (𝓝 (∫ x, g x ∂(∑ i ∈ Finset.range (n + 1), ν i : FiniteMeasure E))) := by
      apply tendsto_iff_forall_integral_tendsto.1 _ g
      apply tendsto_finset_sum _ (fun i hi ↦ hν i)
    -- therefore, after some point the difference is bounded by `ε / 3`.
    filter_upwards [Metric.tendsto_nhds.1 this (ε / 3) (by positivity), hf] with ρ hρ h'ρ
    -- let us show that in this case the full integrals differ by at most `ε`.
    calc dist (∫ (x : E), g x ∂ρ) (∫ (x : E), g x ∂μ)
    -- we separate away the tails from the sums up to `n`
    _ ≤ dist (∫ (x : E), g x ∂ρ)
          (∫ x, g x ∂(∑ i ∈ Finset.range (n + 1), ρ.restrict (disjointed K i)))
        + dist (∫ x, g x ∂(∑ i ∈ Finset.range (n + 1), ρ.restrict (disjointed K i)))
          (∫ x, g x ∂(∑ i ∈ Finset.range (n + 1), ν i))
        + dist (∫ x, g x ∂(∑ i ∈ Finset.range (n + 1), ν i)) (∫ (x : E), g x ∂μ) :=
      dist_triangle4 _ _ _ _
    -- each term is bounded by `ε / 3` by design.
    _ < ε / 3 + ε / 3 + ε / 3 := by
      gcongr
      · have : ρ = ρ.restrict (partialSups K n)ᶜ +
            ∑ i ∈ Finset.range (n + 1), ρ.restrict (disjointed K i) := by
          rw [I, ← FiniteMeasure.restrict_union disjoint_compl_left (A n).measurableSet]
          simp
        nth_rewrite 1 [this]
        rw [toMeasure_add, integral_add_measure (g.integrable _) (g.integrable _)]
        simp only [toMeasure_sum, dist_add_self_left]
        calc ‖∫ x, g x ∂(ρ.restrict ((partialSups K) n)ᶜ)‖
        _ ≤ ∫ x, ‖g x‖ ∂(ρ.restrict ((partialSups K) n)ᶜ) := norm_integral_le_integral_norm _
        _ ≤ ∫ x, ‖g‖ ∂(ρ.restrict ((partialSups K) n)ᶜ : Measure E) := by
          apply integral_mono_of_nonneg
          · filter_upwards with x using by positivity
          · simp
          · filter_upwards with x using norm_coe_le_norm g x
        _ = ‖g‖ * ρ ((partialSups K) n)ᶜ := by simp [mul_comm]
        _ ≤ ‖g‖ * ρ (K n)ᶜ := by gcongr; apply le_partialSups
        _ ≤ ‖g‖ * u n := by gcongr; exact h'ρ.2 n
        _ < ε / 3 := h'n
      · simpa using hρ
    _ = ε := by ring
  -- Now that we have proved the convergence, we can finish the proof of the theorem. It remains
  -- to check the mass control of the limit (which we have already done when proving finiteness)
  -- and to show that `μ (Kₙᶜ) ≤ uₙ`, which is harder.
  refine ⟨μ, ⟨?_, fun n ↦ ?_⟩, L⟩
  · simp only [mass, mk_apply, μ]
    rw [show C = (C : ℝ≥0∞).toNNReal by simp]
    exact ENNReal.toNNReal_mono (by simp) B
  -- Let us now prove that `μ (Kₙᶜ) ≤ uₙ`. We argue differently depending on whether the space is
  -- normal or if the sequence `K` is monotone.
  rcases h with h | h
  · -- To show that `μ (Kₙᶜ) ≤ uₙ` when the space is normal, we argue that `μ (Kₙᶜ)` is the
    -- supremum of the integrals of continuous functions supported in `Kₙᶜ` and bounded by `1`,
    -- as the measure is inner regular. Therefore, we are reduced to a question about integrals of
    -- continuous functions, for which we can take advantage of the weak convergence.
    have : Measure.InnerRegular (μ : Measure E) := by simp only [toMeasure_mk, μ]; infer_instance
    rw [← ENNReal.coe_le_coe, ennreal_coeFn_eq_coeFn_toMeasure,
      (hK n).isClosed.isOpen_compl.measure_eq_biSup_integral_continuous]
    simp only [compl_compl, iSup_le_iff, ENNReal.ofReal_le_coe]
    intro g g_cont gK g_nonneg g_le
    have : Tendsto (fun (ρ : FiniteMeasure E) ↦ ∫ x, g x ∂ρ) f (𝓝 (∫ x, g x ∂μ)) := by
      let g' : E →ᵇ ℝ :=
      { toFun := g
        map_bounded' := by
          refine ⟨1, fun x y ↦ ?_⟩
          simp only [dist, abs_le, neg_le_sub_iff_le_add, tsub_le_iff_right]
          exact ⟨(g_le y).trans (by simpa using g_nonneg x),
            (g_le x).trans (by simpa using g_nonneg y)⟩ }
      exact tendsto_iff_forall_integral_tendsto.1 L g'
    apply le_of_tendsto this
    filter_upwards [hf] with ρ hρ
    calc ∫ x, g x ∂ρ
    _ ≤ ∫ x, indicator (K n)ᶜ 1 x ∂ρ := by
      apply integral_mono_of_nonneg
      · filter_upwards [] with x using g_nonneg x
      · apply Integrable.indicator (integrable_const _) (hK n).measurableSet.compl
      · filter_upwards [] with x
        by_cases hx : x ∈ (K n)ᶜ
        · simpa [hx] using g_le x
        · simp only [hx, not_false_eq_true, indicator_of_notMem]
          apply le_of_eq
          apply gK
          simpa using hx
    _ = ρ (K n)ᶜ := by simp [integral_indicator (hK n).measurableSet.compl]
    _ ≤ u n := mod_cast hρ.2 n
  · -- to show that `μ (Kₙᶜ) ≤ uₙ` when the sequence `K` is monotone, we argue that the only
    -- contribution to `μ (Kₙᶜ)` comes from the measures `νᵢ` with `i > n`. Then we restrict to
    -- a finite sum `∑ i ∈ Ioc n m, νᵢ`, and argue that it is the limit of
    -- `∑ i ∈ Ioc n m, ρ.restricted (K i \ K(i - 1))`, i.e., `ρ.restricted (K m \ K n)`. The total
    -- mass converges (thanks to the weak convergence of finite sums), and the total mass of
    -- `ρ.restricted (K m \ K n)` is bounded by `ρ (Kₙᶜ) ≤ uₙ`.
    suffices (μ : Measure E) (K n)ᶜ ≤ u n by
      apply ENNReal.coe_le_coe.1
      convert this
      simp
    simp only [toMeasure_mk, (hK n).measurableSet.compl, Measure.sum_apply, μ]
    have : Tendsto (fun m ↦ ∑ i ∈ Finset.range (m + 1), (ν i : Measure E) (K n)ᶜ) atTop
        (𝓝 (∑' i, (ν i : Measure E) (K n)ᶜ)) :=
      (ENNReal.tendsto_nat_tsum _).comp (tendsto_add_atTop_nat 1)
    apply le_of_tendsto this
    filter_upwards [Ici_mem_atTop n] with m (hm : n ≤ m)
    have : ∑ i ∈ Finset.range (m + 1), (ν i : Measure E) (K n)ᶜ
        = ∑ i ∈ Finset.Ioc n m, (ν i : Measure E) (K n)ᶜ := by
      apply (Finset.sum_subset (by grind) _).symm
      simp +contextual only [Finset.mem_range_succ_iff, Finset.mem_Ioc, not_and,
        not_true_eq_false, imp_false, not_lt, ← null_iff_toMeasure_null]
      intro i hi h'i
      apply (ν i).mono_null _ (νK i)
      rw [Monotone.partialSups_eq h]
      exact compl_subset_compl.2 (h h'i)
    rw [this]
    suffices (∑ i ∈ Finset.Ioc n m, ν i).toMeasure univ ≤ u n by
      apply le_trans _ this
      simp only [toMeasure_sum, Measure.coe_finset_sum, Finset.sum_apply]
      gcongr
      simp
    suffices (∑ i ∈ Finset.Ioc n m, ν i).mass ≤ u n by
      convert ENNReal.coe_le_coe.2 this
      simp
    have : Tendsto (fun (μ : FiniteMeasure E) ↦
        (∑ i ∈ Finset.Ioc n m, μ.restrict (disjointed K i)).mass) f
        (𝓝 ((∑ i ∈ Finset.Ioc n m, ν i).mass)) := by
      apply Tendsto.mass
      exact tendsto_finset_sum _ (fun i hi ↦ hν i)
    apply le_of_tendsto this
    filter_upwards [hf] with μ hμ
    have : ∑ i ∈ Finset.Ioc n m, μ.restrict (disjointed K i) = μ.restrict (K m \ K n) := by
      rw [← biUnion_Ioc_disjointed_of_monotone h hm, FiniteMeasure.restrict_biUnion_finset]
      · exact (disjoint_disjointed K).set_pairwise _
      · exact MeasurableSet.disjointed (fun i ↦ (hK i).measurableSet)
    rw [this, restrict_mass]
    exact le_trans (apply_mono _ (diff_subset_compl (K m) (K n))) (hμ.2 n)

/-- **Prokhorov theorem**: Given a sequence of compact sets `Kₙ` and a sequence `uₙ` tending to
zero, the finite measures of mass `C` giving mass at most `uₙ` to the complement of `Kₙ` form a
compact set. -/
lemma isCompact_setOf_finiteMeasure_mass_eq_compl_isCompact_le {u : ℕ → ℝ≥0}
    {K : ℕ → Set E} (C : ℝ≥0) (hu : Tendsto u atTop (𝓝 0)) (hK : ∀ n, IsCompact (K n))
    (h : NormalSpace E ∨ Monotone K) :
    IsCompact {μ : FiniteMeasure E | μ.mass = C ∧ ∀ n, μ (K n)ᶜ ≤ u n} := by
  have : {μ : FiniteMeasure E | μ.mass = C ∧ ∀ n, μ (K n)ᶜ ≤ u n} =
    {μ | μ.mass ≤ C ∧ ∀ n, μ (K n)ᶜ ≤ u n} ∩ {μ | μ.mass = C} := by ext; grind
  rw [this]
  apply IsCompact.inter_right (isCompact_setOf_finiteMeasure_mass_le_compl_isCompact_le C hu hK h)
  exact isClosed_eq (by fun_prop) (by fun_prop)

/-- **Prokhorov theorem**: Given a sequence of compact sets `Kₙ` and a sequence `uₙ` tending to
zero, the probability measures giving mass at most `uₙ` to the complement of `Kₙ` form a
compact set. -/
lemma isCompact_setOf_probabilityMeasure_mass_eq_compl_isCompact_le {u : ℕ → ℝ≥0}
    {K : ℕ → Set E} (hu : Tendsto u atTop (𝓝 0)) (hK : ∀ n, IsCompact (K n))
    (h : NormalSpace E ∨ Monotone K) :
    IsCompact {μ : ProbabilityMeasure E | ∀ n, μ (K n)ᶜ ≤ u n} := by
  apply (ProbabilityMeasure.toFiniteMeasure_isEmbedding E).isCompact_iff.2
  have : ProbabilityMeasure.toFiniteMeasure '' {μ | ∀ (n : ℕ), μ (K n)ᶜ ≤ u n}
      = {μ : FiniteMeasure E | μ.mass = 1 ∧ ∀ n, μ (K n)ᶜ ≤ u n} := by
    ext μ
    simp only [mem_image, mem_setOf_eq]
    refine ⟨?_, ?_⟩
    · rintro ⟨ν, hν, rfl⟩
      simpa using hν
    · rintro ⟨hμ, h'μ⟩
      let ν : ProbabilityMeasure E := ⟨μ, isProbabilityMeasure_iff_real.2 (by simpa using hμ)⟩
      have : ν.toFiniteMeasure = μ := by ext; rfl
      exact ⟨ν, by simpa [← this] using h'μ , this⟩
  rw [this]
  exact isCompact_setOf_finiteMeasure_mass_eq_compl_isCompact_le 1 hu hK h

/-- **Prokhorov theorem**: the closure of a tight set of probability measures is compact.
We only require the space to be T2. -/
lemma isCompact_closure_of_isTightMeasureSet {S : Set (ProbabilityMeasure E)}
    (hS : IsTightMeasureSet {((μ : ProbabilityMeasure E) : Measure E) | μ ∈ S}) :
    IsCompact (closure S) := by
  obtain ⟨u, -, u_pos, u_lim⟩ :
      ∃ u : ℕ → ℝ≥0, StrictAnti u ∧ (∀ n, 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto 0
  have A n : ∃ (K : Set E), IsCompact K ∧ ∀ μ ∈ S, μ Kᶜ ≤ u n := by
    rcases isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1 hS (u n)
      (by norm_cast; exact u_pos n) with ⟨K, K_comp, hK⟩
    refine ⟨K, K_comp, fun μ hμ ↦ ?_⟩
    have : (μ : Measure E) Kᶜ ≤ u n := hK _ ⟨μ, hμ, rfl⟩
    exact ENNReal.coe_le_coe.1 (by simpa using this)
  choose K K_comp hK using A
  let K' n := ⋃ i ∈ Iic n, K i
  have h'K : IsCompact {μ : ProbabilityMeasure E | ∀ n, μ (K' n)ᶜ ≤ u n} := by
    apply isCompact_setOf_probabilityMeasure_mass_eq_compl_isCompact_le u_lim
    · exact fun n ↦ (finite_Iic n).isCompact_biUnion (fun i hi ↦ K_comp i)
    · right
      simp only [Monotone, mem_Iic, le_eq_subset, iUnion_subset_iff, K']
      intro a b hab i hi
      apply subset_biUnion_of_mem
      exact hi.trans hab
  apply IsCompact.closure_of_subset h'K
  intro μ hμ n
  calc μ (K' n)ᶜ
  _ ≤ μ (K n)ᶜ := by
    gcongr
    simp only [mem_Iic, K']
    apply subset_biUnion_of_mem
    exact le_rfl (a := n)
  _ ≤ u n := by grind
