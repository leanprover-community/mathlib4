/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Measure.Tight

import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Tight sets of measures in Hilbert spaces

In an infinite-dimensional Hilbert space, closed balls are not compact, so a bound on the norms
does not suffice for tightness. Given a Hilbert basis `b`, a set of measures is tight as soon as
the norms are bounded in probability and, uniformly over the set, the measures concentrate near
the finite-dimensional subspaces spanned by finitely many vectors of `b`.

## Main statements

* `HilbertBasis.isCompact_closedBall_inter_iInter`: a closed ball intersected with sets on which
  the distance to the span of finitely many basis vectors is at most `ε m`, with `ε m → 0`,
  is compact.
* `HilbertBasis.isTightMeasureSet_of_tendsto_measure`: if the norms are bounded in probability
  and the distance to the span of `b i, i ∈ s` is small in probability uniformly over the set
  as `s` grows, then the set of measures is tight.
* `HilbertBasis.isTightMeasureSet_of_lintegral`: the same conclusion from a uniform bound on the
  second moments of the norm and uniformly small second moments of the tails.
* `HilbertBasis.isTightMeasureSet_of_lintegral_inner_sq_le`: if the second moments of the
  coordinates `⟪b i, x⟫` are bounded uniformly over the set by a summable family, then the set
  is tight.

## References

* [V. I. Bogachev, *Measure theory. Vol. II*][bogachev2007]: Definition 8.6.1 (uniform
  tightness); cf. Example 8.6.5(i) for tightness from a uniform moment bound

-/

public section

open Filter Metric Set MeasureTheory
open scoped Topology ENNReal NNReal RealInnerProductSpace

/-- In a separable inner product space, an orthonormal family is countable. -/
theorem Orthonormal.countable {𝕜 ι E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [TopologicalSpace.SeparableSpace E] {v : ι → E}
    (hv : Orthonormal 𝕜 v) : Countable ι := by
  refine Pairwise.countable_of_isOpen_disjoint (s := fun i ↦ ball (v i) (1 / 2)) ?_
    (fun _ ↦ isOpen_ball) (fun i ↦ nonempty_ball.2 (by norm_num))
  intro i j hij
  refine ball_disjoint_ball ?_
  have h : dist (v i) (v j) ^ 2 = 2 := by
    rw [dist_eq_norm, @norm_sub_sq 𝕜, hv.1 i, hv.1 j, hv.2 hij]
    norm_num
  nlinarith [dist_nonneg (x := v i) (y := v j)]

namespace HilbertBasis

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (b : HilbertBasis ι ℝ E)

/-- A Hilbert space with a Hilbert basis is complete. -/
protected theorem completeSpace (b : HilbertBasis ι ℝ E) : CompleteSpace E :=
  b.repr.toIsometryEquiv.completeSpace

/-- In a separable space, the index type of a Hilbert basis is countable. -/
protected theorem countable [TopologicalSpace.SeparableSpace E] (b : HilbertBasis ι ℝ E) :
    Countable ι :=
  b.orthonormal.countable

/-- **Parseval's identity**: `∑ i, ⟪b i, x⟫ ^ 2 = ‖x‖ ^ 2`. -/
theorem hasSum_inner_sq (x : E) : HasSum (fun i ↦ ⟪b i, x⟫ ^ 2) (‖x‖ ^ 2) := by
  simpa [sq, real_inner_comm x, real_inner_self_eq_norm_sq] using b.hasSum_inner_mul_inner x x

/-- The sum of the squares of the coordinates outside a finite set `s` is the squared distance
from `x` to its orthogonal projection `∑ i ∈ s, ⟪b i, x⟫ • b i` on the span of `b i, i ∈ s`. -/
theorem hasSum_indicator_inner_sq (s : Finset ι) (x : E) :
    HasSum ((s : Set ι)ᶜ.indicator fun i ↦ ⟪b i, x⟫ ^ 2)
      (‖x - ∑ i ∈ s, ⟪b i, x⟫ • b i‖ ^ 2) := by
  convert b.hasSum_inner_sq (x - ∑ i ∈ s, ⟪b i, x⟫ • b i) using 2 with i
  rw [inner_sub_right]
  by_cases hi : i ∈ s
  · simp [hi, b.orthonormal.inner_right_sum _ hi]
  · rw [Set.indicator_of_mem (by simpa using hi), inner_sum, Finset.sum_eq_zero, sub_zero]
    intro j hj
    rw [real_inner_smul_right, b.orthonormal.2 (ne_of_mem_of_not_mem hj hi).symm, mul_zero]

/-- Version of `HilbertBasis.hasSum_indicator_inner_sq` with extended nonnegative reals: the
sum of the squares of the coordinates outside `s` is the squared distance from `x` to the span of
`b i, i ∈ s`. -/
theorem tsum_indicator_enorm_inner_sq (s : Finset ι) (x : E) :
    ∑' i, (s : Set ι)ᶜ.indicator (fun i ↦ ‖⟪b i, x⟫‖ₑ ^ 2) i =
      ‖x - ∑ i ∈ s, ⟪b i, x⟫ • b i‖ₑ ^ 2 := by
  have h := b.hasSum_indicator_inner_sq s x
  have h_nonneg : ∀ i, 0 ≤ (s : Set ι)ᶜ.indicator (fun i ↦ ⟪b i, x⟫ ^ 2) i :=
    fun i ↦ Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) i
  conv_rhs => rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← h.tsum_eq,
    ENNReal.ofReal_tsum_of_nonneg h_nonneg h.summable]
  refine tsum_congr fun i ↦ ?_
  by_cases hi : i ∈ (s : Set ι)ᶜ
  · rw [Set.indicator_of_mem hi, Set.indicator_of_mem hi, ← ofReal_norm,
      ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
  · simp [hi]

/-- A closed ball intersected with sets on which the distance to the span of
`b i, i ∈ s m` is at most `ε m`, where `ε m → 0`, is compact. -/
theorem isCompact_closedBall_inter_iInter (r : ℝ) (s : ℕ → Finset ι) {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) :
    IsCompact (closedBall 0 r ∩ ⋂ m, {x : E | ‖x - ∑ i ∈ s m, ⟪b i, x⟫ • b i‖ ≤ ε m}) := by
  have := b.completeSpace
  refine isCompact_iff_totallyBounded_isComplete.2 ⟨?_, IsClosed.isComplete ?_⟩
  · refine totallyBounded_iff.2 fun δ hδ ↦ ?_
    obtain ⟨m, hm⟩ := (hε.eventually (gt_mem_nhds (half_pos hδ))).exists
    -- the finite-dimensional span of `b i, i ∈ s m`, intersected with a large ball
    set U : Submodule ℝ E := Submodule.span ℝ (b '' (s m : Set ι))
    have : FiniteDimensional ℝ U :=
      FiniteDimensional.span_of_finite ℝ ((s m).finite_toSet.image _)
    have hB : IsCompact (((↑) : U → E) '' closedBall 0 (r + δ)) :=
      (ProperSpace.isCompact_closedBall _ _).image continuous_subtype_val
    obtain ⟨t, ht, hcov⟩ := totallyBounded_iff.1 hB.totallyBounded (δ / 2) (half_pos hδ)
    refine ⟨t, ht, fun x hx ↦ ?_⟩
    simp only [mem_inter_iff, mem_closedBall_zero_iff, mem_iInter, mem_ofPred_eq] at hx
    set y := ∑ i ∈ s m, ⟪b i, x⟫ • b i
    have hyU : y ∈ U := Submodule.sum_mem _ fun i hi ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    have hxy : dist x y < δ / 2 := by rw [dist_eq_norm]; exact (hx.2 m).trans_lt hm
    have hyB : y ∈ ((↑) : U → E) '' closedBall 0 (r + δ) := by
      refine ⟨⟨y, hyU⟩, ?_, rfl⟩
      rw [mem_closedBall_zero_iff, ← Submodule.norm_coe]
      have := norm_le_norm_add_norm_sub' y x
      rw [← dist_eq_norm, dist_comm] at this
      linarith [hx.1]
    obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.1 (hcov hyB)
    refine mem_iUnion₂.2 ⟨z, hz, ?_⟩
    rw [mem_ball] at hyz ⊢
    linarith [dist_triangle x y z]
  · exact isClosed_closedBall.inter <| isClosed_iInter fun m ↦
      isClosed_le (by fun_prop) continuous_const

variable {mE : MeasurableSpace E} {S : Set (Measure E)}

/-- **Tightness in a Hilbert space.** Let `b` be a Hilbert basis. If the norms are bounded in
probability uniformly over `S`, and for each `ε > 0` the probability that the distance from `x`
to the span of `b i, i ∈ s` exceeds `ε` tends to `0` uniformly over `S` as `s` grows, then
`S` is tight. -/
theorem isTightMeasureSet_of_tendsto_measure
    (h_norm : Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ {x | r < ‖x‖}) atTop (𝓝 0))
    (h_tail : ∀ ε > 0, Tendsto (fun s : Finset ι ↦
      ⨆ μ ∈ S, μ {x | ε < ‖x - ∑ i ∈ s, ⟪b i, x⟫ • b i‖}) atTop (𝓝 0)) :
    IsTightMeasureSet S := by
  refine isTightMeasureSet_iff_exists_isCompact_measure_compl_le.2 fun ε hε ↦ ?_
  have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε.ne').ne'
  obtain ⟨δ, hδ_pos, hδ⟩ := ENNReal.exists_pos_sum_of_countable hε2 ℕ
  obtain ⟨r, hr⟩ := ENNReal.tendsto_atTop_zero.1 h_norm (ε / 2) (pos_iff_ne_zero.2 hε2)
  have h_s (m : ℕ) : ∃ s : Finset ι, ⨆ μ ∈ S,
      μ {x | 1 / ((m : ℝ) + 1) < ‖x - ∑ i ∈ s, ⟪b i, x⟫ • b i‖} ≤ δ m := by
    have hm : (0 : ℝ) < 1 / ((m : ℝ) + 1) := Nat.one_div_pos_of_nat
    have hδm : (0 : ℝ≥0∞) < δ m := ENNReal.coe_pos.2 (hδ_pos m)
    exact ((h_tail _ hm).eventually (ge_mem_nhds hδm)).exists
  choose s hs using h_s
  refine ⟨_, b.isCompact_closedBall_inter_iInter r s tendsto_one_div_add_atTop_nhds_zero_nat,
    fun μ hμ ↦ ?_⟩
  have h_sub : (closedBall (0 : E) r ∩
      ⋂ m : ℕ, {x | ‖x - ∑ i ∈ s m, ⟪b i, x⟫ • b i‖ ≤ 1 / ((m : ℝ) + 1)})ᶜ ⊆
      {x | r < ‖x‖} ∪ ⋃ m : ℕ, {x | 1 / ((m : ℝ) + 1) < ‖x - ∑ i ∈ s m, ⟪b i, x⟫ • b i‖} := by
    intro x hx
    simp only [mem_compl_iff, mem_inter_iff, mem_closedBall_zero_iff, mem_iInter, mem_ofPred_eq,
      not_and, not_forall, not_le, mem_union, mem_iUnion] at hx ⊢
    by_cases h : ‖x‖ ≤ r
    · exact .inr (hx h)
    · exact .inl (not_le.1 h)
  calc μ (closedBall (0 : E) r ∩
        ⋂ m : ℕ, {x | ‖x - ∑ i ∈ s m, ⟪b i, x⟫ • b i‖ ≤ 1 / ((m : ℝ) + 1)})ᶜ
  _ ≤ μ {x | r < ‖x‖} +
      ∑' m : ℕ, μ {x | 1 / ((m : ℝ) + 1) < ‖x - ∑ i ∈ s m, ⟪b i, x⟫ • b i‖} :=
    (measure_mono h_sub).trans <| (measure_union_le _ _).trans <| by
      gcongr
      exact measure_iUnion_le _
  _ ≤ ε / 2 + ∑' m : ℕ, (δ m : ℝ≥0∞) := by
    gcongr with m
    · exact (le_iSup₂ (f := fun μ (_ : μ ∈ S) ↦ μ {x | r < ‖x‖}) μ hμ).trans (hr r le_rfl)
    · exact (le_iSup₂ (f := fun μ (_ : μ ∈ S) ↦
        μ {x | 1 / ((m : ℝ) + 1) < ‖x - ∑ i ∈ s m, ⟪b i, x⟫ • b i‖}) μ hμ).trans (hs m)
  _ ≤ ε / 2 + ε / 2 := by gcongr
  _ = ε := ENNReal.add_halves ε

/-- **Tightness in a Hilbert space from second moments.** Let `b` be a Hilbert basis. If the
second moments `∫⁻ x, ‖x‖ₑ ^ 2 ∂μ` are bounded uniformly over `S`, and the second moments of the
distance from `x` to the span of `b i, i ∈ s` tend to `0` uniformly over `S` as `s` grows, then
`S` is tight. -/
theorem isTightMeasureSet_of_lintegral [OpensMeasurableSpace E]
    (h_norm : ⨆ μ ∈ S, ∫⁻ x, ‖x‖ₑ ^ 2 ∂μ ≠ ∞)
    (h_tail : Tendsto (fun s : Finset ι ↦
      ⨆ μ ∈ S, ∫⁻ x, ‖x - ∑ i ∈ s, ⟪b i, x⟫ • b i‖ₑ ^ 2 ∂μ) atTop (𝓝 0)) :
    IsTightMeasureSet S := by
  -- Markov's inequality, uniformly over `S`
  have h_markov {f : E → E} (hf : Continuous f) (c : ℝ) (hc : 0 < c) :
      ⨆ μ ∈ S, μ {x | c < ‖f x‖} ≤
        (⨆ μ ∈ S, ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) / ENNReal.ofReal c ^ 2 := by
    refine iSup₂_le fun μ hμ ↦ ?_
    calc μ {x | c < ‖f x‖}
    _ ≤ μ {x | ENNReal.ofReal c ^ 2 ≤ ‖f x‖ₑ ^ 2} := by
      refine measure_mono fun x hx ↦ ?_
      simp only [mem_ofPred_eq] at hx ⊢
      rw [← ofReal_norm]
      gcongr
    _ ≤ (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) / ENNReal.ofReal c ^ 2 :=
      meas_ge_le_lintegral_div (hf.enorm.measurable.pow_const 2).aemeasurable
        (pow_ne_zero 2 (ENNReal.ofReal_pos.2 hc).ne') (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    _ ≤ (⨆ μ ∈ S, ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) / ENNReal.ofReal c ^ 2 := by
      gcongr
      exact le_iSup₂ (f := fun μ (_ : μ ∈ S) ↦ ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) μ hμ
  refine b.isTightMeasureSet_of_tendsto_measure ?_ fun ε hε ↦ ?_
  · have h_top : Tendsto (fun r : ℝ ↦ ENNReal.ofReal r ^ 2) atTop (𝓝 ∞) := by
      have := ((ENNReal.continuous_pow 2).tendsto ∞).comp ENNReal.tendsto_ofReal_atTop
      rwa [ENNReal.top_pow two_ne_zero] at this
    have h_lim := ENNReal.Tendsto.const_div h_top (Or.inr h_norm)
    rw [ENNReal.div_top] at h_lim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_lim
      (.of_forall fun _ ↦ zero_le) ?_
    filter_upwards [eventually_gt_atTop 0] with r hr
    exact h_markov continuous_id r hr
  · have h_lim := ENNReal.Tendsto.div_const h_tail
      (Or.inr (pow_ne_zero 2 (ENNReal.ofReal_pos.2 hε).ne'))
    rw [ENNReal.zero_div] at h_lim
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_lim (fun _ ↦ zero_le)
      fun s ↦ h_markov (by fun_prop) ε hε

/-- **Tightness in a Hilbert space from summable coordinate second moments.** Let `b` be a Hilbert
basis indexed by a countable type. If `∫⁻ x, ‖⟪b i, x⟫‖ₑ ^ 2 ∂μ ≤ c i` for all `μ ∈ S` and all
`i`, where `∑' i, c i < ∞`, then `S` is tight. -/
theorem isTightMeasureSet_of_lintegral_inner_sq_le [Countable ι] [OpensMeasurableSpace E]
    {c : ι → ℝ≥0∞} (hc : ∑' i, c i ≠ ∞)
    (h : ∀ μ ∈ S, ∀ i, ∫⁻ x, ‖⟪b i, x⟫‖ₑ ^ 2 ∂μ ≤ c i) :
    IsTightMeasureSet S := by
  have h_tail (s : Finset ι) : ⨆ μ ∈ S, ∫⁻ x, ‖x - ∑ i ∈ s, ⟪b i, x⟫ • b i‖ₑ ^ 2 ∂μ ≤
      ∑' i, (s : Set ι)ᶜ.indicator c i := by
    refine iSup₂_le fun μ hμ ↦ ?_
    simp_rw [← b.tsum_indicator_enorm_inner_sq]
    rw [lintegral_tsum fun i ↦ ?_]
    · refine tsum_le_tsum fun i ↦ ?_
      by_cases hi : i ∈ (s : Set ι)ᶜ
      · simpa only [Set.indicator_of_mem hi] using h μ hμ i
      · simp [hi]
    · by_cases hi : i ∈ (s : Set ι)ᶜ
      · simp only [Set.indicator_of_mem hi]
        exact ((continuous_const.inner continuous_id).enorm.measurable.pow_const 2).aemeasurable
      · simp [hi]
  refine b.isTightMeasureSet_of_lintegral (ne_top_of_le_ne_top hc ?_) ?_
  · simpa using h_tail ∅
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le) h_tail
    convert ENNReal.tendsto_tsum_compl_atTop_zero hc using 2 with s
    exact (tsum_subtype ((s : Set ι)ᶜ) c).symm

end HilbertBasis
