/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.MeasureTheory.Measure.Doubling
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Covering.Differentiation

/-!
# Uniformly locally doubling measures and Lebesgue's density theorem

Lebesgue's density theorem states that given a set `S` in a sigma compact metric space with
locally-finite uniformly locally doubling measure `μ` then for almost all points `x` in `S`, for any
sequence of closed balls `B₀, B₁, B₂, ...` containing `x`, the limit `μ (S ∩ Bⱼ) / μ (Bⱼ) → 1` as
`j → ∞`.

In this file we combine general results about existence of Vitali families for uniformly locally
doubling measures with results about differentiation along a Vitali family to obtain an explicit
form of Lebesgue's density theorem.

## Main results
* `IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div`: a version of Lebesgue's density
  theorem for sequences of balls converging on a point but whose centres are not required to be
  fixed.

-/


noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace

open scoped NNReal Topology

namespace IsUnifLocDoublingMeasure

variable {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α] (μ : Measure α)
  [IsUnifLocDoublingMeasure μ]

section

variable [SecondCountableTopology α] [BorelSpace α] [IsLocallyFiniteMeasure μ]

open scoped Topology

/-- A Vitali family in a space with a uniformly locally doubling measure, designed so that the sets
at `x` contain all `closedBall y r` when `dist x y ≤ K * r`. -/
irreducible_def vitaliFamily (K : ℝ) : VitaliFamily μ := by
  /- the Vitali covering theorem gives a family that works well at small scales, thanks to the
    doubling property. We enlarge this family to add large sets, to make sure that all balls and not
    only small ones belong to the family, for convenience. -/
  let R := scalingScaleOf μ (max (4 * K + 3) 3)
  have Rpos : 0 < R := scalingScaleOf_pos _ _
  have A : ∀ x : α, ∃ᶠ r in 𝓝[>] (0 : ℝ),
      μ (closedBall x (3 * r)) ≤ scalingConstantOf μ (max (4 * K + 3) 3) * μ (closedBall x r) := by
    intro x
    apply frequently_iff.2 fun {U} hU => ?_
    obtain ⟨ε, εpos, hε⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 hU
    refine ⟨min ε R, hε ⟨lt_min εpos Rpos, min_le_left _ _⟩, ?_⟩
    exact measure_mul_le_scalingConstantOf_mul μ
      ⟨zero_lt_three, le_max_right _ _⟩ (min_le_right _ _)
  exact (Vitali.vitaliFamily μ (scalingConstantOf μ (max (4 * K + 3) 3)) A).enlarge (R / 4)
    (by linarith)

/-- In the Vitali family `IsUnifLocDoublingMeasure.vitaliFamily K`, the sets based at `x`
contain all balls `closedBall y r` when `dist x y ≤ K * r`. -/
theorem closedBall_mem_vitaliFamily_of_dist_le_mul {K : ℝ} {x y : α} {r : ℝ} (h : dist x y ≤ K * r)
    (rpos : 0 < r) : closedBall y r ∈ (vitaliFamily μ K).setsAt x := by
  let R := scalingScaleOf μ (max (4 * K + 3) 3)
  simp only [vitaliFamily, VitaliFamily.enlarge, Vitali.vitaliFamily, mem_union, mem_setOf_eq,
    isClosed_closedBall, true_and, (nonempty_ball.2 rpos).mono ball_subset_interior_closedBall,
    measurableSet_closedBall]
  /- The measure is doubling on scales smaller than `R`. Therefore, we treat differently small
    and large balls. For large balls, this follows directly from the enlargement we used in the
    definition. -/
  by_cases H : closedBall y r ⊆ closedBall x (R / 4)
  swap; · exact Or.inr H
  left
  /- For small balls, there is the difficulty that `r` could be large but still the ball could be
    small, if the annulus `{y | ε ≤ dist y x ≤ R/4}` is empty. We split between the cases `r ≤ R`
    and `r > R`, and use the doubling for the former and rough estimates for the latter. -/
  rcases le_or_gt r R with (hr | hr)
  · refine ⟨(K + 1) * r, ?_⟩
    constructor
    · apply closedBall_subset_closedBall'
      rw [dist_comm]
      linarith
    · have I1 : closedBall x (3 * ((K + 1) * r)) ⊆ closedBall y ((4 * K + 3) * r) := by
        apply closedBall_subset_closedBall'
        linarith
      have I2 : closedBall y ((4 * K + 3) * r) ⊆ closedBall y (max (4 * K + 3) 3 * r) := by
        apply closedBall_subset_closedBall
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) rpos.le
      apply (measure_mono (I1.trans I2)).trans
      exact measure_mul_le_scalingConstantOf_mul _
        ⟨zero_lt_three.trans_le (le_max_right _ _), le_rfl⟩ hr
  · refine ⟨R / 4, H, ?_⟩
    have : closedBall x (3 * (R / 4)) ⊆ closedBall y r := by
      apply closedBall_subset_closedBall'
      have A : y ∈ closedBall y r := mem_closedBall_self rpos.le
      have B := mem_closedBall'.1 (H A)
      linarith
    apply (measure_mono this).trans _
    refine le_mul_of_one_le_left (zero_le _) ?_
    exact ENNReal.one_le_coe_iff.2 (le_max_right _ _)

theorem tendsto_closedBall_filterAt {K : ℝ} {x : α} {ι : Type*} {l : Filter ι} (w : ι → α)
    (δ : ι → ℝ) (δlim : Tendsto δ l (𝓝[>] 0)) (xmem : ∀ᶠ j in l, x ∈ closedBall (w j) (K * δ j)) :
    Tendsto (fun j => closedBall (w j) (δ j)) l ((vitaliFamily μ K).filterAt x) := by
  refine (vitaliFamily μ K).tendsto_filterAt_iff.mpr ⟨?_, fun ε hε => ?_⟩
  · filter_upwards [xmem, δlim self_mem_nhdsWithin] with j hj h'j
    exact closedBall_mem_vitaliFamily_of_dist_le_mul μ hj h'j
  · rcases l.eq_or_neBot with rfl | h
    · simp
    have hK : 0 ≤ K := by
      rcases (xmem.and (δlim self_mem_nhdsWithin)).exists with ⟨j, hj, h'j⟩
      have : 0 ≤ K * δ j := nonempty_closedBall.1 ⟨x, hj⟩
      exact (mul_nonneg_iff_left_nonneg_of_pos (mem_Ioi.1 h'j)).1 this
    have δpos := eventually_mem_of_tendsto_nhdsWithin δlim
    replace δlim := tendsto_nhds_of_tendsto_nhdsWithin δlim
    replace hK : 0 < K + 1 := by linarith
    apply (((Metric.tendsto_nhds.mp δlim _ (div_pos hε hK)).and δpos).and xmem).mono
    rintro j ⟨⟨hjε, hj₀ : 0 < δ j⟩, hx⟩ y hy
    replace hjε : (K + 1) * δ j < ε := by
      simpa [abs_eq_self.mpr hj₀.le] using (lt_div_iff₀' hK).mp hjε
    simp only [mem_closedBall] at hx hy ⊢
    linarith [dist_triangle_right y x (w j)]

end

section Applications

variable [SecondCountableTopology α] [BorelSpace α] [IsLocallyFiniteMeasure μ] {E : Type*}
  [NormedAddCommGroup E]

/-- A version of **Lebesgue's density theorem** for a sequence of closed balls whose centers are
not required to be fixed.

See also `Besicovitch.ae_tendsto_measure_inter_div`. -/
theorem ae_tendsto_measure_inter_div (S : Set α) (K : ℝ) : ∀ᵐ x ∂μ.restrict S,
    ∀ {ι : Type*} {l : Filter ι} (w : ι → α) (δ : ι → ℝ) (_ : Tendsto δ l (𝓝[>] 0))
      (_ : ∀ᶠ j in l, x ∈ closedBall (w j) (K * δ j)),
      Tendsto (fun j => μ (S ∩ closedBall (w j) (δ j)) / μ (closedBall (w j) (δ j))) l (𝓝 1) := by
  filter_upwards [(vitaliFamily μ K).ae_tendsto_measure_inter_div S] with x hx ι l w δ δlim
    xmem using hx.comp (tendsto_closedBall_filterAt μ _ _ δlim xmem)

/-- A version of **Lebesgue differentiation theorem** for a sequence of closed balls whose
centers are not required to be fixed. -/
theorem ae_tendsto_average_norm_sub {f : α → E} (hf : LocallyIntegrable f μ) (K : ℝ) : ∀ᵐ x ∂μ,
    ∀ {ι : Type*} {l : Filter ι} (w : ι → α) (δ : ι → ℝ) (_ : Tendsto δ l (𝓝[>] 0))
      (_ : ∀ᶠ j in l, x ∈ closedBall (w j) (K * δ j)),
      Tendsto (fun j => ⨍ y in closedBall (w j) (δ j), ‖f y - f x‖ ∂μ) l (𝓝 0) := by
  filter_upwards [(vitaliFamily μ K).ae_tendsto_average_norm_sub hf] with x hx ι l w δ δlim
    xmem using hx.comp (tendsto_closedBall_filterAt μ _ _ δlim xmem)

/-- A version of **Lebesgue differentiation theorem** for a sequence of closed balls whose
centers are not required to be fixed. -/
theorem ae_tendsto_average [NormedSpace ℝ E] [CompleteSpace E]
    {f : α → E} (hf : LocallyIntegrable f μ) (K : ℝ) : ∀ᵐ x ∂μ,
      ∀ {ι : Type*} {l : Filter ι} (w : ι → α) (δ : ι → ℝ) (_ : Tendsto δ l (𝓝[>] 0))
        (_ : ∀ᶠ j in l, x ∈ closedBall (w j) (K * δ j)),
        Tendsto (fun j => ⨍ y in closedBall (w j) (δ j), f y ∂μ) l (𝓝 (f x)) := by
  filter_upwards [(vitaliFamily μ K).ae_tendsto_average hf] with x hx ι l w δ δlim xmem using
    hx.comp (tendsto_closedBall_filterAt μ _ _ δlim xmem)

end Applications

end IsUnifLocDoublingMeasure
