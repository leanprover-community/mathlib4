/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.MeasureTheory.Covering.Differentiation
public import Mathlib.MeasureTheory.Covering.Vitali

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

public section


noncomputable section

open Set Filter Metric MeasureTheory

open scoped NNReal Topology

namespace IsUnifLocDoublingMeasure

variable {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α] (μ : Measure α)
  [IsUnifLocDoublingMeasure μ]

section

variable [SecondCountableTopology α] [BorelSpace α] [IsLocallyFiniteMeasure μ]

open scoped Topology

omit [SecondCountableTopology α] [BorelSpace α] [IsLocallyFiniteMeasure μ] in
/-- A uniformly locally doubling measure is doubling at all small enough scales around every point,
with a uniform constant. -/
private theorem frequently_measure_closedBall_three_mul_le (x : α) :
    ∃ᶠ r in 𝓝[>] 0, μ (closedBall x (3 * r)) ≤ scalingConstantOf μ 3 * μ (closedBall x r) :=
  Eventually.frequently <| by
    filter_upwards [Ioc_mem_nhdsGT (scalingScaleOf_pos μ 3)] with r hr
    exact measure_mul_le_scalingConstantOf_mul μ ⟨zero_lt_three, le_rfl⟩ hr.2

/-- A Vitali family in a space with a uniformly locally doubling measure. For any `K`, the sets at
`x` contain all small enough balls `closedBall y r` with `dist x y ≤ K * r`,
see `IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt`. -/
def vitaliFamily : VitaliFamily μ :=
  Vitali.vitaliFamilyOfForall μ (fun _ ↦ scalingConstantOf μ 3)
    (frequently_measure_closedBall_three_mul_le μ)

omit [SecondCountableTopology α] [BorelSpace α] [IsLocallyFiniteMeasure μ] in
/-- Auxiliary lemma for `tendsto_closedBall_filterAt`: in the Vitali family
`IsUnifLocDoublingMeasure.vitaliFamily`, the sets based at `x`
contain all balls `closedBall y r` when `dist x y ≤ K * r` and `r` is small enough. -/
private theorem closedBall_mem_of_dist_le_mul {K : ℝ} {x y : α} {r : ℝ}
    (h : dist x y ≤ K * r) (rpos : 0 < r) (hr : r ≤ scalingScaleOf μ (max (4 * K + 3) 3)) :
    IsClosed (closedBall y r) ∧ (interior (closedBall y r)).Nonempty ∧
      ∃ r', closedBall y r ⊆ closedBall x r' ∧
        μ (closedBall x (3 * r')) ≤
          scalingConstantOf μ (max (4 * K + 3) 3) * μ (closedBall y r) := by
  refine ⟨isClosed_closedBall, (nonempty_ball.2 rpos).mono ball_subset_interior_closedBall,
    (K + 1) * r, ?_, ?_⟩
  · apply closedBall_subset_closedBall'
    rw [dist_comm]
    linarith
  · have I1 : closedBall x (3 * ((K + 1) * r)) ⊆ closedBall y ((4 * K + 3) * r) := by
      apply closedBall_subset_closedBall'
      linarith
    have I2 : closedBall y ((4 * K + 3) * r) ⊆ closedBall y (max (4 * K + 3) 3 * r) := by
      gcongr
      exact le_max_left ..
    apply (measure_mono (I1.trans I2)).trans
    exact measure_mul_le_scalingConstantOf_mul _
      ⟨zero_lt_three.trans_le (le_max_right _ _), le_rfl⟩ hr

/-- The closed balls `closedBall (w j) (δ j)` tend to `(vitaliFamily μ).filterAt x`
whenever `δ j → 0⁺` and eventually `x ∈ closedBall (w j) (K * δ j)`. -/
theorem tendsto_closedBall_filterAt {K : ℝ} {x : α} {ι : Type*} {l : Filter ι} (w : ι → α)
    (δ : ι → ℝ) (δlim : Tendsto δ l (𝓝[>] 0)) (xmem : ∀ᶠ j in l, x ∈ closedBall (w j) (K * δ j)) :
    Tendsto (fun j => closedBall (w j) (δ j)) l ((vitaliFamily μ).filterAt x) := by
  rw [vitaliFamily, Vitali.filterAt_vitaliFamily_of_exists _ _
    ⟨_, frequently_measure_closedBall_three_mul_le μ x⟩]
  refine Tendsto.mono_right ?_ (le_iSup _ (scalingConstantOf μ (max (4 * K + 3) 3)))
  rw [tendsto_inf, tendsto_principal, nhds_basis_closedBall.smallSets.tendsto_right_iff]
  have δpos := eventually_mem_of_tendsto_nhdsWithin δlim
  replace δlim := tendsto_nhds_of_tendsto_nhdsWithin δlim
  refine ⟨fun ε hε => ?_, ?_⟩
  · rcases l.eq_or_neBot with rfl | h
    · simp
    have hK : 0 ≤ K := by
      rcases (xmem.and δpos).exists with ⟨j, hj, h'j⟩
      have : 0 ≤ K * δ j := nonempty_closedBall.1 ⟨x, hj⟩
      exact (mul_nonneg_iff_left_nonneg_of_pos (mem_Ioi.1 h'j)).1 this
    replace hK : 0 < K + 1 := by linarith
    apply (((Metric.tendsto_nhds.mp δlim _ (div_pos hε hK)).and δpos).and xmem).mono
    rintro j ⟨⟨hjε, hj₀ : 0 < δ j⟩, hx⟩ y hy
    replace hjε : (K + 1) * δ j < ε := by
      simpa [abs_eq_self.mpr hj₀.le] using (lt_div_iff₀' hK).mp hjε
    simp only [mem_closedBall] at hx hy ⊢
    linarith [dist_triangle_right y x (w j)]
  · filter_upwards [xmem, δpos, δlim.eventually (gt_mem_nhds (scalingScaleOf_pos μ _))]
      with j hj h'j h''j
    exact closedBall_mem_of_dist_le_mul μ hj h'j h''j.le

/-- Closed balls centered at `x` tend to `(vitaliFamily μ).filterAt x`
as their radius tends to `0`. -/
theorem tendsto_closedBall_filterAt_self (x : α) :
    Tendsto (closedBall x) (𝓝[>] 0) ((vitaliFamily μ).filterAt x) :=
  tendsto_closedBall_filterAt μ (K := 0) (fun _ ↦ x) id tendsto_id (by simp)

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
  filter_upwards [(vitaliFamily μ).ae_tendsto_measure_inter_div S] with x hx ι l w δ δlim
    xmem using hx.comp (tendsto_closedBall_filterAt μ _ _ δlim xmem)

/-- A version of **Lebesgue differentiation theorem** for a sequence of closed balls whose
centers are not required to be fixed. -/
theorem ae_tendsto_average_norm_sub {f : α → E} (hf : LocallyIntegrable f μ) (K : ℝ) : ∀ᵐ x ∂μ,
    ∀ {ι : Type*} {l : Filter ι} (w : ι → α) (δ : ι → ℝ) (_ : Tendsto δ l (𝓝[>] 0))
      (_ : ∀ᶠ j in l, x ∈ closedBall (w j) (K * δ j)),
      Tendsto (fun j => ⨍ y in closedBall (w j) (δ j), ‖f y - f x‖ ∂μ) l (𝓝 0) := by
  filter_upwards [(vitaliFamily μ).ae_tendsto_average_norm_sub hf] with x hx ι l w δ δlim
    xmem using hx.comp (tendsto_closedBall_filterAt μ _ _ δlim xmem)

/-- A version of **Lebesgue differentiation theorem** for a sequence of closed balls whose
centers are not required to be fixed. -/
theorem ae_tendsto_average [NormedSpace ℝ E] [CompleteSpace E]
    {f : α → E} (hf : LocallyIntegrable f μ) (K : ℝ) : ∀ᵐ x ∂μ,
      ∀ {ι : Type*} {l : Filter ι} (w : ι → α) (δ : ι → ℝ) (_ : Tendsto δ l (𝓝[>] 0))
        (_ : ∀ᶠ j in l, x ∈ closedBall (w j) (K * δ j)),
        Tendsto (fun j => ⨍ y in closedBall (w j) (δ j), f y ∂μ) l (𝓝 (f x)) := by
  filter_upwards [(vitaliFamily μ).ae_tendsto_average hf] with x hx ι l w δ δlim xmem using
    hx.comp (tendsto_closedBall_filterAt μ _ _ δlim xmem)

end Applications

end IsUnifLocDoublingMeasure
