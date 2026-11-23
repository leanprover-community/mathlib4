/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.MeasureTheory.Covering.ClosedBallCovering
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
* `IsUnifLocDoublingMeasure.closedBallCoveringMeasure`: a locally finite uniformly locally doubling
  measure has the closed ball covering property,
  see `MeasureTheory.Measure.ClosedBallCoveringMeasure`.
* `IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div`: a version of Lebesgue's density
  theorem for sequences of balls converging on a point but whose centres are not required to be
  fixed.
-/

public section


noncomputable section

open Set Filter Metric MeasureTheory

open scoped NNReal ENNReal Topology

namespace IsUnifLocDoublingMeasure

variable {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α] (μ : Measure α)
  [IsUnifLocDoublingMeasure μ]

/-- In a space with a uniformly locally doubling measure, any null set `s` can be covered with
closed balls whose measures add up to at most `ε`, for any positive `ε`. This works even if one
restricts the set of allowed radii around a point `x` to a set `f x` which accumulates at `0`.

See `MeasureTheory.Measure.exists_closedBall_covering_tsum_measure_le` for a version for any set `s`
in a space with the Besicovitch covering property. -/
theorem exists_closedBall_covering_tsum_measure_le_of_measure_eq_zero
    [OpensMeasurableSpace α] [SecondCountableTopology α] [μ.OuterRegular]
    {ε : ℝ≥0∞} (hε : ε ≠ 0) (f : α → Set ℝ) {s : Set α} (hμs : μ s = 0)
    (hf : ∀ x ∈ s, ∀ δ > 0, (f x ∩ Ioo 0 δ).Nonempty) :
    ∃ (t : Set α) (r : α → ℝ), t.Countable ∧ t ⊆ s ∧ (∀ x ∈ t, r x ∈ f x) ∧
      s ⊆ ⋃ x ∈ t, closedBall x (r x) ∧ ∑' x : t, μ (closedBall x (r x)) ≤ ε := by
  /- Choose an open set `U ⊇ s` of measure less than `ε / C`, where `C` is the doubling constant
  for the ratio `4`. Cover `s` by balls `closedBall x (4 * r x)` such that the balls
  `closedBall x (r x)` are pairwise disjoint and are included in `U`. -/
  obtain ⟨U, hsU, hUo, hμU⟩ : ∃ U ⊇ s, IsOpen U ∧ μ U < ε / scalingConstantOf μ 4 :=
    s.exists_isOpen_lt_of_lt _ <| by
      rw [hμs]
      exact ENNReal.div_pos hε ENNReal.coe_ne_top
  have : ∀ x ∈ s, ∃ r > 0, r ≤ scalingScaleOf μ 4 ∧ 4 * r ∈ f x ∧ closedBall x r ⊆ U := by
    intro x hx
    rcases nhds_basis_closedBall.mem_iff.mp (hUo.mem_nhds (hsU hx)) with ⟨δ, hδ₀, hδU⟩
    have := scalingScaleOf_pos μ 4
    rcases hf x hx (min δ (4 * scalingScaleOf μ 4)) (by positivity) with ⟨r, hfr, hr₀, hr⟩
    rw [lt_min_iff] at hr
    refine ⟨r / 4, by positivity, by linarith, by rwa [mul_div_cancel₀ _ four_ne_zero], ?_⟩
    exact (closedBall_subset_closedBall (by linarith)).trans hδU
  choose! r hr₀ hrR hrf hrU using this
  obtain ⟨t, hts, ht_disj, ht_covers⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall s id r _ hrR 4
      (by norm_num)
  simp only [id] at ht_disj ht_covers
  have htc : t.Countable := ht_disj.countable_of_nonempty_interior fun x hx ↦
    (nonempty_ball.2 (hr₀ x (hts hx))).mono ball_subset_interior_closedBall
  refine ⟨t, (4 * r ·), htc, hts, fun x hx ↦ hrf x (hts hx), fun x hx ↦ ?_, ?_⟩
  · rcases ht_covers x hx with ⟨y, hyt, hxy⟩
    exact mem_biUnion hyt (hxy <| mem_closedBall_self (hr₀ x hx).le)
  · calc ∑' x : t, μ (closedBall x (4 * r x))
      _ ≤ ∑' x : t, scalingConstantOf μ 4 * μ (closedBall x (r x)) := by
        gcongr with x
        exact measure_mul_le_scalingConstantOf_mul μ (by simp) (hrR x (hts x.2))
      _ = scalingConstantOf μ 4 * μ (⋃ x ∈ t, closedBall x (r x)) := by
        rw [measure_biUnion htc ht_disj fun _ _ ↦ measurableSet_closedBall,
          ENNReal.tsum_mul_left]
      _ ≤ scalingConstantOf μ 4 * μ U := by
        gcongr
        exact iUnion₂_subset fun x hx ↦ hrU x (hts hx)
      _ ≤ ε := by
        grw [hμU, ENNReal.mul_div_cancel]
        · simp [(one_pos.trans_le (one_le_scalingConstantOf _ _)).ne']
        · simp

section

variable [SecondCountableTopology α] [BorelSpace α] [IsLocallyFiniteMeasure μ]

open scoped Topology

/-- A Vitali family in a space with a uniformly locally doubling measure, designed so that the sets
at `x` contain all `closedBall y r` when `dist x y ≤ K * r`. -/
def vitaliFamily (K : ℝ) : VitaliFamily μ := by
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
  simp only [vitaliFamily, VitaliFamily.enlarge, Vitali.vitaliFamily, mem_union, mem_ofPred_eq,
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
        gcongr
        exact le_max_left ..
      apply (measure_mono (I1.trans I2)).trans
      exact measure_mul_le_scalingConstantOf_mul _
        ⟨zero_lt_three.trans_le (le_max_right _ _), le_rfl⟩ hr
  · refine ⟨_, H, ?_⟩
    grw [scalingConstantOf, ← le_max_right, ENNReal.coe_one, one_mul,
      closedBall_subset_closedBall' (y := y)]
    have A : y ∈ closedBall y r := mem_closedBall_self rpos.le
    have B := mem_closedBall'.1 (H A)
    linarith

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

/-- A locally finite uniformly locally doubling measure has the closed ball covering property:
any set `s` can be covered by closed balls centered at the points of `s`
whose measures add up to at most `μ s + ε`. -/
instance closedBallCoveringMeasure : Measure.ClosedBallCoveringMeasure μ :=
  .of_vitaliFamily (vitaliFamily μ 0)
    (fun x ↦ tendsto_closedBall_filterAt μ (fun _ ↦ x) id tendsto_id (.of_forall fun _ ↦ by simp))
    fun _ hε f _ hs hf ↦ exists_closedBall_covering_tsum_measure_le_of_measure_eq_zero μ hε f hs hf

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
