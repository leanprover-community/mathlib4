/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Covering.VitaliFamily
public import Mathlib.MeasureTheory.Measure.Regular

/-!
# Measures with the closed ball covering property

In this file we define a typeclass `MeasureTheory.Measure.ClosedBallCoveringMeasure μ` saying that
any set `s` (possibly non-measurable) can be covered by countably many closed balls
centered at the points of `s` such that the sum of their measures is at most `μ s + ε`.
Moreover, one can restrict the set of allowed radii at each point `x`
to any set `f x` that accumulates at `0`.

In contrast to Vitali families, which provide disjoint coverings of *almost all* of `s`,
this property gives a covering of *all* of `s`.
This makes it possible to estimate the outer measure `ν s`
for an outer measure `ν` that is not known to be absolutely continuous with respect to `μ`.

## Main results

* `MeasureTheory.Measure.ClosedBallCoveringMeasure`: the typeclass;
* `MeasureTheory.Measure.exists_closedBall_covering_tsum_measure_le`: the covering property;
* `MeasureTheory.Measure.ClosedBallCoveringMeasure.of_ae_of_null`: a measure has this property,
  if it is outer regular, a.e. point of any set can be covered by disjoint closed balls,
  and any null set can be covered by closed balls of arbitrarily small total measure;
* `MeasureTheory.Measure.ClosedBallCoveringMeasure.of_vitaliFamily`: a version of the previous
  constructor that takes the a.e. covering from a Vitali family `v`
  such that closed balls centered at `x` converge to `x` along `v`;
* `MeasureTheory.Measure.outerMeasure_le_mul`: if `μ` is σ-finite,
  `ν` is an outer measure, and for all `x ∈ s` and `C' > C`, the inequality
  `ν (s ∩ closedBall x r) ≤ C' * μ (closedBall x r)` holds for arbitrarily small `r > 0`,
  then `ν s ≤ C * μ s`;
* `MeasureTheory.Measure.outerMeasure_null_of_null_of_forall_exists_le_mul`:
  if `μ s = 0` and for all `x ∈ s` we have `ν (s ∩ closedBall x r) ≤ C x * μ (closedBall x r)`
  for arbitrarily small `r > 0`, then `ν s = 0`;
* `MeasureTheory.Measure.measure_image_le_mul`,
  `MeasureTheory.Measure.measure_image_null_of_null_of_forall_exists_le_mul`:
  versions of the previous two results for `ν (f '' s)`.

The instances are proved in other files:
* for a measure in a space with the Besicovitch covering property,
  see `Mathlib/MeasureTheory/Covering/Besicovitch.lean`;
* for a uniformly locally doubling measure,
  see `Mathlib/MeasureTheory/Covering/DensityTheorem.lean`.
-/

public section

open Set Filter Metric
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Measure

variable {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α] {μ : Measure α}

/-- We say that a measure `μ` on a metric space has the *closed ball covering property*,
if for any set `s`, for any `ε > 0`, and for any family of sets `f x` accumulating at `0`,
there exists a countable set of points `t ⊆ s` and radii `r x ∈ f x`
such that the closed balls `closedBall x (r x)`, `x ∈ t`, cover `s`,
and the sum of their measures is at most `μ s + ε`.

This property holds for locally finite measures in spaces with the Besicovitch covering property
(e.g., finite-dimensional real normed spaces),
and for uniformly locally doubling measures. -/
class ClosedBallCoveringMeasure (μ : Measure α) : Prop where
  exists_closedBall_covering_tsum_measure_le {ε : ℝ≥0∞} (hε : ε ≠ 0) (f : α → Set ℝ) (s : Set α)
    (hf : ∀ x ∈ s, ∀ δ > 0, (f x ∩ Ioo 0 δ).Nonempty) :
    ∃ (t : Set α) (r : α → ℝ), t.Countable ∧ t ⊆ s ∧ (∀ x ∈ t, r x ∈ f x) ∧
      s ⊆ ⋃ x ∈ t, closedBall x (r x) ∧ ∑' x : t, μ (closedBall x (r x)) ≤ μ s + ε

/-- If `μ` has the closed ball covering property, then any set `s` can be covered with closed balls
centered at the points of `s` whose measures add up to at most `μ s + ε`, for any positive `ε`.
This works even if one restricts the set of allowed radii around a point `x` to a set `f x`
which accumulates at `0`. -/
theorem exists_closedBall_covering_tsum_measure_le (μ : Measure α) [ClosedBallCoveringMeasure μ]
    {ε : ℝ≥0∞} (hε : ε ≠ 0) (f : α → Set ℝ) (s : Set α)
    (hf : ∀ x ∈ s, ∀ δ > 0, (f x ∩ Ioo 0 δ).Nonempty) :
    ∃ (t : Set α) (r : α → ℝ), t.Countable ∧ t ⊆ s ∧ (∀ x ∈ t, r x ∈ f x) ∧
      s ⊆ ⋃ x ∈ t, closedBall x (r x) ∧ ∑' x : t, μ (closedBall x (r x)) ≤ μ s + ε :=
  ClosedBallCoveringMeasure.exists_closedBall_covering_tsum_measure_le hε f s hf

namespace ClosedBallCoveringMeasure

/-- An outer regular measure `μ` has the closed ball covering property, if

- almost every point of any set `s` can be covered by disjoint closed balls
  centered at the points of `s` with radii in prescribed sets `f x` accumulating at zero;
- any null set can be covered by closed balls with radii in prescribed sets `f x`
  whose measures add up to an arbitrarily small number. -/
theorem of_ae_of_null [OpensMeasurableSpace α] [μ.OuterRegular]
    (hae : ∀ (f : α → Set ℝ) (s : Set α), (∀ x ∈ s, ∀ δ > 0, (f x ∩ Ioo 0 δ).Nonempty) →
      ∃ (t : Set α) (r : α → ℝ), t.Countable ∧ t ⊆ s ∧ (∀ x ∈ t, r x ∈ f x) ∧
        μ (s \ ⋃ x ∈ t, closedBall x (r x)) = 0 ∧ t.PairwiseDisjoint fun x ↦ closedBall x (r x))
    (hnull : ∀ ε ≠ 0, ∀ (f : α → Set ℝ) (s : Set α), μ s = 0 →
      (∀ x ∈ s, ∀ δ > 0, (f x ∩ Ioo 0 δ).Nonempty) →
      ∃ (t : Set α) (r : α → ℝ), t.Countable ∧ t ⊆ s ∧ (∀ x ∈ t, r x ∈ f x) ∧
        s ⊆ ⋃ x ∈ t, closedBall x (r x) ∧ ∑' x : t, μ (closedBall x (r x)) ≤ ε) :
    ClosedBallCoveringMeasure μ where
  exists_closedBall_covering_tsum_measure_le {ε} hε f s hf := by
    classical
    /- Choose an open set `U ⊇ s` such that `μ U ≤ μ s + ε / 2`.
    Cover almost all of `s` by disjoint closed balls included in `U`,
    then cover the remaining null set by closed balls of total measure at most `ε / 2`. -/
    obtain ⟨U, hsU, hUo, hμU⟩ : ∃ U ⊇ s, IsOpen U ∧ μ U ≤ μ s + ε / 2 :=
      s.exists_isOpen_le_add μ (ENNReal.half_pos hε).ne'
    have : ∀ x ∈ s, ∃ R > 0, ball x R ⊆ U := fun x hx ↦ isOpen_iff.1 hUo x (hsU hx)
    choose! R hR₀ hRU using this
    obtain ⟨t₀, r₀, ht₀c, ht₀s, hr₀, hμt₀, ht₀d⟩ :=
      hae (fun x ↦ f x ∩ Ioo 0 (R x)) s fun x hx δ hδ ↦ by
        rcases hf x hx (min δ (R x)) (lt_min hδ (hR₀ x hx)) with ⟨r, hrf, hr₀, hr⟩
        rw [lt_min_iff] at hr
        exact ⟨r, ⟨hrf, hr₀, hr.2⟩, hr₀, hr.1⟩
    obtain ⟨t₁, r₁, ht₁c, ht₁s, hr₁, hst₁, hμt₁⟩ :=
      hnull (ε / 2) (ENNReal.half_pos hε).ne' f _ hμt₀ fun x hx ↦ hf x hx.1
    have hdisj : Disjoint t₀ t₁ := by
      refine Set.disjoint_left.2 fun x hx₀ hx₁ ↦ (ht₁s hx₁).2 ?_
      exact mem_biUnion hx₀ <| mem_closedBall_self (hr₀ x hx₀).2.1.le
    have hr_t₀ : ∀ x ∈ t₀, t₀.piecewise r₀ r₁ x = r₀ x := fun _ ↦ piecewise_eq_of_mem _ _ _
    have hr_t₁ : ∀ x ∈ t₁, t₀.piecewise r₀ r₁ x = r₁ x := fun _ hx ↦
      piecewise_eq_of_notMem _ _ _ (Set.disjoint_right.1 hdisj hx)
    refine ⟨t₀ ∪ t₁, t₀.piecewise r₀ r₁, ht₀c.union ht₁c,
      union_subset ht₀s (ht₁s.trans sdiff_subset), ?_, ?_, ?_⟩
    · rintro x (hx | hx)
      · exact hr_t₀ x hx ▸ (hr₀ x hx).1
      · exact hr_t₁ x hx ▸ hr₁ x hx
    · intro x hxs
      by_cases hx : x ∈ ⋃ y ∈ t₀, closedBall y (r₀ y)
      · rcases mem_iUnion₂.1 hx with ⟨y, hy, hxy⟩
        exact mem_biUnion (mem_union_left _ hy) (hr_t₀ y hy ▸ hxy)
      · rcases mem_iUnion₂.1 (hst₁ ⟨hxs, hx⟩) with ⟨y, hy, hxy⟩
        exact mem_biUnion (mem_union_right _ hy) (hr_t₁ y hy ▸ hxy)
    · calc
        ∑' x : ↥(t₀ ∪ t₁), μ (closedBall x (t₀.piecewise r₀ r₁ x))
          ≤ ∑' x : t₀, μ (closedBall x (t₀.piecewise r₀ r₁ x)) +
              ∑' x : t₁, μ (closedBall x (t₀.piecewise r₀ r₁ x)) :=
            tsum_union_le (fun x ↦ μ (closedBall x (t₀.piecewise r₀ r₁ x))) _ _
        _ = μ (⋃ x ∈ t₀, closedBall x (r₀ x)) + ∑' x : t₁, μ (closedBall x (r₁ x)) := by
          rw [measure_biUnion ht₀c ht₀d fun _ _ ↦ isClosed_closedBall.measurableSet]
          congr 1 <;> refine tsum_congr fun x ↦ ?_
          exacts [by rw [hr_t₀ x x.2], by rw [hr_t₁ x x.2]]
        _ ≤ μ U + ε / 2 := by
          refine add_le_add (measure_mono <| iUnion₂_subset fun x hx ↦ ?_) hμt₁
          exact (closedBall_subset_ball (hr₀ x hx).2.2).trans (hRU x (ht₀s hx))
        _ ≤ μ s + ε := by grw [hμU, add_assoc, ENNReal.add_halves]

end ClosedBallCoveringMeasure

end MeasureTheory.Measure

namespace VitaliFamily

open MeasureTheory

variable {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α] {μ : Measure α}

/-- Let `v` be a Vitali family such that the closed balls `closedBall x r` converge to `x` along `v`
as `r → 0+`. Then almost every point of any set `s` can be covered by disjoint closed balls
centered at the points of `s` with radii in prescribed sets `f x` accumulating at zero. -/
theorem exists_disjoint_closedBall_covering_ae [SecondCountableTopology α] (v : VitaliFamily μ)
    (hv : ∀ x, Tendsto (closedBall x) (𝓝[>] 0) (v.filterAt x)) (f : α → Set ℝ) (s : Set α)
    (hf : ∀ x ∈ s, ∀ δ > 0, (f x ∩ Ioo 0 δ).Nonempty) :
    ∃ (t : Set α) (r : α → ℝ), t.Countable ∧ t ⊆ s ∧ (∀ x ∈ t, r x ∈ f x) ∧
      μ (s \ ⋃ x ∈ t, closedBall x (r x)) = 0 ∧ t.PairwiseDisjoint fun x ↦ closedBall x (r x) := by
  classical
  have hfine : v.FineSubfamilyOn (fun x ↦ closedBall x '' (f x ∩ Ioi 0)) s := by
    refine v.fineSubfamilyOn_of_frequently _ _ fun x hx ↦ (hv x).frequently ?_
    refine (nhdsGT_basis 0).frequently_iff.2 fun δ hδ ↦ ?_
    rcases hf x hx δ hδ with ⟨r, hrf, hr⟩
    exact ⟨r, hr, mem_image_of_mem _ ⟨hrf, hr.1⟩⟩
  choose! ρ hρf hρ using fun p (hp : p ∈ hfine.index) ↦ hfine.covering_mem hp
  have hcenter : ∀ p ∈ hfine.index, p.1 ∈ p.2 := fun p hp ↦ by
    have := hρ p hp ▸ mem_closedBall_self (hρf p hp).2.le (x := p.1)
    exact this
  have hinj : InjOn Prod.fst hfine.index := fun p hp q hq hpq ↦
    hfine.covering_disjoint.elim hp hq <| not_disjoint_iff.2 ⟨p.1, hcenter p hp, hpq ▸ hcenter q hq⟩
  set r : α → ℝ := fun x ↦ if h : ∃ p ∈ hfine.index, p.1 = x then ρ h.choose else 0
  have hr : ∀ p ∈ hfine.index, closedBall p.1 (r p.1) = p.2 ∧ r p.1 ∈ f p.1 := by
    intro p hp
    have h : ∃ q ∈ hfine.index, q.1 = p.1 := ⟨p, hp, rfl⟩
    simp only [r, h, ↓reduceDIte, hinj h.choose_spec.1 hp h.choose_spec.2]
    exact ⟨hρ p hp, (hρf p hp).1⟩
  have hU : ⋃ x ∈ Prod.fst '' hfine.index, closedBall x (r x) = ⋃ p ∈ hfine.index, p.2 := by
    rw [biUnion_image]
    exact iUnion₂_congr fun p hp ↦ (hr p hp).1
  refine ⟨Prod.fst '' hfine.index, r, hfine.index_countable.image _, ?_, ?_, ?_, ?_⟩
  · exact image_subset_iff.2 hfine.index_subset
  · exact forall_mem_image.2 fun p hp ↦ (hr p hp).2
  · exact hU ▸ hfine.measure_sdiff_biUnion
  · rw [hinj.pairwiseDisjoint_image]
    exact hfine.covering_disjoint.mono_on fun p hp ↦ (hr p hp).1.le

end VitaliFamily

namespace MeasureTheory.Measure.ClosedBallCoveringMeasure

variable {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α] {μ : Measure α}

/-- An outer regular measure `μ` has the closed ball covering property, if

- there exists a Vitali family `v` for `μ` such that the closed balls `closedBall x r` converge to
  `x` along `v` as `r → 0+`;
- any null set can be covered by closed balls with radii in prescribed sets `f x`
  whose measures add up to an arbitrarily small number. -/
theorem of_vitaliFamily [OpensMeasurableSpace α] [SecondCountableTopology α] [μ.OuterRegular]
    (v : VitaliFamily μ) (hv : ∀ x, Tendsto (closedBall x) (𝓝[>] 0) (v.filterAt x))
    (hnull : ∀ ε ≠ 0, ∀ (f : α → Set ℝ) (s : Set α), μ s = 0 →
      (∀ x ∈ s, ∀ δ > 0, (f x ∩ Ioo 0 δ).Nonempty) →
      ∃ (t : Set α) (r : α → ℝ), t.Countable ∧ t ⊆ s ∧ (∀ x ∈ t, r x ∈ f x) ∧
        s ⊆ ⋃ x ∈ t, closedBall x (r x) ∧ ∑' x : t, μ (closedBall x (r x)) ≤ ε) :
    ClosedBallCoveringMeasure μ :=
  of_ae_of_null (v.exists_disjoint_closedBall_covering_ae hv) hnull

end MeasureTheory.Measure.ClosedBallCoveringMeasure

/-!
### Bounds on outer measures

In this section we prove that `ν s ≤ C * μ s` for an outer measure `ν`,
if for every point `x ∈ s` and every `C' > C`, the inequality
`ν (s ∩ closedBall x r) ≤ C' * μ (closedBall x r)` holds for arbitrarily small `r > 0`,
i.e., if "the lower density of `ν` restricted to `s` with respect to `μ`" is at most `C` on `s`.
We also prove versions of this statement for the images of sets under maps
and for the case `C = 0`.
-/

namespace MeasureTheory.Measure

variable {α β : Type*} [PseudoMetricSpace α] [MeasurableSpace α] {μ : Measure α}
  [ClosedBallCoveringMeasure μ] {ν : OuterMeasure α} {C : ℝ≥0∞} {s : Set α}

/-- Let `μ` be a measure with the closed ball covering property, let `ν` be an outer measure.
Let `s` be a set, let `C` be a constant such that `μ s ≠ 0 ∨ C ≠ ∞` and `C ≠ 0 ∨ μ s ≠ ∞`.
Suppose that for each `x ∈ s` and each `C' > C`, the inequality
`ν (s ∩ closedBall x r) ≤ C' * μ (closedBall x r)` holds for arbitrarily small `r > 0`.
Then `ν s ≤ C * μ s`.

See `MeasureTheory.Measure.outerMeasure_le_mul` for a version that assumes `μ` to be σ-finite
instead of `C ≠ 0 ∨ μ s ≠ ∞`. -/
theorem outerMeasure_le_mul' (hsC : μ s ≠ 0 ∨ C ≠ ∞) (hCs : C ≠ 0 ∨ μ s ≠ ∞)
    (h : ∀ x ∈ s, ∀ C' > C, ∃ᶠ r in 𝓝[>] 0, ν (s ∩ closedBall x r) ≤ C' * μ (closedBall x r)) :
    ν s ≤ C * μ s := by
  rcases eq_or_ne C ∞ with rfl | hC
  · rw [ENNReal.top_mul (hsC.resolve_right fun h ↦ h rfl)]
    exact le_top
  -- It suffices to prove `ν s ≤ (C + ε) * (μ s + ε)` for all `ε > 0`.
  suffices ∀ ε > 0, ν s ≤ (C + ε) * (μ s + ε) by
    have H : Tendsto (fun ε ↦ (C + ε) * (μ s + ε)) (𝓝 0) (𝓝 (C * μ s)) := by
      apply ENNReal.Tendsto.mul <;>
        first | assumption | simpa using tendsto_const_nhds.add (tendsto_id (x := 𝓝 (0 : ℝ≥0∞)))
    exact ge_of_tendsto_of_frequently H <| (frequently_gt_nhds _).mono this
  /- Cover `s` by countably many closed balls such that
  `ν (s ∩ closedBall x (r x)) ≤ (C + ε) * μ (closedBall x (r x))` for each ball
  and `∑' x : t, μ (closedBall x (r x)) ≤ μ s + ε`. -/
  intro ε hε
  obtain ⟨t, r, htc, -, hνμ, hsr, hμ⟩ := exists_closedBall_covering_tsum_measure_le μ hε.ne'
    (fun x ↦ {r | ν (s ∩ closedBall x r) ≤ (C + ε) * μ (closedBall x r)}) s fun x hx δ hδ ↦ by
      rcases (nhdsGT_basis 0).frequently_iff.1 (h x hx _ (ENNReal.lt_add_right hC hε.ne')) δ hδ
        with ⟨r, hr, hle⟩
      exact ⟨r, hle, hr⟩
  have := htc.to_subtype
  calc
    ν s ≤ ν (⋃ x : t, s ∩ closedBall x (r x)) := by
      rw [← inter_iUnion]
      gcongr
      simpa
    _ ≤ ∑' x : t, ν (s ∩ closedBall x (r x)) := measure_iUnion_le _
    _ ≤ ∑' x : t, (C + ε) * μ (closedBall x (r x)) := by gcongr with i; exact hνμ i i.2
    _ ≤ (C + ε) * (μ s + ε) := by rw [ENNReal.tsum_mul_left]; gcongr

/-- Let `μ` be a σ-finite measure with the closed ball covering property,
let `ν` be an outer measure.
Let `s` be a set, let `C` be a constant such that `μ s ≠ 0 ∨ C ≠ ∞`.
Suppose that for each `x ∈ s` and each `C' > C`, the inequality
`ν (s ∩ closedBall x r) ≤ C' * μ (closedBall x r)` holds for arbitrarily small `r > 0`.
Then `ν s ≤ C * μ s`.

Note that we do not assume measurability of `s`. -/
theorem outerMeasure_le_mul [SigmaFinite μ] (hsC : μ s ≠ 0 ∨ C ≠ ∞)
    (h : ∀ x ∈ s, ∀ C' > C, ∃ᶠ r in 𝓝[>] 0, ν (s ∩ closedBall x r) ≤ C' * μ (closedBall x r)) :
    ν s ≤ C * μ s := by
  rcases eq_or_ne C 0 with rfl | hC
  · calc
      ν s = ν (⋃ n, s ∩ spanningSets μ n) := by simp [← inter_iUnion]
      _ ≤ ∑' n, ν (s ∩ spanningSets μ n) := measure_iUnion_le _
      _ ≤ ∑' n, 0 * μ (s ∩ spanningSets μ n) := by
        gcongr with n
        refine outerMeasure_le_mul' (by simp) (.inr ?_) fun x hx C' hC' ↦
          (h x hx.1 C' hC').mono fun r ↦ le_trans ?_
        · exact (measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top ..) |>.ne
        · gcongr
          apply inter_subset_left
      _ = 0 * μ s := by simp
  · exact outerMeasure_le_mul' hsC (.inl hC) h

/-- Let `μ` be a measure with the closed ball covering property, let `ν` be an outer measure.
Let `s` be a `μ`-null set.
Suppose that for each `x ∈ s` there exists a constant `C` such that the inequality
`ν (s ∩ closedBall x r) ≤ C * μ (closedBall x r)` holds for arbitrarily small `r > 0`.
Then `s` is a `ν`-null set. -/
theorem outerMeasure_null_of_null_of_forall_exists_le_mul (hs : μ s = 0)
    (h : ∀ x ∈ s, ∃ C : ℝ≥0, ∃ᶠ r in 𝓝[>] 0, ν (s ∩ closedBall x r) ≤ C * μ (closedBall x r)) :
    ν s = 0 := by
  set t : ℕ → Set α := fun n ↦
    {x ∈ s | ∃ᶠ r in 𝓝[>] 0, ν (s ∩ closedBall x r) ≤ n * μ (closedBall x r)}
  have hst : s ⊆ ⋃ n, t n := fun x hx ↦ by
    rcases h x hx with ⟨C, hC⟩
    rcases exists_nat_ge C with ⟨n, hn⟩
    refine mem_iUnion.2 ⟨n, hx, hC.mono fun r hr ↦ hr.trans ?_⟩
    gcongr
    exact_mod_cast hn
  refine measure_mono_null hst <| measure_iUnion_null fun n ↦ ?_
  have hμ : μ (t n) = 0 := measure_mono_null (sep_subset _ _) hs
  refine nonpos_iff_eq_zero.1 <| calc
    ν (t n) ≤ n * μ (t n) := by
      refine outerMeasure_le_mul' (.inr (ENNReal.natCast_ne_top n)) (.inr (by simp [hμ]))
        fun x hx C' hC' ↦ hx.2.mono fun r hr ↦ ?_
      grw [← hC'.le, ← hr]
      exact measure_mono (inter_subset_inter_left _ (sep_subset _ _))
    _ = 0 := by simp [hμ]

/-- Let `μ` be a σ-finite measure with the closed ball covering property,
let `ν` be an outer measure, let `s` be a set.
Suppose that for each `x ∈ s` there exists a constant `C` such that the inequality
`ν (s ∩ closedBall x r) ≤ C * μ (closedBall x r)` holds for arbitrarily small `r > 0`.
Suppose also that for `μ`-a.e. `x ∈ s` and each `ε > 0`, the inequality
`ν (s ∩ closedBall x r) ≤ ε * μ (closedBall x r)` holds for arbitrarily small `r > 0`.
Then `s` is a `ν`-null set.

Informally, if `ν (s ∩ closedBall x r) = O(μ (closedBall x r))` at all points of `s`
and `ν (s ∩ closedBall x r) = o(μ (closedBall x r))` at almost all points of `s`
(along some sequences of radii tending to zero), then `ν s = 0`.

Note that we do not assume measurability of `s`. -/
theorem outerMeasure_null_of_forall_le_mul_ae_null [SigmaFinite μ]
    (h : ∀ x ∈ s, ∃ C : ℝ≥0, ∃ᶠ r in 𝓝[>] 0, ν (s ∩ closedBall x r) ≤ C * μ (closedBall x r))
    (h₀ : ∀ᵐ x ∂μ, x ∈ s → ∀ ε > (0 : ℝ≥0∞),
      ∃ᶠ r in 𝓝[>] 0, ν (s ∩ closedBall x r) ≤ ε * μ (closedBall x r)) :
    ν s = 0 := by
  set s₀ := {x ∈ s | ∀ ε > (0 : ℝ≥0∞),
    ∃ᶠ r in 𝓝[>] 0, ν (s ∩ closedBall x r) ≤ ε * μ (closedBall x r)}
  have hs₀ : ν s₀ = 0 := by
    refine nonpos_iff_eq_zero.1 <| le_trans ?_ (zero_mul (μ s₀)).le
    refine outerMeasure_le_mul (.inr ENNReal.zero_ne_top) fun x hx ε hε ↦
      (hx.2 ε hε).mono fun r hr ↦ ?_
    exact (measure_mono (inter_subset_inter_left _ (sep_subset _ _))).trans hr
  have hs₁ : ν (s \ s₀) = 0 := by
    refine outerMeasure_null_of_null_of_forall_exists_le_mul (μ := μ) ?_ fun x hx ↦ ?_
    · refine measure_mono_null (fun x hx ↦ ?_) (ae_iff.1 h₀)
      exact fun hP ↦ hx.2 ⟨hx.1, hP hx.1⟩
    · obtain ⟨C, hC⟩ := h x hx.1
      exact ⟨C, hC.mono fun r hr ↦ by grw [sdiff_subset, hr]⟩
  exact measure_mono_null (fun x hx ↦ (em (x ∈ s₀)).imp id fun h ↦ ⟨hx, h⟩)
    (measure_union_null hs₀ hs₁)

/-- Let `μ` be a σ-finite measure with the closed ball covering property,
let `f : α → β` be a map, let `ν` be an outer measure on `β`.
Let `s` be a set, let `C` be a constant such that `μ s ≠ 0 ∨ C ≠ ∞`.
Suppose that for each `x ∈ s` and each `C' > C`, the inequality
`ν (f '' (s ∩ closedBall x r)) ≤ C' * μ (closedBall x r)` holds for arbitrarily small `r > 0`.
Then `ν (f '' s) ≤ C * μ s`. -/
theorem outerMeasure_image_le_mul [SigmaFinite μ] {f : α → β} {ν : OuterMeasure β}
    (hsC : μ s ≠ 0 ∨ C ≠ ∞)
    (h : ∀ x ∈ s, ∀ C' > C,
      ∃ᶠ r in 𝓝[>] 0, ν (f '' (s ∩ closedBall x r)) ≤ C' * μ (closedBall x r)) :
    ν (f '' s) ≤ C * μ s := by
  simp only [← OuterMeasure.comap_apply] at h ⊢
  exact outerMeasure_le_mul hsC h

/-- Let `μ` be a σ-finite measure with the closed ball covering property,
let `f : α → β` be a map, let `ν` be a measure on `β`.
Let `s` be a set, let `C` be a constant such that `μ s ≠ 0 ∨ C ≠ ∞`.
Suppose that for each `x ∈ s` and each `C' > C`, the inequality
`ν (f '' (s ∩ closedBall x r)) ≤ C' * μ (closedBall x r)` holds for arbitrarily small `r > 0`.
Then `ν (f '' s) ≤ C * μ s`. -/
theorem measure_image_le_mul [SigmaFinite μ] {_ : MeasurableSpace β} {f : α → β} {ν : Measure β}
    (hsC : μ s ≠ 0 ∨ C ≠ ∞)
    (h : ∀ x ∈ s, ∀ C' > C,
      ∃ᶠ r in 𝓝[>] 0, ν (f '' (s ∩ closedBall x r)) ≤ C' * μ (closedBall x r)) :
    ν (f '' s) ≤ C * μ s :=
  outerMeasure_image_le_mul (ν := ν.toOuterMeasure) hsC h

/-- Let `μ` be a measure with the closed ball covering property,
let `f : α → β` be a map, let `ν` be an outer measure on `β`. Let `s` be a `μ`-null set.
Suppose that for each `x ∈ s` there exists a constant `C` such that the inequality
`ν (f '' (s ∩ closedBall x r)) ≤ C * μ (closedBall x r)` holds for arbitrarily small `r > 0`.
Then `f '' s` is a `ν`-null set. -/
theorem outerMeasure_image_null_of_null_of_forall_exists_le_mul {f : α → β}
    {ν : OuterMeasure β} (hs : μ s = 0)
    (h : ∀ x ∈ s, ∃ C : ℝ≥0,
      ∃ᶠ r in 𝓝[>] 0, ν (f '' (s ∩ closedBall x r)) ≤ C * μ (closedBall x r)) :
    ν (f '' s) = 0 := by
  simp only [← OuterMeasure.comap_apply] at h ⊢
  exact outerMeasure_null_of_null_of_forall_exists_le_mul hs h

/-- Let `μ` be a measure with the closed ball covering property,
let `f : α → β` be a map, let `ν` be a measure on `β`. Let `s` be a `μ`-null set.
Suppose that for each `x ∈ s` there exists a constant `C` such that the inequality
`ν (f '' (s ∩ closedBall x r)) ≤ C * μ (closedBall x r)` holds for arbitrarily small `r > 0`.
Then `f '' s` is a `ν`-null set.

This is useful to prove the Lusin N-property of a map `f`. -/
theorem measure_image_null_of_null_of_forall_exists_le_mul {_ : MeasurableSpace β} {f : α → β}
    {ν : Measure β} (hs : μ s = 0)
    (h : ∀ x ∈ s, ∃ C : ℝ≥0,
      ∃ᶠ r in 𝓝[>] 0, ν (f '' (s ∩ closedBall x r)) ≤ C * μ (closedBall x r)) :
    ν (f '' s) = 0 :=
  outerMeasure_image_null_of_null_of_forall_exists_le_mul (ν := ν.toOuterMeasure) hs h

end MeasureTheory.Measure
