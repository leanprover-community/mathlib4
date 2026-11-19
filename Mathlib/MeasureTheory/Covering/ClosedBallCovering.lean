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
  such that closed balls centered at `x` converge to `x` along `v`.

The instances are proved in other files:
* for a measure in a space with the Besicovitch covering property,
  see `Mathlib/MeasureTheory/Covering/Besicovitch.lean`;
* for a uniformly locally doubling measure,
  see `Mathlib/MeasureTheory/Covering/DensityTheorem.lean`.
-/

public section

open Set Filter Metric
open scoped ENNReal Topology

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
