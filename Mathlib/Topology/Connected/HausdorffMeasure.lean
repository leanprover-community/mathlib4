/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Connected sets and Hausdorff measure

In this file we relate connectedness of a subset `s` of an extended metric space to its Hausdorff
measure.

The key geometric idea is that the distance from a fixed base point is Lipschitz, so it does not
increase Hausdorff measures, and the image of a preconnected set under this map is an interval whose
one-dimensional Hausdorff measure equals its length. Comparing the two turns distances inside `s`
into lower bounds for `μH[1] s`.

## Main results

* `IsPreconnected.ediam_le_hausdorffMeasure`: the diameter of a preconnected set is at most its
  one-dimensional Hausdorff measure.
* `IsPreconnected.subsingleton_of_hausdorffMeasure_lt_top`: a preconnected set with finite
  `d`-dimensional Hausdorff measure for some `d < 1` is a subsingleton.
* `isTotallyDisconnected_of_hausdorffMeasure_lt_top`: a set with finite `d`-dimensional Hausdorff
  measure for some `d < 1` is totally disconnected.
* `IsPreconnected.totallyBounded_of_hausdorffMeasure_lt_top`: a preconnected set with finite
  one-dimensional Hausdorff measure is totally bounded.

## TODO

Prove that a preconnected and complete subset with finite one-dimensional Hausdorff measure is path
connected and locally path connected. In fact, any two points in such a set can be connected by an
injective geodesic with constant speed whose length is bounded above by the one-dimensional
Hausdorff measure of this set.

-/

open MeasureTheory Metric Set
open scoped ENNReal

@[expose] public section

variable {X : Type*} [EMetricSpace X] {s : Set X} {a b : X}

/-- The set of points at finite distance from `a` is clopen. -/
theorem isClopen_setOf_edist_ne_top : IsClopen {x | edist a x ≠ ∞} := by
  constructor
  · rw [← isOpen_compl_iff, EMetric.isOpen_iff]
    refine fun x hx => ⟨1, one_pos, fun y hy => ?_⟩
    simp only [mem_compl_iff, mem_setOf_eq, not_not] at hx ⊢
    rw [mem_eball] at hy
    refine (ENNReal.add_eq_top.1 (top_le_iff.1 (hx ▸ edist_triangle a y x))).resolve_right ?_
    exact (hy.trans_le le_top).ne
  · rw [EMetric.isOpen_iff]
    refine fun x hx => ⟨1, one_pos, fun z hz => ?_⟩
    refine ((edist_triangle a x z).trans_lt (ENNReal.add_lt_top.2 ⟨hx.lt_top, ?_⟩)).ne
    rw [edist_comm]
    exact hz.trans_le le_top

/-- In a preconnected subset of an extended metric space, any two points are at finite distance. -/
theorem IsPreconnected.edist_ne_top (hs : IsPreconnected s) (ha : a ∈ s) (hb : b ∈ s) :
    edist a b ≠ ∞ :=
  hs.subset_isClopen isClopen_setOf_edist_ne_top ⟨a, ha, by simp⟩ hb

/-- The points at finite distance from `a` form a pseudometric space, with distance given by the
real part of the extended distance. -/
@[reducible] def pseudoMetricSpaceSetOfEdistNeTop (a : X) :
    PseudoMetricSpace {x : X | edist a x ≠ ∞} :=
  PseudoEMetricSpace.toPseudoMetricSpace fun p q => by
    refine ((edist_triangle p.1 a q.1).trans_lt (ENNReal.add_lt_top.2 ⟨?_, q.2.lt_top⟩)).ne
    rw [edist_comm]
    exact p.2.lt_top

/-- The distance function `x ↦ (edist a x).toReal` is Lipschitz on any preconnected set `s` that
contains `a`. -/
theorem lipschitzOnWith_toReal_edist (hs : IsPreconnected s) (ha : a ∈ s) :
    LipschitzOnWith 1 (fun x => (edist a x).toReal) s := by
  let := pseudoMetricSpaceSetOfEdistNeTop a
  intro x hx y hy
  exact LipschitzWith.dist_right (⟨a, by simp⟩ : {x | edist a x ≠ ∞})
    ⟨x, hs.edist_ne_top ha hx⟩ ⟨y, hs.edist_ne_top ha hy⟩

variable [MeasurableSpace X] [BorelSpace X]

/-- For any `a`, `b` in a preconnected set `s` and any `r ≤ edist a b`, the radius `r` is at most
the one-dimensional Hausdorff measure of the part of `s` lying in the open ball of radius `r` around
`a`. This lemma is needed in the proof of
`IsPreconnected.totallyBounded_of_hausdorffMeasure_lt_top`. -/
theorem IsPreconnected.le_hausdorffMeasure_of_le_edist (hs : IsPreconnected s) (ha : a ∈ s)
    (hb : b ∈ s) {r : ℝ≥0∞} (hr : r ≤ edist a b) :
    r ≤ μH[1] (s ∩ eball a r) :=
  have hrne : r ≠ ∞ := ne_top_of_le_ne_top (hs.edist_ne_top ha hb) hr
  calc
    r = ENNReal.ofReal r.toReal := (ENNReal.ofReal_toReal hrne).symm
    _ = μH[1] (Ico 0 r.toReal) := by rw [hausdorffMeasure_real, Real.volume_Ico, sub_zero]
    _ ≤ μH[1] ((fun x => (edist a x).toReal) '' (s ∩ eball a r)) := by
        refine measure_mono fun c hc => ?_
        have : Ico 0 r.toReal ⊆ (fun x => (edist a x).toReal) '' s := calc
          _ ⊆ Icc 0 (edist a b).toReal := by grind [ENNReal.toReal_mono (hs.edist_ne_top ha hb) hr]
          _ ⊆ _ := (hs.image _ (lipschitzOnWith_toReal_edist hs ha).continuousOn).Icc_subset
            ⟨a, ha, by simp⟩ ⟨b, hb, rfl⟩
        obtain ⟨z, hz, hgz⟩ : c ∈ (fun x => (edist a x).toReal) '' s := this hc
        refine ⟨z, ⟨hz, ?_⟩, hgz⟩
        rw [mem_eball', ← ENNReal.toReal_lt_toReal (hs.edist_ne_top ha hz) hrne]
        exact hgz.le.trans_lt hc.2
    _ ≤ _ := by
        simpa using ((lipschitzOnWith_toReal_edist hs ha).mono
          inter_subset_left).hausdorffMeasure_image_le zero_le_one

/-- The distance between two points of a preconnected set `s` is at most the one-dimensional
Hausdorff measure of `s`. -/
theorem IsPreconnected.edist_le_hausdorffMeasure (hs : IsPreconnected s) (ha : a ∈ s) (hb : b ∈ s) :
    edist a b ≤ μH[1] s := by
  grw [hs.le_hausdorffMeasure_of_le_edist ha hb le_rfl, measure_mono inter_subset_left]

/-- The extended diameter of a preconnected set is at most its one-dimensional Hausdorff measure. -/
theorem IsPreconnected.ediam_le_hausdorffMeasure (hs : IsPreconnected s) :
    ediam s ≤ μH[1] s :=
  ediam_le fun _ ha _ hb => hs.edist_le_hausdorffMeasure ha hb

/-- A preconnected set with finite `d`-dimensional Hausdorff measure for some `d < 1` is a
subsingleton. -/
theorem IsPreconnected.subsingleton_of_hausdorffMeasure_lt_top (hs : IsPreconnected s) {d : ℝ}
    (hd : d < 1) (hle : μH[d] s < ∞) : s.Subsingleton := by
  grw [← ediam_eq_zero_iff, ← le_zero_iff, hs.ediam_le_hausdorffMeasure, le_zero_iff]
  grind [Measure.hausdorffMeasure_zero_or_top hd s]

/-- A set with finite `d`-dimensional Hausdorff measure for some `d < 1` is totally disconnected. -/
theorem isTotallyDisconnected_of_hausdorffMeasure_lt_top {d : ℝ} (hd : d < 1)
    (hle : μH[d] s < ∞) : IsTotallyDisconnected s :=
  fun _ hts ht => ht.subsingleton_of_hausdorffMeasure_lt_top hd ((measure_mono hts).trans_lt hle)

/-- A preconnected set with finite one-dimensional Hausdorff measure is totally bounded. -/
theorem IsPreconnected.totallyBounded_of_hausdorffMeasure_lt_top (hs : IsPreconnected s)
    (hle : μH[1] s < ∞) : TotallyBounded s := by
  by_cases! hse : s = ∅
  · simp_all
  refine EMetric.totallyBounded_iff.2 fun ε hε => ?_
  by_contra! hcov
  have hgreedy (t : Finset X) : ∃ y, y ∈ s ∧ ∀ x ∈ t, ε ≤ edist x y := by
    obtain ⟨z, hz, hznotin⟩ := not_subset.1 (hcov t t.finite_toSet)
    refine ⟨z, hz, fun x hx => ?_⟩
    simpa [mem_eball, not_lt, edist_comm] using fun hmem => hznotin (mem_biUnion hx hmem)
  -- A greedy choice of an `ε`-separated sequence inside `s`.
  obtain ⟨f, hf1, hf2⟩ :=
    exists_seq_of_forall_finset_exists (· ∈ s) (fun x y => ε ≤ edist x y) (fun t _ => hgreedy t)
  -- Adding up the disjoint contributions gives `N * (ε / 2) ≤ μH[1] s` for every `N`.
  have hbound (N : ℕ) : N * (ε / 2) ≤ μH[1] s := by
    calc
      N * (ε / 2) = ∑ _n ∈ Finset.range N, (ε / 2) := by simp [Finset.sum_const, Finset.card_range]
      _ ≤ ∑ n ∈ Finset.range N, μH[1] (s ∩ eball (f n) (ε / 2)) := by
          refine Finset.sum_le_sum fun n _ => ?_
          apply hs.le_hausdorffMeasure_of_le_edist (hf1 n) (hf1 (n + 1))
          grw [ENNReal.half_le_self, hf2 n (n + 1) n.lt_add_one]
      _ ≤ ∑ n ∈ Finset.range N, μH[1] ((toMeasurable μH[1] s) ∩ eball (f n) (ε / 2)) := by
          refine Finset.sum_le_sum fun n _ => measure_mono ?_
          grw [subset_toMeasurable _ s]
      _ = μH[1] (⋃ n ∈ Finset.range N, (toMeasurable μH[1] s) ∩ eball (f n) (ε / 2)) := by
          refine (measure_biUnion_finset (fun i hi j hj hij => ?_) fun i _ => ?_).symm
          · simp only [Function.onFun]
            suffices h : Disjoint (eball (f i) (ε / 2)) (eball (f j) (ε / 2)) from
              h.mono inter_subset_right inter_subset_right
            wlog hijlt : i < j generalizing i j
            · exact (this j hj i hi hij.symm (by grind)).symm
            · apply disjoint_left.2 fun z hzm hzn => ?_
              rw [mem_eball] at hzm hzn
              refine (not_le.2 ?_) (hf2 i j hijlt)
              calc
                edist (f i) (f j) ≤ edist (f i) z + edist z (f j) := edist_triangle _ _ _
                _ < ε / 2 + ε / 2 := by rw [edist_comm (f i) z]; gcongr
                _ = ε := by simp
          · measurability
      _ ≤ μH[1] (toMeasurable μH[1] s) := measure_mono (iUnion₂_subset fun i _ => inter_subset_left)
      _ = μH[1] s := by simp
  have : ε / 2 ≠ 0 := by simp [hε.ne.symm]
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt (ENNReal.div_ne_top hle.ne this)
  refine (not_le.2 ((ENNReal.div_lt_iff (Or.inl this) (Or.inl ?_)).mp hN)) (hbound N)
  refine ENNReal.div_ne_top (fun heq => ?_) two_ne_zero
  obtain ⟨a, ha⟩ := hse
  refine hcov {a} (finite_singleton a) fun b hb => ?_
  simpa [heq] using (hs.edist_ne_top hb ha).lt_top

end
