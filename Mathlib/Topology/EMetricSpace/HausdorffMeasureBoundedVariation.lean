/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Topology.Connected.HausdorffMeasure
public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Variation and one-dimensional Hausdorff measure

This file relates the variation `eVariationOn f s` of a map `f : α → E` on a set `s` to the
one-dimensional Hausdorff measure of the image `f '' s`.

## Main results

* `MeasureTheory.Measure.hausdorffMeasure_le_eVariationOn`: for any map `f` and any set `s`,
  `μH[1] (f '' s)` is at most the variation of `f` on `s`.
* `MeasureTheory.Measure.hausdorffMeasure_eq_eVariationOn`: if `f` is continuous and injective on an
  interval `s`, then `μH[1] (f '' s)` equals the variation of `f` on `s`.
-/

open ENNReal Set Filter Topology Metric

public section

namespace MeasureTheory.Measure
variable {α E : Type*} [LinearOrder α] [EMetricSpace E] (f : α → E) (s : Set α) {ε : ℝ}

private lemma toReal_eVariationOn_Iic_mono (htop : eVariationOn f s ≠ ∞) {x y : α} (hxy : x ≤ y) :
    (eVariationOn f (s ∩ Iic x)).toReal ≤ (eVariationOn f (s ∩ Iic y)).toReal :=
  ENNReal.toReal_mono (ne_top_of_le_ne_top htop (eVariationOn.mono f inter_subset_left))
    (eVariationOn.mono f (inter_subset_inter_right _ (Iic_subset_Iic.mpr hxy)))

private lemma eVariationOn_inter_Icc_eq (htop : eVariationOn f s ≠ ∞) {x y : α} (hx : x ∈ s)
    (hxy : x ≤ y) :
    eVariationOn f (s ∩ Icc x y) = ENNReal.ofReal
      ((eVariationOn f (s ∩ Iic y)).toReal - (eVariationOn f (s ∩ Iic x)).toReal) := by
  have h {t : Set α} (ht : t ⊆ s) : eVariationOn f t ≠ ∞ :=
    ne_top_of_le_ne_top htop (eVariationOn.mono f ht)
  rw [← eVariationOn.Iic_add_Icc f hxy hx, ENNReal.toReal_add (h inter_subset_left)
    (h inter_subset_left), add_sub_cancel_left, ENNReal.ofReal_toReal (h inter_subset_left)]

/-- The set of elements `x` where `eVariationOn f (s ∩ Iic x)` sits between `[k * ε, (k + 1) * ε)`.
This provides coverings of `s` where each piece has variation at most `ε`. -/
private def slice (ε : ℝ) (k : ℕ) : Set α :=
  {x ∈ s | k * ε ≤ (eVariationOn f (s ∩ Iic x)).toReal ∧
    (eVariationOn f (s ∩ Iic x)).toReal < (k + 1) * ε}

private lemma subset_iUnion_slice (hε : 0 < ε) : s ⊆ ⋃ k, slice f s ε k := by
  intro x hx
  have h0 : 0 ≤ (eVariationOn f (s ∩ Iic x)).toReal / ε := by positivity
  refine mem_iUnion.mpr ⟨⌊(eVariationOn f (s ∩ Iic x)).toReal / ε⌋₊, hx, ?_, ?_⟩
  · exact (le_div_iff₀ hε).mp (Nat.floor_le h0)
  · exact (div_lt_iff₀ hε).mp (Nat.lt_floor_add_one _)

private lemma ediam_image_slice_le (htop : eVariationOn f s ≠ ∞) (k : ℕ) :
    ediam (f '' slice f s ε k) ≤ ENNReal.ofReal ε := by
  refine ediam_image_le_iff.mpr fun x hx y hy ↦ ?_
  wlog! hxy : x ≤ y
  · exact edist_comm (f x) (f y) ▸ this f s htop k y hy x hx hxy.le
  apply (eVariationOn.edist_le f (s := s ∩ Icc x y) ⟨hx.1, le_rfl, hxy⟩ ⟨hy.1, hxy, le_rfl⟩).trans
  rw [eVariationOn_inter_Icc_eq f s htop hx.1 hxy]
  exact ENNReal.ofReal_le_ofReal (by linarith [hx.2.1, hy.2.2])

private lemma sum_eVariationOn_slice_le (htop : eVariationOn f s ≠ ∞) (hε : 0 ≤ ε) (m : ℕ) :
    ∑ k ∈ Finset.range m, eVariationOn f (slice f s ε k) ≤ eVariationOn f s := by
  suffices ∑ k ∈ Finset.range m, eVariationOn f (slice f s ε k) ≤
      eVariationOn f {x ∈ s | (eVariationOn f (s ∩ Iic x)).toReal < m * ε} from
    this.trans (eVariationOn.mono f fun x hx ↦ hx.1)
  induction m with
  | zero => simp
  | succ m ih =>
    grw [Finset.sum_range_succ, ih]
    refine (eVariationOn.add_le_union f fun x hx y hy ↦ ?_).trans (eVariationOn.mono f ?_)
    · by_contra! h
      linarith [hx.2, hy.2.1, toReal_eVariationOn_Iic_mono f s htop h.le]
    · exact Set.union_subset (fun x hx ↦ ⟨hx.1, by grind⟩) (fun x hx ↦ ⟨hx.1, mod_cast hx.2.2⟩)

variable [MeasurableSpace E] [BorelSpace E]

theorem hausdorffMeasure_le_eVariationOn : μH[1] (f '' s) ≤ eVariationOn f s := by
  by_cases htop : eVariationOn f s = ∞
  · simp [htop]
  set ε : ℕ → ℝ := fun n ↦ 1 / (n + 1)
  have hε (n : ℕ) : 0 < ε n := by positivity
  have hr : Tendsto (fun n ↦ ENNReal.ofReal (ε n)) atTop (𝓝 0) := by
    simpa [ε] using ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine hausdorffMeasure_le_liminf_tsum _ _ _ hr (fun n k ↦ f '' slice f s (ε n) k)
    (.of_forall fun n k ↦ ediam_image_slice_le f s htop k)
    (.of_forall fun n ↦ (image_mono (subset_iUnion_slice f s (hε n))).trans image_iUnion.le)
    |>.trans <| liminf_le_of_frequently_le' (.of_forall fun n ↦ ?_)
  refine ENNReal.tsum_le_of_sum_range_le fun m ↦ ?_
  calc ∑ k ∈ Finset.range m, ediam (f '' slice f s (ε n) k) ^ (1 : ℝ)
    _ ≤ ∑ k ∈ Finset.range m, eVariationOn f (slice f s (ε n) k) := by
      gcongr with k
      rw [ENNReal.rpow_one]
      exact ediam_image_le_iff.mpr fun x hx y hy ↦ eVariationOn.edist_le f hx hy
    _ ≤ eVariationOn f s := sum_eVariationOn_slice_le f s htop (hε n).le m

theorem hausdorffMeasure_eq_eVariationOn {α : Type*} [ConditionallyCompleteLinearOrder α]
    [DenselyOrdered α] [TopologicalSpace α] [OrderTopology α] {f : α → E} {s : Set α}
    (hs : s.OrdConnected) (hinj : InjOn f s) (hcont : ContinuousOn f s) :
    μH[1] (f '' s) = eVariationOn f s := by
  refine le_antisymm (hausdorffMeasure_le_eVariationOn f s) <| iSup_le fun ⟨n, u, hu, us⟩ ↦ ?_
  have hIcc (i : ℕ) : Icc (u i) (u (i + 1)) ⊆ s := hs.out (us i) (us (i + 1))
  calc ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))
    _ ≤ ∑ i ∈ Finset.range n, μH[1] (f '' Icc (u i) (u (i + 1))) := by
      gcongr with i
      exact (isPreconnected_Icc.image _ (hcont.mono (hIcc i))).edist_le_hausdorffMeasure
        (mem_image_of_mem f (right_mem_Icc.mpr (hu i.le_succ)))
        (mem_image_of_mem f (left_mem_Icc.mpr (hu i.le_succ)))
    _ = μH[1] (⋃ i ∈ Finset.range n, f '' Icc (u i) (u (i + 1))) := by
      have := nullSingletonClass_hausdorff E one_pos
      refine (measure_biUnion_finset₀ (fun i hi j hj hij ↦ ?_) fun i _ ↦ ?_).symm
      · wlog h : i < j generalizing i j
        · exact (this j hj i hi hij.symm (hij.lt_or_gt.resolve_left h)).symm
        rw [Function.onFun, AEDisjoint, ← hinj.image_inter (hIcc i) (hIcc j)]
        refine (Subsingleton.image (fun p hp q hq ↦ ?_) f).measure_zero _
        rw [le_antisymm (hp.1.2.trans (hu h)) hp.2.1, le_antisymm (hq.1.2.trans (hu h)) hq.2.1]
      · exact (isCompact_Icc.image_of_continuousOn (hcont.mono (hIcc i)))
          |>.isClosed.measurableSet.nullMeasurableSet
    _ ≤ μH[1] (f '' s) := measure_mono (iUnion₂_subset fun i _ ↦ image_mono (hIcc i))

end MeasureTheory.Measure
