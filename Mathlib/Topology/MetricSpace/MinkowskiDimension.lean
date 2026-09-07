/-
Copyright (c) 2026 Francesco Nishanil Chotuck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francesco Nishanil Chotuck
-/
module

public import Mathlib.Topology.MetricSpace.CoveringNumbers
public import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Minkowski (box-counting) dimension

We define the lower and upper Minkowski dimensions of a set in a pseudo-emetric space, which
measure the growth rate of the covering number `externalCoveringNumber ε s` as `ε → 0⁺`, and we
compare them with the Hausdorff dimension.

Classically, these dimensions are the `liminf` (resp. `limsup`) of
`log (externalCoveringNumber ε s) / log (1 / ε)` as `ε → 0⁺`. To avoid logarithms and division
in `ℝ≥0∞`, we define them instead as the infimum of all `d : ℝ≥0` such that
`externalCoveringNumber ε s ≤ ε ^ (-d : ℝ)` frequently (resp. eventually) as `ε → 0⁺`.
A set with no finite `ε`-covers for small `ε` has both Minkowski dimensions equal to `⊤`.

## Main definitions

* `lowerMinkowskiDim`: the lower Minkowski dimension of a set, as an element of `ℝ≥0∞`.
* `upperMinkowskiDim`: the upper Minkowski dimension of a set, as an element of `ℝ≥0∞`.

## Main statements

* `lowerMinkowskiDim_le_upperMinkowskiDim`: the lower dimension is at most the upper dimension.
* `Set.Finite.upperMinkowskiDim_eq_zero`: finite sets have Minkowski dimension zero.
* `lowerMinkowskiDim_closure`, `upperMinkowskiDim_closure`: the Minkowski dimensions are
  unchanged by taking the closure.
* `upperMinkowskiDim_union`: the upper Minkowski dimension of `s ∪ t` is the maximum of the
  upper Minkowski dimensions.
* `dimH_le_lowerMinkowskiDim`: the Hausdorff dimension is at most the lower Minkowski dimension.

## References

* [K. Falconer, *Fractal geometry: Mathematical foundations and applications*][falconer1990]
-/

@[expose] public section

open EMetric Filter Metric MeasureTheory Set
open scoped ENNReal NNReal Topology

variable {X : Type*} [PseudoEMetricSpace X] {s t : Set X} {d : ℝ≥0}

/-- The lower Minkowski dimension (or lower box-counting dimension) of a set `s` in a
pseudo-emetric space: the infimum of all `d : ℝ≥0` such that, frequently as `ε → 0⁺`, the set
`s` can be covered by at most `ε ^ (-d : ℝ)` closed balls of radius `ε`.

A set with no finite `ε`-covers for small `ε` has lower Minkowski dimension `⊤`. -/
noncomputable def lowerMinkowskiDim (s : Set X) : ℝ≥0∞ :=
  ⨅ (d : ℝ≥0) (_ : ∃ᶠ ε : ℝ≥0 in 𝓝[>] 0,
    (externalCoveringNumber ε s : ℝ≥0∞) ≤ (ε : ℝ≥0∞) ^ (-(d : ℝ))), (d : ℝ≥0∞)

/-- The upper Minkowski dimension (or upper box-counting dimension) of a set `s` in a
pseudo-emetric space: the infimum of all `d : ℝ≥0` such that, eventually as `ε → 0⁺`, the set
`s` can be covered by at most `ε ^ (-d : ℝ)` closed balls of radius `ε`.

A set with no finite `ε`-covers for small `ε` has upper Minkowski dimension `⊤`. -/
noncomputable def upperMinkowskiDim (s : Set X) : ℝ≥0∞ :=
  ⨅ (d : ℝ≥0) (_ : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
    (externalCoveringNumber ε s : ℝ≥0∞) ≤ (ε : ℝ≥0∞) ^ (-(d : ℝ))), (d : ℝ≥0∞)

/-- If frequently as `ε → 0⁺` the set `s` can be covered by at most `ε ^ (-d : ℝ)` closed balls
of radius `ε`, then `lowerMinkowskiDim s ≤ d`. -/
lemma lowerMinkowskiDim_le_of_frequently_le
    (h : ∃ᶠ ε : ℝ≥0 in 𝓝[>] 0, (externalCoveringNumber ε s : ℝ≥0∞) ≤ (ε : ℝ≥0∞) ^ (-(d : ℝ))) :
    lowerMinkowskiDim s ≤ d := iInf₂_le d h

/-- If eventually as `ε → 0⁺` the set `s` can be covered by at most `ε ^ (-d : ℝ)` closed balls
of radius `ε`, then `upperMinkowskiDim s ≤ d`. -/
lemma upperMinkowskiDim_le_of_eventually_le
    (h : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, (externalCoveringNumber ε s : ℝ≥0∞) ≤ (ε : ℝ≥0∞) ^ (-(d : ℝ))) :
    upperMinkowskiDim s ≤ d := iInf₂_le d h

/-- To bound the lower Minkowski dimension from below, it suffices to bound from below every
exponent `d` satisfying the defining covering condition. -/
lemma le_lowerMinkowskiDim {a : ℝ≥0∞}
    (h : ∀ d : ℝ≥0, (∃ᶠ ε : ℝ≥0 in 𝓝[>] 0,
      (externalCoveringNumber ε s : ℝ≥0∞) ≤ (ε : ℝ≥0∞) ^ (-(d : ℝ))) → a ≤ d) :
    a ≤ lowerMinkowskiDim s := le_iInf₂ h

/-- To bound the upper Minkowski dimension from below, it suffices to bound from below every
exponent `d` satisfying the defining covering condition. -/
lemma le_upperMinkowskiDim {a : ℝ≥0∞}
    (h : ∀ d : ℝ≥0, (∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
      (externalCoveringNumber ε s : ℝ≥0∞) ≤ (ε : ℝ≥0∞) ^ (-(d : ℝ))) → a ≤ d) :
    a ≤ upperMinkowskiDim s := le_iInf₂ h

/-- If `lowerMinkowskiDim s < a`, then some exponent `d < a` satisfies the defining covering
condition frequently as `ε → 0⁺`. -/
lemma exists_frequently_of_lowerMinkowskiDim_lt {a : ℝ≥0∞} (h : lowerMinkowskiDim s < a) :
    ∃ d : ℝ≥0, (d : ℝ≥0∞) < a ∧ ∃ᶠ ε : ℝ≥0 in 𝓝[>] 0,
      (externalCoveringNumber ε s : ℝ≥0∞) ≤ (ε : ℝ≥0∞) ^ (-(d : ℝ)) := by
  simp only [lowerMinkowskiDim, iInf_lt_iff] at h
  obtain ⟨d, hd, hda⟩ := h
  exact ⟨d, hda, hd⟩

/-- If `upperMinkowskiDim s < a`, then some exponent `d < a` satisfies the defining covering
condition eventually as `ε → 0⁺`. -/
lemma exists_eventually_of_upperMinkowskiDim_lt {a : ℝ≥0∞} (h : upperMinkowskiDim s < a) :
    ∃ d : ℝ≥0, (d : ℝ≥0∞) < a ∧ ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
      (externalCoveringNumber ε s : ℝ≥0∞) ≤ (ε : ℝ≥0∞) ^ (-(d : ℝ)) := by
  simp only [upperMinkowskiDim, iInf_lt_iff] at h
  obtain ⟨d, hd, hda⟩ := h
  exact ⟨d, hda, hd⟩

/-- The lower Minkowski dimension is at most the upper Minkowski dimension. -/
lemma lowerMinkowskiDim_le_upperMinkowskiDim (s : Set X) :
    lowerMinkowskiDim s ≤ upperMinkowskiDim s :=
  iInf_mono fun _ ↦ iInf_const_mono Eventually.frequently

@[gcongr]
lemma lowerMinkowskiDim_mono (h : s ⊆ t) : lowerMinkowskiDim s ≤ lowerMinkowskiDim t := by
  refine iInf_mono fun d ↦ iInf_const_mono fun hfreq ↦ hfreq.mono fun ε hε ↦ le_trans ?_ hε
  exact_mod_cast externalCoveringNumber_mono_set h

@[gcongr]
lemma upperMinkowskiDim_mono (h : s ⊆ t) : upperMinkowskiDim s ≤ upperMinkowskiDim t := by
  refine iInf_mono fun d ↦ iInf_const_mono fun hev ↦ hev.mono fun ε hε ↦ le_trans ?_ hε
  exact_mod_cast externalCoveringNumber_mono_set h

private lemma eventually_rpow_neg_le_rpow_neg {d₁ d₂ : ℝ≥0} (h : d₁ ≤ d₂) :
    ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, (ε : ℝ≥0∞) ^ (-(d₁ : ℝ)) ≤ (ε : ℝ≥0∞) ^ (-(d₂ : ℝ)) := by
  filter_upwards [(eventually_le_nhds one_pos).filter_mono nhdsWithin_le_nhds] with ε hε
  exact ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hε)
    (neg_le_neg (by exact_mod_cast h))

private lemma eventually_const_le_rpow_neg {C : ℝ≥0∞} (hC : C ≠ ∞) (hd : 0 < d) :
    ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, C ≤ (ε : ℝ≥0∞) ^ (-(d : ℝ)) := by
  have h_coe : Tendsto (fun ε : ℝ≥0 ↦ (ε : ℝ≥0∞)) (𝓝[>] (0 : ℝ≥0)) (𝓝 (0 : ℝ≥0∞)) := by
    rw [← ENNReal.coe_zero]
    exact (ENNReal.tendsto_coe.2 tendsto_id).mono_left nhdsWithin_le_nhds
  have h_lim := h_coe.ennrpow_const (-(d : ℝ))
  rw [ENNReal.zero_rpow_of_neg (by simpa using hd)] at h_lim
  exact (h_lim.eventually (lt_mem_nhds hC.lt_top)).mono fun ε hε ↦ hε.le

private lemma le_rpow_neg_add {x C : ℝ≥0∞} {ε δ : ℝ≥0}
    (hx : x ≤ C * (ε : ℝ≥0∞) ^ (-(d : ℝ))) (hC : C ≤ (ε : ℝ≥0∞) ^ (-(δ : ℝ))) (hε : 0 < ε) :
    x ≤ (ε : ℝ≥0∞) ^ (-((d + δ : ℝ≥0) : ℝ)) :=
  calc x ≤ C * (ε : ℝ≥0∞) ^ (-(d : ℝ)) := hx
    _ ≤ (ε : ℝ≥0∞) ^ (-(δ : ℝ)) * (ε : ℝ≥0∞) ^ (-(d : ℝ)) := by gcongr
    _ = (ε : ℝ≥0∞) ^ (-((d + δ : ℝ≥0) : ℝ)) := by
        rw [← ENNReal.rpow_add _ _ (by exact_mod_cast hε.ne') ENNReal.coe_ne_top]
        congr 1
        push_cast
        ring

lemma upperMinkowskiDim_le_of_eventually_le_mul {C : ℝ≥0∞} (hC : C ≠ ∞)
    (h : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, (externalCoveringNumber ε s : ℝ≥0∞) ≤ C * (ε : ℝ≥0∞) ^ (-(d : ℝ))) :
    upperMinkowskiDim s ≤ d := by
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ ↦ ?_
  refine le_trans (upperMinkowskiDim_le_of_eventually_le (d := d + δ) ?_) (by push_cast; rfl)
  filter_upwards [h, eventually_const_le_rpow_neg hC hδ, eventually_mem_nhdsWithin]
    with ε hN hCle (hε : (0 : ℝ≥0) < ε)
  exact le_rpow_neg_add hN hCle hε

lemma lowerMinkowskiDim_le_of_frequently_le_mul {C : ℝ≥0∞} (hC : C ≠ ∞)
    (h : ∃ᶠ ε : ℝ≥0 in 𝓝[>] 0, (externalCoveringNumber ε s : ℝ≥0∞) ≤ C * (ε : ℝ≥0∞) ^ (-(d : ℝ))) :
    lowerMinkowskiDim s ≤ d := by
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ ↦ ?_
  refine le_trans (lowerMinkowskiDim_le_of_frequently_le (d := d + δ) ?_) (by push_cast; rfl)
  refine ((h.and_eventually ((eventually_const_le_rpow_neg hC hδ).and
    eventually_mem_nhdsWithin)).mono ?_)
  rintro ε ⟨hN, hCle, (hε : (0 : ℝ≥0) < ε)⟩
  exact le_rpow_neg_add hN hCle hε

protected lemma Set.Finite.upperMinkowskiDim_eq_zero (hs : s.Finite) :
    upperMinkowskiDim s = 0 := by
  refine le_antisymm ?_ zero_le
  refine upperMinkowskiDim_le_of_eventually_le_mul (C := (s.encard : ℝ≥0∞))
    (by exact_mod_cast hs.encard_lt_top.ne) (Eventually.of_forall fun ε ↦ ?_)
  simp only [NNReal.coe_zero, neg_zero, ENNReal.rpow_zero, mul_one]
  exact_mod_cast externalCoveringNumber_le_encard_self s

protected lemma Set.Finite.lowerMinkowskiDim_eq_zero (hs : s.Finite) :
    lowerMinkowskiDim s = 0 :=
  le_antisymm ((lowerMinkowskiDim_le_upperMinkowskiDim s).trans_eq
    hs.upperMinkowskiDim_eq_zero) zero_le

protected lemma Set.Subsingleton.upperMinkowskiDim_eq_zero (hs : s.Subsingleton) :
    upperMinkowskiDim s = 0 := hs.finite.upperMinkowskiDim_eq_zero

protected lemma Set.Subsingleton.lowerMinkowskiDim_eq_zero (hs : s.Subsingleton) :
    lowerMinkowskiDim s = 0 := hs.finite.lowerMinkowskiDim_eq_zero

@[simp]
lemma upperMinkowskiDim_empty : upperMinkowskiDim (∅ : Set X) = 0 :=
  subsingleton_empty.upperMinkowskiDim_eq_zero

@[simp]
lemma lowerMinkowskiDim_empty : lowerMinkowskiDim (∅ : Set X) = 0 :=
  subsingleton_empty.lowerMinkowskiDim_eq_zero

@[simp]
lemma upperMinkowskiDim_singleton (x : X) : upperMinkowskiDim ({x} : Set X) = 0 :=
  subsingleton_singleton.upperMinkowskiDim_eq_zero

@[simp]
lemma lowerMinkowskiDim_singleton (x : X) : lowerMinkowskiDim ({x} : Set X) = 0 :=
  subsingleton_singleton.lowerMinkowskiDim_eq_zero

@[simp]
lemma lowerMinkowskiDim_closure (s : Set X) :
    lowerMinkowskiDim (closure s) = lowerMinkowskiDim s := by
  simp only [lowerMinkowskiDim, externalCoveringNumber_closure]

@[simp]
lemma upperMinkowskiDim_closure (s : Set X) :
    upperMinkowskiDim (closure s) = upperMinkowskiDim s := by
  simp only [upperMinkowskiDim, externalCoveringNumber_closure]

/-- The upper Minkowski dimension of a union of two sets is the maximum of the upper Minkowski
dimensions. This is false for the lower Minkowski dimension. -/
lemma upperMinkowskiDim_union (s t : Set X) :
    upperMinkowskiDim (s ∪ t) = max (upperMinkowskiDim s) (upperMinkowskiDim t) := by
  refine le_antisymm ?_ (max_le (upperMinkowskiDim_mono subset_union_left)
    (upperMinkowskiDim_mono subset_union_right))
  by_contra! hlt
  rw [max_lt_iff] at hlt
  obtain ⟨d₁, hd₁, h₁⟩ := exists_eventually_of_upperMinkowskiDim_lt hlt.1
  obtain ⟨d₂, hd₂, h₂⟩ := exists_eventually_of_upperMinkowskiDim_lt hlt.2
  have h_union : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
      (externalCoveringNumber ε (s ∪ t) : ℝ≥0∞) ≤ 2 * (ε : ℝ≥0∞) ^ (-((max d₁ d₂ : ℝ≥0) : ℝ)) := by
    filter_upwards [h₁, h₂, eventually_rpow_neg_le_rpow_neg (le_max_left d₁ d₂),
      eventually_rpow_neg_le_rpow_neg (le_max_right d₁ d₂)] with ε hεs hεt hm₁ hm₂
    calc (externalCoveringNumber ε (s ∪ t) : ℝ≥0∞)
        ≤ (externalCoveringNumber ε s : ℝ≥0∞) + (externalCoveringNumber ε t : ℝ≥0∞) := 
          mod_cast externalCoveringNumber_union_le ε s t
      _ ≤ (ε : ℝ≥0∞) ^ (-((max d₁ d₂ : ℝ≥0) : ℝ)) + (ε : ℝ≥0∞) ^ (-((max d₁ d₂ : ℝ≥0) : ℝ)) :=
          add_le_add (hεs.trans hm₁) (hεt.trans hm₂)
      _ = 2 * (ε : ℝ≥0∞) ^ (-((max d₁ d₂ : ℝ≥0) : ℝ)) := (two_mul _).symm
  exact (upperMinkowskiDim_le_of_eventually_le_mul (by simp) h_union).not_gt
    (mod_cast max_lt hd₁ hd₂)

section HausdorffDimension

variable {Y : Type*} [EMetricSpace Y] {s : Set Y}

private lemma tsum_ediam_closedEBall_rpow_le {C : Set Y} {ε : ℝ≥0} (hε : 0 < ε)
    (hC : (C.encard : ℝ≥0∞) ≤ (ε : ℝ≥0∞) ^ (-(d : ℝ))) :
    ∑' c : C, ediam (closedEBall (c : Y) (ε : ℝ≥0∞)) ^ (d : ℝ) ≤ (2 : ℝ≥0∞) ^ (d : ℝ) :=
  calc ∑' c : C, ediam (closedEBall (c : Y) (ε : ℝ≥0∞)) ^ (d : ℝ)
      ≤ ∑' _ : C, ((2 : ℝ≥0∞) * (ε : ℝ≥0∞)) ^ (d : ℝ) :=
        ENNReal.tsum_le_tsum fun c ↦ ENNReal.rpow_le_rpow ediam_closedEBall_le (by positivity)
    _ = (C.encard : ℝ≥0∞) * ((2 : ℝ≥0∞) * (ε : ℝ≥0∞)) ^ (d : ℝ) := ENNReal.tsum_set_const _ _
    _ ≤ (ε : ℝ≥0∞) ^ (-(d : ℝ)) * ((2 : ℝ≥0∞) * (ε : ℝ≥0∞)) ^ (d : ℝ) := by gcongr
    _ = (2 : ℝ≥0∞) ^ (d : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← mul_assoc,
          mul_right_comm, ← ENNReal.rpow_add _ _ (mod_cast hε.ne') ENNReal.coe_ne_top, 
          neg_add_cancel, ENNReal.rpow_zero, one_mul]

/-- If, frequently as `ε → 0⁺`, the set `s` can be covered by at most `ε ^ (-d : ℝ)` closed
balls of radius `ε`, then the Hausdorff dimension of `s` is at most `d`. -/
theorem dimH_le_of_frequently_le (h : ∃ᶠ ε : ℝ≥0 in 𝓝[>] 0,
    (externalCoveringNumber ε s : ℝ≥0∞) ≤ (ε : ℝ≥0∞) ^ (-(d : ℝ))) : dimH s ≤ d := by
  borelize Y
  obtain ⟨u, hu_lim, hu⟩ :=
    exists_seq_forall_of_frequently (h.and_eventually eventually_mem_nhdsWithin)
  have hu_pos : ∀ n, 0 < u n := fun n ↦ mem_Ioi.1 (hu n).2
  have hex (n : ℕ) : ∃ C : Set Y, C.Finite ∧ IsCover (u n) s C ∧
      (C.encard : ℝ≥0∞) ≤ (u n : ℝ≥0∞) ^ (-(d : ℝ)) := by
    obtain ⟨C, hC, hCe⟩ := exists_isCover_encard_eq_externalCoveringNumber (u n) s
    have hCd : (C.encard : ℝ≥0∞) ≤ (u n : ℝ≥0∞) ^ (-(d : ℝ)) := by rw [hCe]; exact (hu n).1
    refine ⟨C, encard_ne_top_iff.1 ?_, hC, hCd⟩
    simpa using (hCd.trans_lt (ENNReal.rpow_ne_top_of_nonneg' (mod_cast hu_pos n)
      ENNReal.coe_ne_top).lt_top).ne
  choose Cov hCov_fin hCov hCov_card using hex
  have : ∀ n, Countable (Cov n) := fun n ↦ (hCov_fin n).countable.to_subtype
  have hr : Tendsto (fun n ↦ 2 * (u n : ℝ≥0∞)) atTop (𝓝 0) := by
    have hu_lim' : Tendsto (fun n ↦ (u n : ℝ≥0∞)) atTop (𝓝 0) := by
      rw [← ENNReal.coe_zero]
      exact ENNReal.tendsto_coe.2 (hu_lim.mono_right nhdsWithin_le_nhds)
    simpa using ENNReal.Tendsto.const_mul hu_lim' (Or.inr (by simp))
  have hst : ∀ n, s ⊆ ⋃ c : Cov n, closedEBall (c : Y) (u n) := by
    intro n
    have := isCover_iff_subset_iUnion_closedEBall.1 (hCov n)
    rwa [biUnion_eq_iUnion] at this
  have hμ : μH[(d : ℝ)] s ≤ (2 : ℝ≥0∞) ^ (d : ℝ) := by
    apply (Measure.hausdorffMeasure_le_liminf_tsum (d : ℝ) s (fun n ↦ 2 * (u n : ℝ≥0∞)) hr
      (fun n (c : Cov n) ↦ closedEBall (c : Y) (u n))
      (Eventually.of_forall fun n c ↦ ediam_closedEBall_le)
      (Eventually.of_forall hst)).trans
    exact liminf_le_of_frequently_le' <| Frequently.of_forall fun n ↦
      tsum_ediam_closedEBall_rpow_le (hu_pos n) (hCov_card n)
  exact dimH_le_of_hausdorffMeasure_ne_top
    (ne_top_of_le_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) (by simp)) hμ)

/-- The Hausdorff dimension is at most the lower Minkowski dimension.
See [K. Falconer, *Fractal geometry*][falconer1990], Chapter 3. -/
theorem dimH_le_lowerMinkowskiDim (s : Set Y) : dimH s ≤ lowerMinkowskiDim s :=
  le_lowerMinkowskiDim fun _ ↦ dimH_le_of_frequently_le

/-- The Hausdorff dimension is at most the upper Minkowski dimension. -/
theorem dimH_le_upperMinkowskiDim (s : Set Y) : dimH s ≤ upperMinkowskiDim s :=
  (dimH_le_lowerMinkowskiDim s).trans (lowerMinkowskiDim_le_upperMinkowskiDim s)

end HausdorffDimension
