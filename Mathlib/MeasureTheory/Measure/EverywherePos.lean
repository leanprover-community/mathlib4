/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.MeasureTheory.Constructions.Prod.Integral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.UrysohnsLemma
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Everywhere positive sets in measure spaces

A set `s` in a topological space with a measure `μ` is *completely positive*
(also called *self-supporting*) if any neighborhood `n` of any point of `s`
satisfies `μ (s ∩ n) > 0`.


-/

open scoped Topology ENNReal
open Set Filter

namespace MeasureTheory.Measure

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α]

/-- A set `s` is *everywhere positive* (also called *self-supporting*) with respect to a
measure `μ` if it has positive measure around each of its points, i.e., if all neighborhoods `n`
of points of `s` satisfy `μ (s ∩ n) > 0`. -/
@[pp_dot] def IsEverywherePos (μ : Measure α) (s : Set α) : Prop :=
  ∀ x ∈ s, ∀ n ∈ 𝓝[s] x, 0 < μ n

/-- * The everywhere positive subset of a set is the subset made of those points all of whose
neighborhoods have positive measure inside the set. -/
@[pp_dot] def everywherePosSubset (μ : Measure α) (s : Set α) : Set α :=
  {x | x ∈ s ∧ ∀ n ∈ 𝓝[s] x, 0 < μ n}

lemma everywherePosSubset_subset (s : Set α) (μ : Measure α) : μ.everywherePosSubset s ⊆ s :=
  fun _x hx ↦ hx.1

lemma exists_isOpen_everywherePosSubset_eq_diff (μ : Measure α) (s : Set α) :
    ∃ u, IsOpen u ∧ μ.everywherePosSubset s = s \ u := by
  refine ⟨{x | ∃ n ∈ 𝓝[s] x, μ n = 0}, ?_, by ext x; simp [everywherePosSubset, zero_lt_iff]⟩
  rw [isOpen_iff_mem_nhds]
  intro x ⟨n, ns, hx⟩
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 ns with ⟨v, vx, hv⟩
  rcases mem_nhds_iff.1 vx with ⟨w, wv, w_open, xw⟩
  have A : w ⊆ {x | ∃ n ∈ 𝓝[s] x, μ n = 0} := by
    intro y yw
    refine ⟨s ∩ w, inter_mem_nhdsWithin _ (w_open.mem_nhds yw), measure_mono_null ?_ hx⟩
    rw [inter_comm]
    exact (inter_subset_inter_left _ wv).trans hv
  have B : w ∈ 𝓝 x := w_open.mem_nhds xw
  exact mem_of_superset B A

variable {μ : Measure α} {s k : Set α}

protected lemma _root_.MeasurableSet.everywherePosSubset [OpensMeasurableSpace α]
    (hs : MeasurableSet s) :
    MeasurableSet (μ.everywherePosSubset s) := by
  rcases exists_isOpen_everywherePosSubset_eq_diff μ s with ⟨u, u_open, hu⟩
  rw [hu]
  exact hs.diff u_open.measurableSet

protected lemma _root_.IsClosed.everywherePosSubset (hs : IsClosed s) :
    IsClosed (μ.everywherePosSubset s) := by
  rcases exists_isOpen_everywherePosSubset_eq_diff μ s with ⟨u, u_open, hu⟩
  rw [hu]
  exact hs.sdiff u_open

protected lemma _root_.IsCompact.everywherePosSubset (hs : IsClosed s) :
    IsClosed (μ.everywherePosSubset s) := by
  rcases exists_isOpen_everywherePosSubset_eq_diff μ s with ⟨u, u_open, hu⟩
  rw [hu]
  exact hs.sdiff u_open

lemma measure_eq_zero_of_subset_diff_everywherePosSubset
    (hk : IsCompact k) (h'k : k ⊆ s \ μ.everywherePosSubset s) : μ k = 0 := by sorry

lemma everywherePosSubset_ae_eq [InnerRegular μ] (hs : MeasurableSet s) :
    μ.everywherePosSubset s =ᵐ[μ] s := by sorry

lemma everywherePosSubset_ae_eq_of_measure_ne_top [InnerRegularCompactLTTop μ]
    (hs : MeasurableSet s) (h's : μ s ≠ ∞) :
    μ.everywherePosSubset s =ᵐ[μ] s := by sorry

lemma isEverywherePos_everywherePosSubset [InnerRegular μ] (hs : MeasurableSet s) :
    μ.IsEverywherePos (μ.everywherePosSubset s) := sorry

lemma isEverywherePos_everywherePosSubset_of_measure_ne_top [InnerRegularCompactLTTop μ]
    (hs : MeasurableSet s) (h's : μ s ≠ ∞) :
    μ.IsEverywherePos (μ.everywherePosSubset s) := sorry

open Pointwise

lemma IsEverywherePos.IsGdelta {G : Type*} [Group G] [TopologicalSpace G] [TopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
    [IsMulLeftInvariant μ] [IsFiniteMeasureOnCompacts μ] [InnerRegularCompactLTTop μ] {k : Set G}
    (h : μ.IsEverywherePos k) (hk : IsCompact k) (h'k : IsClosed k) :
    IsGδ k := by
  obtain ⟨u, -, u_mem, u_lim⟩ : ∃ u, StrictAnti u ∧ (∀ (n : ℕ), u n ∈ Ioo 0 1)
    ∧ Tendsto u atTop (𝓝 0) := exists_seq_strictAnti_tendsto' (zero_lt_one : (0 : ℝ≥0∞) < 1)
  have : ∀ n, ∃ (W : Set G), IsOpen W ∧ 1 ∈ W ∧ ∀ g ∈ W * W, μ ((g • k) \ k) ≤ u n := sorry
  choose W W_open mem_W hW using this
  let V n := ⋂ i ∈ Finset.range n, W i
  suffices ⋂ n, V n * k ⊆ k by
    have : k = ⋂ n, V n * k := by
      apply Subset.antisymm (subset_iInter_iff.2 (fun n ↦ ?_)) this
      exact subset_mul_right k (by simp [mem_W])
    rw [this]
    refine isGδ_iInter_of_isOpen (fun n ↦ ?_)
    exact IsOpen.mul_right (isOpen_biInter_finset (fun i hi ↦ W_open i))
  intro x hx
  choose v hv y hy hvy using mem_iInter.1 hx
  obtain ⟨z, zk, hz⟩ : ∃ z ∈ k, MapClusterPt z atTop y := hk.exists_mapClusterPt (by simp [hy])
  have A n : μ (((x * z ⁻¹) • k) \ k) ≤ u n := by
    apply hW
    have : W n * {z} ∈ 𝓝 z := (IsOpen.mul_right (W_open n)).mem_nhds (by simp [mem_W])
    obtain ⟨i, hi, ni⟩ : ∃ i, y i ∈ W n * {z} ∧ n < i :=
      (((mapClusterPt_iff _ _ _).1 hz _ this).and_eventually (eventually_gt_atTop n)).exists
    refine ⟨x * (y i) ⁻¹, ?_, y i * z⁻¹, by simpa using hi, by group⟩
    have I : V i ⊆ W n := iInter₂_subset n (by simp [ni])
    have J : x * (y i) ⁻¹ ∈ V i := by simpa [← hvy i] using hv i
    exact I J
  have B : μ (((x * z ⁻¹) • k) \ k) = 0 :=
    le_antisymm (ge_of_tendsto u_lim (eventually_of_forall A)) bot_le
  have C : μ (k \ ((z * x⁻¹) • k)) = 0 := by
    have : μ ((z * x⁻¹) • (((x * z ⁻¹) • k) \ k)) = 0 := by rwa [measure_smul]
    convert this using 2
    rw [smul_set_sdiff, smul_smul]
    group
    simp
  by_contra H
  have : k ∩ ((z * x⁻¹) • k)ᶜ ∈ 𝓝[k] z := by
    apply inter_mem_nhdsWithin k
    apply IsOpen.mem_nhds (by simpa using h'k.smul _)
    simp only [mem_compl_iff]
    contrapose! H
    simpa [mem_smul_set_iff_inv_smul_mem] using H
  have : 0 < μ (k \ ((z * x⁻¹) • k)) := h z zk _ this
  exact lt_irrefl _ (C.le.trans_lt this)
