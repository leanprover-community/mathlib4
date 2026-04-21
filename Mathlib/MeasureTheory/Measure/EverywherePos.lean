/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Tactic.Group
public import Mathlib.Topology.UrysohnsLemma

/-!
# Everywhere positive sets in measure spaces

A set `s` in a topological space with a measure `μ` is *everywhere positive* (also called
*self-supporting*) if any neighborhood `n` of any point of `s` satisfies `μ (s ∩ n) > 0`.

## Main definitions and results

* `μ.IsEverywherePos s` registers that, for any point in `s`, all its neighborhoods have positive
  measure inside `s`.
* `μ.everywherePosSubset s` is the subset of `s` made of those points all of whose neighborhoods
  have positive measure inside `s`.
* `everywherePosSubset_ae_eq` shows that `s` and `μ.everywherePosSubset s` coincide almost
  everywhere if `μ` is inner regular and `s` is measurable.
* `isEverywherePos_everywherePosSubset` shows that `μ.everywherePosSubset s` satisfies the property
  `μ.IsEverywherePos` if `μ` is inner regular and `s` is measurable.

The latter two statements have also versions when `μ` is inner regular for finite measure sets,
assuming additionally that `s` has finite measure.

* `IsEverywherePos.IsGδ` proves that an everywhere positive compact closed set is a Gδ set,
  in a topological group with a left-invariant measure. This is a nontrivial statement, used
  crucially in the study of the uniqueness of Haar measures.
* `innerRegularWRT_preimage_one_hasCompactSupport_measure_ne_top`: for a Haar measure, any
  finite measure set can be approximated from inside by level sets of continuous
  compactly supported functions. This property is also known as completion-regularity of Haar
  measures.
-/

@[expose] public section

open scoped Topology ENNReal NNReal
open Set Filter

namespace MeasureTheory.Measure

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α]

/-- A set `s` is *everywhere positive* (also called *self-supporting*) with respect to a
measure `μ` if it has positive measure around each of its points, i.e., if all neighborhoods `n`
of points of `s` satisfy `μ (s ∩ n) > 0`. -/
def IsEverywherePos (μ : Measure α) (s : Set α) : Prop :=
  ∀ x ∈ s, ∀ n ∈ 𝓝[s] x, 0 < μ n

/-- The everywhere positive subset of a set is the subset made of those points all of whose
neighborhoods have positive measure inside the set. -/
def everywherePosSubset (μ : Measure α) (s : Set α) : Set α :=
  {x | x ∈ s ∧ ∀ n ∈ 𝓝[s] x, 0 < μ n}

lemma everywherePosSubset_subset (μ : Measure α) (s : Set α) : μ.everywherePosSubset s ⊆ s :=
  fun _x hx ↦ hx.1

/-- The everywhere positive subset of a set is obtained by removing an open set. -/
lemma exists_isOpen_everywherePosSubset_eq_diff (μ : Measure α) (s : Set α) :
    ∃ u, IsOpen u ∧ μ.everywherePosSubset s = s \ u := by
  refine ⟨{x | ∃ n ∈ 𝓝[s] x, μ n = 0}, ?_, by ext x; simp [everywherePosSubset, pos_iff_ne_zero]⟩
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

variable {μ ν : Measure α} {s k : Set α}

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

protected lemma _root_.IsCompact.everywherePosSubset (hs : IsCompact s) :
    IsCompact (μ.everywherePosSubset s) := by
  rcases exists_isOpen_everywherePosSubset_eq_diff μ s with ⟨u, u_open, hu⟩
  rw [hu]
  exact hs.diff u_open

/-- Any compact set contained in `s \ μ.everywherePosSubset s` has zero measure. -/
lemma measure_eq_zero_of_subset_diff_everywherePosSubset
    (hk : IsCompact k) (h'k : k ⊆ s \ μ.everywherePosSubset s) : μ k = 0 := by
  apply hk.induction_on (p := fun t ↦ μ t = 0)
  · exact measure_empty
  · exact fun s t hst ht ↦ measure_mono_null hst ht
  · exact fun s t hs ht ↦ measure_union_null hs ht
  · intro x hx
    obtain ⟨u, ux, hu⟩ : ∃ u ∈ 𝓝[s] x, μ u = 0 := by
      simpa [everywherePosSubset, (h'k hx).1] using (h'k hx).2
    exact ⟨u, nhdsWithin_mono x (h'k.trans diff_subset) ux, hu⟩

/-- In a space with an inner regular measure, any measurable set coincides almost everywhere with
its everywhere positive subset. -/
lemma everywherePosSubset_ae_eq [OpensMeasurableSpace α] [InnerRegular μ] (hs : MeasurableSet s) :
    μ.everywherePosSubset s =ᵐ[μ] s := by
  simp only [ae_eq_set, diff_eq_empty.mpr (everywherePosSubset_subset μ s), measure_empty,
    true_and, (hs.diff hs.everywherePosSubset).measure_eq_iSup_isCompact, ENNReal.iSup_eq_zero]
  intro k hk h'k
  exact measure_eq_zero_of_subset_diff_everywherePosSubset h'k hk

/-- In a space with an inner regular measure for finite measure sets, any measurable set of finite
measure coincides almost everywhere with its everywhere positive subset. -/
lemma everywherePosSubset_ae_eq_of_measure_ne_top
    [OpensMeasurableSpace α] [InnerRegularCompactLTTop μ] (hs : MeasurableSet s) (h's : μ s ≠ ∞) :
    μ.everywherePosSubset s =ᵐ[μ] s := by
  have A : μ (s \ μ.everywherePosSubset s) ≠ ∞ :=
    ((measure_mono diff_subset).trans_lt h's.lt_top).ne
  simp only [ae_eq_set, diff_eq_empty.mpr (everywherePosSubset_subset μ s), measure_empty,
    true_and, (hs.diff hs.everywherePosSubset).measure_eq_iSup_isCompact_of_ne_top A,
    ENNReal.iSup_eq_zero]
  intro k hk h'k
  exact measure_eq_zero_of_subset_diff_everywherePosSubset h'k hk

/-- In a space with an inner regular measure, the everywhere positive subset of a measurable set
is itself everywhere positive. This is not obvious as `μ.everywherePosSubset s` is defined as
the points whose neighborhoods intersect `s` along positive measure subsets, but this does not
say they also intersect `μ.everywherePosSubset s` along positive measure subsets. -/
lemma isEverywherePos_everywherePosSubset
    [OpensMeasurableSpace α] [InnerRegular μ] (hs : MeasurableSet s) :
    μ.IsEverywherePos (μ.everywherePosSubset s) := by
  intro x hx n hn
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hn with ⟨u, u_mem, hu⟩
  have A : 0 < μ (u ∩ s) := by
    have : u ∩ s ∈ 𝓝[s] x := by rw [inter_comm]; exact inter_mem_nhdsWithin s u_mem
    exact hx.2 _ this
  have B : (u ∩ μ.everywherePosSubset s : Set α) =ᵐ[μ] (u ∩ s : Set α) :=
    ae_eq_set_inter (ae_eq_refl _) (everywherePosSubset_ae_eq hs)
  rw [← B.measure_eq] at A
  exact A.trans_le (measure_mono hu)

/-- In a space with an inner regular measure for finite measure sets, the everywhere positive subset
of a measurable set of finite measure is itself everywhere positive. This is not obvious as
`μ.everywherePosSubset s` is defined as the points whose neighborhoods intersect `s` along positive
measure subsets, but this does not say they also intersect `μ.everywherePosSubset s` along positive
measure subsets. -/
lemma isEverywherePos_everywherePosSubset_of_measure_ne_top
    [OpensMeasurableSpace α] [InnerRegularCompactLTTop μ] (hs : MeasurableSet s) (h's : μ s ≠ ∞) :
    μ.IsEverywherePos (μ.everywherePosSubset s) := by
  intro x hx n hn
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hn with ⟨u, u_mem, hu⟩
  have A : 0 < μ (u ∩ s) := by
    have : u ∩ s ∈ 𝓝[s] x := by rw [inter_comm]; exact inter_mem_nhdsWithin s u_mem
    exact hx.2 _ this
  have B : (u ∩ μ.everywherePosSubset s : Set α) =ᵐ[μ] (u ∩ s : Set α) :=
    ae_eq_set_inter (ae_eq_refl _) (everywherePosSubset_ae_eq_of_measure_ne_top hs h's)
  rw [← B.measure_eq] at A
  exact A.trans_le (measure_mono hu)

lemma IsEverywherePos.smul_measure (hs : IsEverywherePos μ s) {c : ℝ≥0∞} (hc : c ≠ 0) :
    IsEverywherePos (c • μ) s :=
  fun x hx n hn ↦ by simpa [hc.bot_lt, hs x hx n hn] using hc.bot_lt

lemma IsEverywherePos.smul_measure_nnreal (hs : IsEverywherePos μ s) {c : ℝ≥0} (hc : c ≠ 0) :
    IsEverywherePos (c • μ) s :=
  hs.smul_measure (by simpa using hc)

/-- If two measures coincide locally, then a set which is everywhere positive for the former is
also everywhere positive for the latter. -/
lemma IsEverywherePos.of_forall_exists_nhds_eq (hs : IsEverywherePos μ s)
    (h : ∀ x ∈ s, ∃ t ∈ 𝓝 x, ∀ u ⊆ t, ν u = μ u) : IsEverywherePos ν s := by
  intro x hx n hn
  rcases h x hx with ⟨t, t_mem, ht⟩
  grw [← inter_subset_left (s := n)]
  rw [ht (n ∩ t) inter_subset_right]
  exact hs x hx _ (inter_mem hn (mem_nhdsWithin_of_mem_nhds t_mem))

/-- If two measures coincide locally, then a set is everywhere positive for the former iff it is
everywhere positive for the latter. -/
lemma isEverywherePos_iff_of_forall_exists_nhds_eq (h : ∀ x ∈ s, ∃ t ∈ 𝓝 x, ∀ u ⊆ t, ν u = μ u) :
    IsEverywherePos ν s ↔ IsEverywherePos μ s := by
  refine ⟨fun H ↦ H.of_forall_exists_nhds_eq ?_, fun H ↦ H.of_forall_exists_nhds_eq h⟩
  intro x hx
  rcases h x hx with ⟨t, ht, h't⟩
  exact ⟨t, ht, fun u hu ↦ (h't u hu).symm⟩

/-- An open set is everywhere positive for a measure which is positive on open sets. -/
lemma _root_.IsOpen.isEverywherePos [IsOpenPosMeasure μ] (hs : IsOpen s) : IsEverywherePos μ s := by
  intro x xs n hn
  rcases mem_nhdsWithin.1 hn with ⟨u, u_open, xu, hu⟩
  apply lt_of_lt_of_le _ (measure_mono hu)
  exact (u_open.inter hs).measure_pos μ ⟨x, ⟨xu, xs⟩⟩

section IsTopologicalGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
  [IsMulLeftInvariant μ] [IsFiniteMeasureOnCompacts μ] [InnerRegularCompactLTTop μ]

open Pointwise

/-- If a compact closed set is everywhere positive with respect to a left-invariant measure on a
topological group, then it is a Gδ set. This is nontrivial, as there is no second-countability or
metrizability assumption in the statement, so a general compact closed set has no reason to be
a countable intersection of open sets. -/
@[to_additive]
lemma IsEverywherePos.IsGdelta_of_isMulLeftInvariant
    {k : Set G} (h : μ.IsEverywherePos k) (hk : IsCompact k) (h'k : IsClosed k) :
    IsGδ k := by
  /- Consider a decreasing sequence of open neighborhoods `Vₙ` of the identity, such that `g k \ k`
  has small measure for all `g ∈ Vₙ`. We claim that `k = ⋂ Vₙ k`, which proves
  the lemma as the sets on the right are open. The inclusion `⊆` is trivial.
  Let us show the converse. Take `x` in the intersection. For each `n`, write `x = vₙ yₙ` with
  `vₙ ∈ Vₙ` and `yₙ ∈ k`. Let `z ∈ k` be a cluster value of `yₙ`, by compactness. As multiplication
  by `vₙ = x yₙ⁻¹ ∈ Vₙ` changes the measure of `k` by very little, passing to the limit we get
  `μ (x z⁻¹ k \ k) = 0`. By invariance of the measure under `z x ⁻¹`, we get `μ (k \ z x⁻¹ k) = 0`.
  Assume `x ∉ k`. Then `z ∈ k \ z x⁻¹ k`. Even more, this set is a neighborhood of `z` within `k`
  (as `z x⁻¹ k` is closed), and it has zero measure. This contradicts the fact that `k` has
  positive measure around the point `z`. -/
  obtain ⟨u, -, u_mem, u_lim⟩ : ∃ u, StrictAnti u ∧ (∀ (n : ℕ), u n ∈ Ioo 0 1)
    ∧ Tendsto u atTop (𝓝 0) := exists_seq_strictAnti_tendsto' (zero_lt_one : (0 : ℝ≥0∞) < 1)
  have : ∀ n, ∃ (W : Set G), IsOpen W ∧ 1 ∈ W ∧ ∀ g ∈ W * W, μ ((g • k) \ k) < u n :=
    fun n ↦ exists_open_nhds_one_mul_subset
      (eventually_nhds_one_measure_smul_diff_lt hk h'k (u_mem n).1.ne')
  choose W W_open mem_W hW using this
  let V n := ⋂ i ∈ Finset.range n, W i
  suffices ⋂ n, V n * k ⊆ k by
    replace : k = ⋂ n, V n * k := by
      apply Subset.antisymm (subset_iInter_iff.2 (fun n ↦ ?_)) this
      exact subset_mul_right k (by simp [V, mem_W])
    rw [this]
    refine .iInter_of_isOpen fun n ↦ ?_
    exact .mul_right (isOpen_biInter_finset (fun i _hi ↦ W_open i))
  intro x hx
  choose v hv y hy hvy using mem_iInter.1 hx
  obtain ⟨z, zk, hz⟩ : ∃ z ∈ k, MapClusterPt z atTop y := hk.exists_mapClusterPt (by simp [hy])
  have A n : μ (((x * z⁻¹) • k) \ k) ≤ u n := by
    apply le_of_lt (hW _ _ ?_)
    have : W n * {z} ∈ 𝓝 z := (IsOpen.mul_right (W_open n)).mem_nhds (by simp [mem_W])
    obtain ⟨i, hi, ni⟩ : ∃ i, y i ∈ W n * {z} ∧ n < i :=
      ((hz.frequently this).and_eventually (eventually_gt_atTop n)).exists
    refine ⟨x * (y i) ⁻¹, ?_, y i * z⁻¹, by simpa using hi, by group⟩
    have I : V i ⊆ W n := iInter₂_subset n (by simp [ni])
    have J : x * (y i)⁻¹ ∈ V i := by simpa [← hvy i] using hv i
    exact I J
  have B : μ (((x * z⁻¹) • k) \ k) = 0 :=
    le_antisymm (ge_of_tendsto u_lim (Eventually.of_forall A)) bot_le
  have C : μ (k \ (z * x⁻¹) • k) = 0 := by
    have : μ ((z * x⁻¹) • (((x * z⁻¹) • k) \ k)) = 0 := by rwa [measure_smul]
    rw [← this, smul_set_sdiff, smul_smul]
    group
    simp
  by_contra H
  have : k ∩ ((z * x⁻¹) • k)ᶜ ∈ 𝓝[k] z := by
    apply inter_mem_nhdsWithin k
    apply IsOpen.mem_nhds (by simpa using h'k.smul _)
    push _ ∈ _
    contrapose H
    simpa [mem_smul_set_iff_inv_smul_mem] using H
  have : 0 < μ (k \ ((z * x⁻¹) • k)) := h z zk _ this
  exact lt_irrefl _ (C.le.trans_lt this)

/-- **Halmos' theorem: Haar measure is completion regular.** More precisely, any finite measure
set can be approximated from inside by a level set of a continuous function with compact support. -/
@[to_additive innerRegularWRT_preimage_one_hasCompactSupport_measure_ne_top_of_addGroup]
theorem innerRegularWRT_preimage_one_hasCompactSupport_measure_ne_top_of_group :
    InnerRegularWRT μ (fun s ↦ ∃ (f : G → ℝ), Continuous f ∧ HasCompactSupport f ∧ s = f ⁻¹' {1})
    (fun s ↦ MeasurableSet s ∧ μ s ≠ ∞) := by
  /- First, approximate a measurable set from inside by a compact closed set `K`. Then notice that
  the everywhere positive subset of `K` is a Gδ,
  by Lemma `IsEverywherePos.IsGdelta_of_isMulLeftInvariant`, and therefore the level set of a
  continuous compactly supported function. Moreover, it has the same measure as `K`. -/
  apply InnerRegularWRT.trans _ innerRegularWRT_isCompact_isClosed_measure_ne_top_of_group
  intro K ⟨K_comp, K_closed⟩ r hr
  let L := μ.everywherePosSubset K
  have L_comp : IsCompact L := K_comp.everywherePosSubset
  have L_closed : IsClosed L := K_closed.everywherePosSubset
  refine ⟨L, everywherePosSubset_subset μ K, ?_, ?_⟩
  · have : μ.IsEverywherePos L :=
      isEverywherePos_everywherePosSubset_of_measure_ne_top K_closed.measurableSet
      K_comp.measure_lt_top.ne
    have L_Gδ : IsGδ L := this.IsGdelta_of_isMulLeftInvariant L_comp L_closed
    obtain ⟨⟨f, f_cont⟩, Lf, -, f_comp, -⟩ : ∃ f : C(G, ℝ), L = f ⁻¹' {1} ∧ EqOn f 0 ∅
        ∧ HasCompactSupport f ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 :=
      exists_continuous_one_zero_of_isCompact_of_isGδ L_comp L_Gδ isClosed_empty
        (disjoint_empty L)
    exact ⟨f, f_cont, f_comp, Lf⟩
  · convert hr using 1
    apply measure_congr
    exact everywherePosSubset_ae_eq_of_measure_ne_top K_closed.measurableSet
      K_comp.measure_lt_top.ne

end IsTopologicalGroup

end Measure

end MeasureTheory
