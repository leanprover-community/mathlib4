/-
Copyright (c) 2015, 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Cauchy

/-!
## Boundedness in (pseudo)-metric spaces

This file contains one definition, and various results on boundedness in pseudo-metric spaces.
* `Metric.diam s` : The `iSup` of the distances of members of `s`.
  Defined in terms of `EMetric.diam`, for better handling of the case when it should be infinite.

* `isBounded_iff_subset_closedBall`: a non-empty set is bounded if and only if
   it is is included in some closed ball
* describing the cobounded filter, relating to the cocompact filter
* `IsCompact.isBounded`: compact sets are bounded
* `TotallyBounded.isBounded`: totally bounded sets are bounded
* `isCompact_iff_isClosed_bounded`, the **Heine–Borel theorem**:
   in a proper space, a set is compact if and only if it is closed and bounded.
* `cobounded_eq_cocompact`: in a proper space, cobounded and compact sets are the same
diameter of a subset, and its relation to boundedness

## Tags

metric, pseudo_metric, bounded, diameter, Heine-Borel theorem
-/

open Set Filter Bornology
open scoped ENNReal Uniformity Topology Pointwise

universe u v w

variable {α : Type u} {β : Type v} {X ι : Type*}
variable [PseudoMetricSpace α]

namespace Metric

#align metric.bounded Bornology.IsBounded

section Bounded

variable {x : α} {s t : Set α} {r : ℝ}

#noalign metric.bounded_iff_is_bounded

#align metric.bounded_empty Bornology.isBounded_empty
#align metric.bounded_iff_mem_bounded Bornology.isBounded_iff_forall_mem
#align metric.bounded.mono Bornology.IsBounded.subset

/-- Closed balls are bounded -/
theorem isBounded_closedBall : IsBounded (closedBall x r) :=
  isBounded_iff.2 ⟨r + r, fun y hy z hz =>
    calc dist y z ≤ dist y x + dist z x := dist_triangle_right _ _ _
    _ ≤ r + r := add_le_add hy hz⟩
#align metric.bounded_closed_ball Metric.isBounded_closedBall

/-- Open balls are bounded -/
theorem isBounded_ball : IsBounded (ball x r) :=
  isBounded_closedBall.subset ball_subset_closedBall
#align metric.bounded_ball Metric.isBounded_ball

/-- Spheres are bounded -/
theorem isBounded_sphere : IsBounded (sphere x r) :=
  isBounded_closedBall.subset sphere_subset_closedBall
#align metric.bounded_sphere Metric.isBounded_sphere

/-- Given a point, a bounded subset is included in some ball around this point -/
theorem isBounded_iff_subset_closedBall (c : α) : IsBounded s ↔ ∃ r, s ⊆ closedBall c r :=
  ⟨fun h ↦ (isBounded_iff.1 (h.insert c)).imp fun _r hr _x hx ↦ hr (.inr hx) (mem_insert _ _),
    fun ⟨_r, hr⟩ ↦ isBounded_closedBall.subset hr⟩
#align metric.bounded_iff_subset_ball Metric.isBounded_iff_subset_closedBall

theorem _root_.Bornology.IsBounded.subset_closedBall (h : IsBounded s) (c : α) :
    ∃ r, s ⊆ closedBall c r :=
  (isBounded_iff_subset_closedBall c).1 h
#align metric.bounded.subset_ball Bornology.IsBounded.subset_closedBall

theorem _root_.Bornology.IsBounded.subset_ball_lt (h : IsBounded s) (a : ℝ) (c : α) :
    ∃ r, a < r ∧ s ⊆ ball c r :=
  let ⟨r, hr⟩ := h.subset_closedBall c
  ⟨max r a + 1, (le_max_right _ _).trans_lt (lt_add_one _), hr.trans <| closedBall_subset_ball <|
    (le_max_left _ _).trans_lt (lt_add_one _)⟩

theorem _root_.Bornology.IsBounded.subset_ball (h : IsBounded s) (c : α) : ∃ r, s ⊆ ball c r :=
  (h.subset_ball_lt 0 c).imp fun _ ↦ And.right

theorem isBounded_iff_subset_ball (c : α) : IsBounded s ↔ ∃ r, s ⊆ ball c r :=
  ⟨(IsBounded.subset_ball · c), fun ⟨_r, hr⟩ ↦ isBounded_ball.subset hr⟩

theorem _root_.Bornology.IsBounded.subset_closedBall_lt (h : IsBounded s) (a : ℝ) (c : α) :
    ∃ r, a < r ∧ s ⊆ closedBall c r :=
  let ⟨r, har, hr⟩ := h.subset_ball_lt a c
  ⟨r, har, hr.trans ball_subset_closedBall⟩
#align metric.bounded.subset_ball_lt Bornology.IsBounded.subset_closedBall_lt

theorem isBounded_closure_of_isBounded (h : IsBounded s) : IsBounded (closure s) :=
  let ⟨C, h⟩ := isBounded_iff.1 h
  isBounded_iff.2 ⟨C, fun _a ha _b hb => isClosed_Iic.closure_subset <|
    map_mem_closure₂ continuous_dist ha hb h⟩
#align metric.bounded_closure_of_bounded Metric.isBounded_closure_of_isBounded

protected theorem _root_.Bornology.IsBounded.closure (h : IsBounded s) : IsBounded (closure s) :=
  isBounded_closure_of_isBounded h
#align metric.bounded.closure Bornology.IsBounded.closure

@[simp]
theorem isBounded_closure_iff : IsBounded (closure s) ↔ IsBounded s :=
  ⟨fun h => h.subset subset_closure, fun h => h.closure⟩
#align metric.bounded_closure_iff Metric.isBounded_closure_iff

#align metric.bounded_union Bornology.isBounded_union
#align metric.bounded.union Bornology.IsBounded.union
#align metric.bounded_bUnion Bornology.isBounded_biUnion
#align metric.bounded.prod Bornology.IsBounded.prod

theorem hasBasis_cobounded_compl_closedBall (c : α) :
    (cobounded α).HasBasis (fun _ ↦ True) (fun r ↦ (closedBall c r)ᶜ) :=
  ⟨compl_surjective.forall.2 fun _ ↦ (isBounded_iff_subset_closedBall c).trans <| by simp⟩

theorem hasBasis_cobounded_compl_ball (c : α) :
    (cobounded α).HasBasis (fun _ ↦ True) (fun r ↦ (ball c r)ᶜ) :=
  ⟨compl_surjective.forall.2 fun _ ↦ (isBounded_iff_subset_ball c).trans <| by simp⟩

@[simp]
theorem comap_dist_right_atTop (c : α) : comap (dist · c) atTop = cobounded α :=
  (atTop_basis.comap _).eq_of_same_basis <| by
    simpa only [compl_def, mem_ball, not_lt] using hasBasis_cobounded_compl_ball c

@[simp]
theorem comap_dist_left_atTop (c : α) : comap (dist c) atTop = cobounded α := by
  simpa only [dist_comm _ c] using comap_dist_right_atTop c

@[simp]
theorem tendsto_dist_right_atTop_iff (c : α) {f : β → α} {l : Filter β} :
    Tendsto (fun x ↦ dist (f x) c) l atTop ↔ Tendsto f l (cobounded α) := by
  rw [← comap_dist_right_atTop c, tendsto_comap_iff, Function.comp_def]

@[simp]
theorem tendsto_dist_left_atTop_iff (c : α) {f : β → α} {l : Filter β} :
    Tendsto (fun x ↦ dist c (f x)) l atTop ↔ Tendsto f l (cobounded α) := by
  simp only [dist_comm c, tendsto_dist_right_atTop_iff]

theorem tendsto_dist_right_cobounded_atTop (c : α) : Tendsto (dist · c) (cobounded α) atTop :=
  tendsto_iff_comap.2 (comap_dist_right_atTop c).ge

theorem tendsto_dist_left_cobounded_atTop (c : α) : Tendsto (dist c) (cobounded α) atTop :=
  tendsto_iff_comap.2 (comap_dist_left_atTop c).ge

/-- A totally bounded set is bounded -/
theorem _root_.TotallyBounded.isBounded {s : Set α} (h : TotallyBounded s) : IsBounded s :=
  -- We cover the totally bounded set by finitely many balls of radius 1,
  -- and then argue that a finite union of bounded sets is bounded
  let ⟨_t, fint, subs⟩ := (totallyBounded_iff.mp h) 1 zero_lt_one
  ((isBounded_biUnion fint).2 fun _ _ => isBounded_ball).subset subs
#align totally_bounded.bounded TotallyBounded.isBounded

/-- A compact set is bounded -/
theorem _root_.IsCompact.isBounded {s : Set α} (h : IsCompact s) : IsBounded s :=
  -- A compact set is totally bounded, thus bounded
  h.totallyBounded.isBounded
#align is_compact.bounded IsCompact.isBounded

#align metric.bounded_of_finite Set.Finite.isBounded
#align set.finite.bounded Set.Finite.isBounded
#align metric.bounded_singleton Bornology.isBounded_singleton

theorem cobounded_le_cocompact : cobounded α ≤ cocompact α :=
  hasBasis_cocompact.ge_iff.2 fun _s hs ↦ hs.isBounded
#align comap_dist_right_at_top_le_cocompact Metric.cobounded_le_cocompactₓ
#align comap_dist_left_at_top_le_cocompact Metric.cobounded_le_cocompactₓ

theorem isCobounded_iff_closedBall_compl_subset {s : Set α} (c : α) :
    IsCobounded s ↔ ∃ (r : ℝ), (Metric.closedBall c r)ᶜ ⊆ s := by
  rw [← isBounded_compl_iff, isBounded_iff_subset_closedBall c]
  apply exists_congr
  intro r
  rw [compl_subset_comm]

theorem _root_.Bornology.IsCobounded.closedBall_compl_subset {s : Set α} (hs : IsCobounded s)
    (c : α) : ∃ (r : ℝ), (Metric.closedBall c r)ᶜ ⊆ s :=
  (isCobounded_iff_closedBall_compl_subset c).mp hs

theorem closedBall_compl_subset_of_mem_cocompact {s : Set α} (hs : s ∈ cocompact α) (c : α) :
    ∃ (r : ℝ), (Metric.closedBall c r)ᶜ ⊆ s :=
  IsCobounded.closedBall_compl_subset (cobounded_le_cocompact hs) c

theorem mem_cocompact_of_closedBall_compl_subset [ProperSpace α] (c : α)
    (h : ∃ r, (closedBall c r)ᶜ ⊆ s) : s ∈ cocompact α := by
  rcases h with ⟨r, h⟩
  rw [Filter.mem_cocompact]
  exact ⟨closedBall c r, isCompact_closedBall c r, h⟩

theorem mem_cocompact_iff_closedBall_compl_subset [ProperSpace α] (c : α) :
    s ∈ cocompact α ↔ ∃ r, (closedBall c r)ᶜ ⊆ s :=
  ⟨(closedBall_compl_subset_of_mem_cocompact · _), mem_cocompact_of_closedBall_compl_subset _⟩

/-- Characterization of the boundedness of the range of a function -/
theorem isBounded_range_iff {f : β → α} : IsBounded (range f) ↔ ∃ C, ∀ x y, dist (f x) (f y) ≤ C :=
  isBounded_iff.trans <| by simp only [forall_mem_range]
#align metric.bounded_range_iff Metric.isBounded_range_iff

theorem isBounded_image_iff {f : β → α} {s : Set β} :
    IsBounded (f '' s) ↔ ∃ C, ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ C :=
  isBounded_iff.trans <| by simp only [forall_mem_image]

theorem isBounded_range_of_tendsto_cofinite_uniformity {f : β → α}
    (hf : Tendsto (Prod.map f f) (.cofinite ×ˢ .cofinite) (𝓤 α)) : IsBounded (range f) := by
  rcases (hasBasis_cofinite.prod_self.tendsto_iff uniformity_basis_dist).1 hf 1 zero_lt_one with
    ⟨s, hsf, hs1⟩
  rw [← image_union_image_compl_eq_range]
  refine (hsf.image f).isBounded.union (isBounded_image_iff.2 ⟨1, fun x hx y hy ↦ ?_⟩)
  exact le_of_lt (hs1 (x, y) ⟨hx, hy⟩)
#align metric.bounded_range_of_tendsto_cofinite_uniformity Metric.isBounded_range_of_tendsto_cofinite_uniformity

theorem isBounded_range_of_cauchy_map_cofinite {f : β → α} (hf : Cauchy (map f cofinite)) :
    IsBounded (range f) :=
  isBounded_range_of_tendsto_cofinite_uniformity <| (cauchy_map_iff.1 hf).2
#align metric.bounded_range_of_cauchy_map_cofinite Metric.isBounded_range_of_cauchy_map_cofinite

theorem _root_.CauchySeq.isBounded_range {f : ℕ → α} (hf : CauchySeq f) : IsBounded (range f) :=
  isBounded_range_of_cauchy_map_cofinite <| by rwa [Nat.cofinite_eq_atTop]
#align cauchy_seq.bounded_range CauchySeq.isBounded_range

theorem isBounded_range_of_tendsto_cofinite {f : β → α} {a : α} (hf : Tendsto f cofinite (𝓝 a)) :
    IsBounded (range f) :=
  isBounded_range_of_tendsto_cofinite_uniformity <|
    (hf.prod_map hf).mono_right <| nhds_prod_eq.symm.trans_le (nhds_le_uniformity a)
#align metric.bounded_range_of_tendsto_cofinite Metric.isBounded_range_of_tendsto_cofinite

/-- In a compact space, all sets are bounded -/
theorem isBounded_of_compactSpace [CompactSpace α] : IsBounded s :=
  isCompact_univ.isBounded.subset (subset_univ _)
#align metric.bounded_of_compact_space Metric.isBounded_of_compactSpace

theorem isBounded_range_of_tendsto (u : ℕ → α) {x : α} (hu : Tendsto u atTop (𝓝 x)) :
    IsBounded (range u) :=
  hu.cauchySeq.isBounded_range
#align metric.bounded_range_of_tendsto Metric.isBounded_range_of_tendsto

theorem disjoint_nhds_cobounded (x : α) : Disjoint (𝓝 x) (cobounded α) :=
  disjoint_of_disjoint_of_mem disjoint_compl_right (ball_mem_nhds _ one_pos) isBounded_ball

theorem disjoint_cobounded_nhds (x : α) : Disjoint (cobounded α) (𝓝 x) :=
  (disjoint_nhds_cobounded x).symm

theorem disjoint_nhdsSet_cobounded {s : Set α} (hs : IsCompact s) : Disjoint (𝓝ˢ s) (cobounded α) :=
  hs.disjoint_nhdsSet_left.2 fun _ _ ↦ disjoint_nhds_cobounded _

theorem disjoint_cobounded_nhdsSet {s : Set α} (hs : IsCompact s) : Disjoint (cobounded α) (𝓝ˢ s) :=
  (disjoint_nhdsSet_cobounded hs).symm

theorem exists_isBounded_image_of_tendsto {α β : Type*} [PseudoMetricSpace β]
    {l : Filter α} {f : α → β} {x : β} (hf : Tendsto f l (𝓝 x)) :
    ∃ s ∈ l, IsBounded (f '' s) :=
  (l.basis_sets.map f).disjoint_iff_left.mp <| (disjoint_nhds_cobounded x).mono_left hf

/-- If a function is continuous within a set `s` at every point of a compact set `k`, then it is
bounded on some open neighborhood of `k` in `s`. -/
theorem exists_isOpen_isBounded_image_inter_of_isCompact_of_forall_continuousWithinAt
    [TopologicalSpace β] {k s : Set β} {f : β → α} (hk : IsCompact k)
    (hf : ∀ x ∈ k, ContinuousWithinAt f s x) :
    ∃ t, k ⊆ t ∧ IsOpen t ∧ IsBounded (f '' (t ∩ s)) := by
  have : Disjoint (𝓝ˢ k ⊓ 𝓟 s) (comap f (cobounded α)) := by
    rw [disjoint_assoc, inf_comm, hk.disjoint_nhdsSet_left]
    exact fun x hx ↦ disjoint_left_comm.2 <|
      tendsto_comap.disjoint (disjoint_cobounded_nhds _) (hf x hx)
  rcases ((((hasBasis_nhdsSet _).inf_principal _)).disjoint_iff ((basis_sets _).comap _)).1 this
    with ⟨U, ⟨hUo, hkU⟩, t, ht, hd⟩
  refine ⟨U, hkU, hUo, (isBounded_compl_iff.2 ht).subset ?_⟩
  rwa [image_subset_iff, preimage_compl, subset_compl_iff_disjoint_right]
#align metric.exists_is_open_bounded_image_inter_of_is_compact_of_forall_continuous_within_at Metric.exists_isOpen_isBounded_image_inter_of_isCompact_of_forall_continuousWithinAt

/-- If a function is continuous at every point of a compact set `k`, then it is bounded on
some open neighborhood of `k`. -/
theorem exists_isOpen_isBounded_image_of_isCompact_of_forall_continuousAt [TopologicalSpace β]
    {k : Set β} {f : β → α} (hk : IsCompact k) (hf : ∀ x ∈ k, ContinuousAt f x) :
    ∃ t, k ⊆ t ∧ IsOpen t ∧ IsBounded (f '' t) := by
  simp_rw [← continuousWithinAt_univ] at hf
  simpa only [inter_univ] using
    exists_isOpen_isBounded_image_inter_of_isCompact_of_forall_continuousWithinAt hk hf
#align metric.exists_is_open_bounded_image_of_is_compact_of_forall_continuous_at Metric.exists_isOpen_isBounded_image_of_isCompact_of_forall_continuousAt

/-- If a function is continuous on a set `s` containing a compact set `k`, then it is bounded on
some open neighborhood of `k` in `s`. -/
theorem exists_isOpen_isBounded_image_inter_of_isCompact_of_continuousOn [TopologicalSpace β]
    {k s : Set β} {f : β → α} (hk : IsCompact k) (hks : k ⊆ s) (hf : ContinuousOn f s) :
    ∃ t, k ⊆ t ∧ IsOpen t ∧ IsBounded (f '' (t ∩ s)) :=
  exists_isOpen_isBounded_image_inter_of_isCompact_of_forall_continuousWithinAt hk fun x hx =>
    hf x (hks hx)
#align metric.exists_is_open_bounded_image_inter_of_is_compact_of_continuous_on Metric.exists_isOpen_isBounded_image_inter_of_isCompact_of_continuousOn

/-- If a function is continuous on a neighborhood of a compact set `k`, then it is bounded on
some open neighborhood of `k`. -/
theorem exists_isOpen_isBounded_image_of_isCompact_of_continuousOn [TopologicalSpace β]
    {k s : Set β} {f : β → α} (hk : IsCompact k) (hs : IsOpen s) (hks : k ⊆ s)
    (hf : ContinuousOn f s) : ∃ t, k ⊆ t ∧ IsOpen t ∧ IsBounded (f '' t) :=
  exists_isOpen_isBounded_image_of_isCompact_of_forall_continuousAt hk fun _x hx =>
    hf.continuousAt (hs.mem_nhds (hks hx))
#align metric.exists_is_open_bounded_image_of_is_compact_of_continuous_on Metric.exists_isOpen_isBounded_image_of_isCompact_of_continuousOn

/-- The **Heine–Borel theorem**: In a proper space, a closed bounded set is compact. -/
theorem isCompact_of_isClosed_isBounded [ProperSpace α] (hc : IsClosed s) (hb : IsBounded s) :
    IsCompact s := by
  rcases eq_empty_or_nonempty s with (rfl | ⟨x, -⟩)
  · exact isCompact_empty
  · rcases hb.subset_closedBall x with ⟨r, hr⟩
    exact (isCompact_closedBall x r).of_isClosed_subset hc hr
#align metric.is_compact_of_is_closed_bounded Metric.isCompact_of_isClosed_isBounded

/-- The **Heine–Borel theorem**: In a proper space, the closure of a bounded set is compact. -/
theorem _root_.Bornology.IsBounded.isCompact_closure [ProperSpace α] (h : IsBounded s) :
    IsCompact (closure s) :=
  isCompact_of_isClosed_isBounded isClosed_closure h.closure
#align metric.bounded.is_compact_closure Bornology.IsBounded.isCompact_closure

-- Porting note (#11215): TODO: assume `[MetricSpace α]`
-- instead of `[PseudoMetricSpace α] [T2Space α]`
/-- The **Heine–Borel theorem**:
In a proper Hausdorff space, a set is compact if and only if it is closed and bounded. -/
theorem isCompact_iff_isClosed_bounded [T2Space α] [ProperSpace α] :
    IsCompact s ↔ IsClosed s ∧ IsBounded s :=
  ⟨fun h => ⟨h.isClosed, h.isBounded⟩, fun h => isCompact_of_isClosed_isBounded h.1 h.2⟩
#align metric.is_compact_iff_is_closed_bounded Metric.isCompact_iff_isClosed_bounded

theorem compactSpace_iff_isBounded_univ [ProperSpace α] :
    CompactSpace α ↔ IsBounded (univ : Set α) :=
  ⟨@isBounded_of_compactSpace α _ _, fun hb => ⟨isCompact_of_isClosed_isBounded isClosed_univ hb⟩⟩
#align metric.compact_space_iff_bounded_univ Metric.compactSpace_iff_isBounded_univ

section ConditionallyCompleteLinearOrder

variable [Preorder α] [CompactIccSpace α]

theorem isBounded_Icc (a b : α) : IsBounded (Icc a b) :=
  (totallyBounded_Icc a b).isBounded
#align metric.bounded_Icc Metric.isBounded_Icc

theorem isBounded_Ico (a b : α) : IsBounded (Ico a b) :=
  (totallyBounded_Ico a b).isBounded
#align metric.bounded_Ico Metric.isBounded_Ico

theorem isBounded_Ioc (a b : α) : IsBounded (Ioc a b) :=
  (totallyBounded_Ioc a b).isBounded
#align metric.bounded_Ioc Metric.isBounded_Ioc

theorem isBounded_Ioo (a b : α) : IsBounded (Ioo a b) :=
  (totallyBounded_Ioo a b).isBounded
#align metric.bounded_Ioo Metric.isBounded_Ioo

/-- In a pseudo metric space with a conditionally complete linear order such that the order and the
    metric structure give the same topology, any order-bounded set is metric-bounded. -/
theorem isBounded_of_bddAbove_of_bddBelow {s : Set α} (h₁ : BddAbove s) (h₂ : BddBelow s) :
    IsBounded s :=
  let ⟨u, hu⟩ := h₁
  let ⟨l, hl⟩ := h₂
  (isBounded_Icc l u).subset (fun _x hx => mem_Icc.mpr ⟨hl hx, hu hx⟩)
#align metric.bounded_of_bdd_above_of_bdd_below Metric.isBounded_of_bddAbove_of_bddBelow

end ConditionallyCompleteLinearOrder

end Bounded

section Diam

variable {s : Set α} {x y z : α}

/-- The diameter of a set in a metric space. To get controllable behavior even when the diameter
should be infinite, we express it in terms of the `EMetric.diam` -/
noncomputable def diam (s : Set α) : ℝ :=
  ENNReal.toReal (EMetric.diam s)
#align metric.diam Metric.diam

/-- The diameter of a set is always nonnegative -/
theorem diam_nonneg : 0 ≤ diam s :=
  ENNReal.toReal_nonneg
#align metric.diam_nonneg Metric.diam_nonneg

theorem diam_subsingleton (hs : s.Subsingleton) : diam s = 0 := by
  simp only [diam, EMetric.diam_subsingleton hs, ENNReal.zero_toReal]
#align metric.diam_subsingleton Metric.diam_subsingleton

/-- The empty set has zero diameter -/
@[simp]
theorem diam_empty : diam (∅ : Set α) = 0 :=
  diam_subsingleton subsingleton_empty
#align metric.diam_empty Metric.diam_empty

/-- A singleton has zero diameter -/
@[simp]
theorem diam_singleton : diam ({x} : Set α) = 0 :=
  diam_subsingleton subsingleton_singleton
#align metric.diam_singleton Metric.diam_singleton

@[to_additive (attr := simp)]
theorem diam_one [One α] : diam (1 : Set α) = 0 :=
  diam_singleton
#align metric.diam_one Metric.diam_one
#align metric.diam_zero Metric.diam_zero

-- Does not work as a simp-lemma, since {x, y} reduces to (insert y {x})
theorem diam_pair : diam ({x, y} : Set α) = dist x y := by
  simp only [diam, EMetric.diam_pair, dist_edist]
#align metric.diam_pair Metric.diam_pair

-- Does not work as a simp-lemma, since {x, y, z} reduces to (insert z (insert y {x}))
theorem diam_triple :
    Metric.diam ({x, y, z} : Set α) = max (max (dist x y) (dist x z)) (dist y z) := by
  simp only [Metric.diam, EMetric.diam_triple, dist_edist]
  rw [ENNReal.toReal_max, ENNReal.toReal_max] <;> apply_rules [ne_of_lt, edist_lt_top, max_lt]
#align metric.diam_triple Metric.diam_triple

/-- If the distance between any two points in a set is bounded by some constant `C`,
then `ENNReal.ofReal C` bounds the emetric diameter of this set. -/
theorem ediam_le_of_forall_dist_le {C : ℝ} (h : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ C) :
    EMetric.diam s ≤ ENNReal.ofReal C :=
  EMetric.diam_le fun x hx y hy => (edist_dist x y).symm ▸ ENNReal.ofReal_le_ofReal (h x hx y hy)
#align metric.ediam_le_of_forall_dist_le Metric.ediam_le_of_forall_dist_le

/-- If the distance between any two points in a set is bounded by some non-negative constant,
this constant bounds the diameter. -/
theorem diam_le_of_forall_dist_le {C : ℝ} (h₀ : 0 ≤ C) (h : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ C) :
    diam s ≤ C :=
  ENNReal.toReal_le_of_le_ofReal h₀ (ediam_le_of_forall_dist_le h)
#align metric.diam_le_of_forall_dist_le Metric.diam_le_of_forall_dist_le

/-- If the distance between any two points in a nonempty set is bounded by some constant,
this constant bounds the diameter. -/
theorem diam_le_of_forall_dist_le_of_nonempty (hs : s.Nonempty) {C : ℝ}
    (h : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ C) : diam s ≤ C :=
  have h₀ : 0 ≤ C :=
    let ⟨x, hx⟩ := hs
    le_trans dist_nonneg (h x hx x hx)
  diam_le_of_forall_dist_le h₀ h
#align metric.diam_le_of_forall_dist_le_of_nonempty Metric.diam_le_of_forall_dist_le_of_nonempty

/-- The distance between two points in a set is controlled by the diameter of the set. -/
theorem dist_le_diam_of_mem' (h : EMetric.diam s ≠ ⊤) (hx : x ∈ s) (hy : y ∈ s) :
    dist x y ≤ diam s := by
  rw [diam, dist_edist]
  rw [ENNReal.toReal_le_toReal (edist_ne_top _ _) h]
  exact EMetric.edist_le_diam_of_mem hx hy
#align metric.dist_le_diam_of_mem' Metric.dist_le_diam_of_mem'

/-- Characterize the boundedness of a set in terms of the finiteness of its emetric.diameter. -/
theorem isBounded_iff_ediam_ne_top : IsBounded s ↔ EMetric.diam s ≠ ⊤ :=
  isBounded_iff.trans <| Iff.intro
    (fun ⟨_C, hC⟩ => ne_top_of_le_ne_top ENNReal.ofReal_ne_top <| ediam_le_of_forall_dist_le hC)
    fun h => ⟨diam s, fun _x hx _y hy => dist_le_diam_of_mem' h hx hy⟩
#align metric.bounded_iff_ediam_ne_top Metric.isBounded_iff_ediam_ne_top

alias ⟨_root_.Bornology.IsBounded.ediam_ne_top, _⟩ := isBounded_iff_ediam_ne_top
#align metric.bounded.ediam_ne_top Bornology.IsBounded.ediam_ne_top

theorem ediam_eq_top_iff_unbounded : EMetric.diam s = ⊤ ↔ ¬IsBounded s :=
  isBounded_iff_ediam_ne_top.not_left.symm

theorem ediam_univ_eq_top_iff_noncompact [ProperSpace α] :
    EMetric.diam (univ : Set α) = ∞ ↔ NoncompactSpace α := by
  rw [← not_compactSpace_iff, compactSpace_iff_isBounded_univ, isBounded_iff_ediam_ne_top,
    Classical.not_not]
#align metric.ediam_univ_eq_top_iff_noncompact Metric.ediam_univ_eq_top_iff_noncompact

@[simp]
theorem ediam_univ_of_noncompact [ProperSpace α] [NoncompactSpace α] :
    EMetric.diam (univ : Set α) = ∞ :=
  ediam_univ_eq_top_iff_noncompact.mpr ‹_›
#align metric.ediam_univ_of_noncompact Metric.ediam_univ_of_noncompact

@[simp]
theorem diam_univ_of_noncompact [ProperSpace α] [NoncompactSpace α] : diam (univ : Set α) = 0 := by
  simp [diam]
#align metric.diam_univ_of_noncompact Metric.diam_univ_of_noncompact

/-- The distance between two points in a set is controlled by the diameter of the set. -/
theorem dist_le_diam_of_mem (h : IsBounded s) (hx : x ∈ s) (hy : y ∈ s) : dist x y ≤ diam s :=
  dist_le_diam_of_mem' h.ediam_ne_top hx hy
#align metric.dist_le_diam_of_mem Metric.dist_le_diam_of_mem

theorem ediam_of_unbounded (h : ¬IsBounded s) : EMetric.diam s = ∞ := ediam_eq_top_iff_unbounded.2 h
#align metric.ediam_of_unbounded Metric.ediam_of_unbounded

/-- An unbounded set has zero diameter. If you would prefer to get the value ∞, use `EMetric.diam`.
This lemma makes it possible to avoid side conditions in some situations -/
theorem diam_eq_zero_of_unbounded (h : ¬IsBounded s) : diam s = 0 := by
  rw [diam, ediam_of_unbounded h, ENNReal.top_toReal]
#align metric.diam_eq_zero_of_unbounded Metric.diam_eq_zero_of_unbounded

/-- If `s ⊆ t`, then the diameter of `s` is bounded by that of `t`, provided `t` is bounded. -/
theorem diam_mono {s t : Set α} (h : s ⊆ t) (ht : IsBounded t) : diam s ≤ diam t :=
  ENNReal.toReal_mono ht.ediam_ne_top <| EMetric.diam_mono h
#align metric.diam_mono Metric.diam_mono

/-- The diameter of a union is controlled by the sum of the diameters, and the distance between
any two points in each of the sets. This lemma is true without any side condition, since it is
obviously true if `s ∪ t` is unbounded. -/
theorem diam_union {t : Set α} (xs : x ∈ s) (yt : y ∈ t) :
    diam (s ∪ t) ≤ diam s + dist x y + diam t := by
  simp only [diam, dist_edist]
  refine (ENNReal.toReal_le_add' (EMetric.diam_union xs yt) ?_ ?_).trans
    (add_le_add_right ENNReal.toReal_add_le _)
  · simp only [ENNReal.add_eq_top, edist_ne_top, or_false]
    exact fun h ↦ top_unique <| h ▸ EMetric.diam_mono (subset_union_left _ _)
  · exact fun h ↦ top_unique <| h ▸ EMetric.diam_mono (subset_union_right _ _)
#align metric.diam_union Metric.diam_union

/-- If two sets intersect, the diameter of the union is bounded by the sum of the diameters. -/
theorem diam_union' {t : Set α} (h : (s ∩ t).Nonempty) : diam (s ∪ t) ≤ diam s + diam t := by
  rcases h with ⟨x, ⟨xs, xt⟩⟩
  simpa using diam_union xs xt
#align metric.diam_union' Metric.diam_union'

theorem diam_le_of_subset_closedBall {r : ℝ} (hr : 0 ≤ r) (h : s ⊆ closedBall x r) :
    diam s ≤ 2 * r :=
  diam_le_of_forall_dist_le (mul_nonneg zero_le_two hr) fun a ha b hb =>
    calc
      dist a b ≤ dist a x + dist b x := dist_triangle_right _ _ _
      _ ≤ r + r := add_le_add (h ha) (h hb)
      _ = 2 * r := by simp [mul_two, mul_comm]
#align metric.diam_le_of_subset_closed_ball Metric.diam_le_of_subset_closedBall

/-- The diameter of a closed ball of radius `r` is at most `2 r`. -/
theorem diam_closedBall {r : ℝ} (h : 0 ≤ r) : diam (closedBall x r) ≤ 2 * r :=
  diam_le_of_subset_closedBall h Subset.rfl
#align metric.diam_closed_ball Metric.diam_closedBall

/-- The diameter of a ball of radius `r` is at most `2 r`. -/
theorem diam_ball {r : ℝ} (h : 0 ≤ r) : diam (ball x r) ≤ 2 * r :=
  diam_le_of_subset_closedBall h ball_subset_closedBall
#align metric.diam_ball Metric.diam_ball

/-- If a family of complete sets with diameter tending to `0` is such that each finite intersection
is nonempty, then the total intersection is also nonempty. -/
theorem _root_.IsComplete.nonempty_iInter_of_nonempty_biInter {s : ℕ → Set α}
    (h0 : IsComplete (s 0)) (hs : ∀ n, IsClosed (s n)) (h's : ∀ n, IsBounded (s n))
    (h : ∀ N, (⋂ n ≤ N, s n).Nonempty) (h' : Tendsto (fun n => diam (s n)) atTop (𝓝 0)) :
    (⋂ n, s n).Nonempty := by
  let u N := (h N).some
  have I : ∀ n N, n ≤ N → u N ∈ s n := by
    intro n N hn
    apply mem_of_subset_of_mem _ (h N).choose_spec
    intro x hx
    simp only [mem_iInter] at hx
    exact hx n hn
  have : CauchySeq u := by
    apply cauchySeq_of_le_tendsto_0 _ _ h'
    intro m n N hm hn
    exact dist_le_diam_of_mem (h's N) (I _ _ hm) (I _ _ hn)
  obtain ⟨x, -, xlim⟩ : ∃ x ∈ s 0, Tendsto (fun n : ℕ => u n) atTop (𝓝 x) :=
    cauchySeq_tendsto_of_isComplete h0 (fun n => I 0 n (zero_le _)) this
  refine ⟨x, mem_iInter.2 fun n => ?_⟩
  apply (hs n).mem_of_tendsto xlim
  filter_upwards [Ici_mem_atTop n] with p hp
  exact I n p hp
#align is_complete.nonempty_Inter_of_nonempty_bInter IsComplete.nonempty_iInter_of_nonempty_biInter

/-- In a complete space, if a family of closed sets with diameter tending to `0` is such that each
finite intersection is nonempty, then the total intersection is also nonempty. -/
theorem nonempty_iInter_of_nonempty_biInter [CompleteSpace α] {s : ℕ → Set α}
    (hs : ∀ n, IsClosed (s n)) (h's : ∀ n, IsBounded (s n)) (h : ∀ N, (⋂ n ≤ N, s n).Nonempty)
    (h' : Tendsto (fun n => diam (s n)) atTop (𝓝 0)) : (⋂ n, s n).Nonempty :=
  (hs 0).isComplete.nonempty_iInter_of_nonempty_biInter hs h's h h'
#align metric.nonempty_Inter_of_nonempty_bInter Metric.nonempty_iInter_of_nonempty_biInter

end Diam

end Metric

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension for the `positivity` tactic: the diameter of a set is always nonnegative. -/
@[positivity Metric.diam _]
def evalDiam : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@Metric.diam _ $inst $s) =>
    assertInstancesCommute
    pure (.nonnegative q(Metric.diam_nonneg))
  | _, _, _ => throwError "not ‖ · ‖"

end Mathlib.Meta.Positivity

open Metric

theorem Metric.cobounded_eq_cocompact [ProperSpace α] : cobounded α = cocompact α := by
  nontriviality α; inhabit α
  exact cobounded_le_cocompact.antisymm <| (hasBasis_cobounded_compl_closedBall default).ge_iff.2
    fun _ _ ↦ (isCompact_closedBall _ _).compl_mem_cocompact
#align comap_dist_right_at_top_eq_cocompact Metric.cobounded_eq_cocompact

theorem tendsto_dist_right_cocompact_atTop [ProperSpace α] (x : α) :
    Tendsto (dist · x) (cocompact α) atTop :=
  (tendsto_dist_right_cobounded_atTop x).mono_left cobounded_eq_cocompact.ge
#align tendsto_dist_right_cocompact_at_top tendsto_dist_right_cocompact_atTop

theorem tendsto_dist_left_cocompact_atTop [ProperSpace α] (x : α) :
    Tendsto (dist x) (cocompact α) atTop :=
  (tendsto_dist_left_cobounded_atTop x).mono_left cobounded_eq_cocompact.ge
#align tendsto_dist_left_cocompact_at_top tendsto_dist_left_cocompact_atTop

theorem comap_dist_left_atTop_eq_cocompact [ProperSpace α] (x : α) :
    comap (dist x) atTop = cocompact α := by simp [cobounded_eq_cocompact]
#align comap_dist_left_at_top_eq_cocompact comap_dist_left_atTop_eq_cocompact

theorem tendsto_cocompact_of_tendsto_dist_comp_atTop {f : β → α} {l : Filter β} (x : α)
    (h : Tendsto (fun y => dist (f y) x) l atTop) : Tendsto f l (cocompact α) :=
  ((tendsto_dist_right_atTop_iff _).1 h).mono_right cobounded_le_cocompact
#align tendsto_cocompact_of_tendsto_dist_comp_at_top tendsto_cocompact_of_tendsto_dist_comp_atTop

theorem Metric.finite_isBounded_inter_isClosed [ProperSpace α] {K s : Set α} [DiscreteTopology s]
    (hK : IsBounded K) (hs : IsClosed s) : Set.Finite (K ∩ s) := by
  refine Set.Finite.subset (IsCompact.finite ?_ ?_) (Set.inter_subset_inter_left s subset_closure)
  · exact hK.isCompact_closure.inter_right hs
  · exact DiscreteTopology.of_subset inferInstance (Set.inter_subset_right _ s)
