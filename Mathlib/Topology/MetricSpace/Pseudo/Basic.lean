/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
module

public import Mathlib.Data.ENNReal.Real
public import Mathlib.Tactic.Bound.Attribute
public import Mathlib.Topology.EMetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic

/-!
## Pseudo-metric spaces

Further results about pseudo-metric spaces.

-/

public section

open Set Filter TopologicalSpace Bornology
open scoped ENNReal NNReal Uniformity Topology

universe u v

variable {α : Type u} {β : Type v} {ι : Type*}

variable [PseudoMetricSpace α]

/-- The triangle (polygon) inequality for sequences of points; `Finset.Ico` version. -/
theorem dist_le_Ico_sum_dist (f : ℕ → α) {m n} (h : m ≤ n) :
    dist (f m) (f n) ≤ ∑ i ∈ Finset.Ico m n, dist (f i) (f (i + 1)) := by
  induction n, h using Nat.le_induction with
  | base => rw [Finset.Ico_self, Finset.sum_empty, dist_self]
  | succ n hle ihn =>
    calc
      dist (f m) (f (n + 1)) ≤ dist (f m) (f n) + dist (f n) (f (n + 1)) := dist_triangle _ _ _
      _ ≤ (∑ i ∈ Finset.Ico m n, _) + _ := add_le_add ihn le_rfl
      _ = ∑ i ∈ Finset.Ico m (n + 1), _ := by
        rw [← Finset.insert_Ico_right_eq_Ico_add_one hle, Finset.sum_insert, add_comm]; simp

/-- The triangle (polygon) inequality for sequences of points; `Finset.range` version. -/
theorem dist_le_range_sum_dist (f : ℕ → α) (n : ℕ) :
    dist (f 0) (f n) ≤ ∑ i ∈ Finset.range n, dist (f i) (f (i + 1)) :=
  Nat.Ico_zero_eq_range ▸ dist_le_Ico_sum_dist f (Nat.zero_le n)

/-- A version of `dist_le_Ico_sum_dist` with each intermediate distance replaced
with an upper estimate. -/
theorem dist_le_Ico_sum_of_dist_le {f : ℕ → α} {m n} (hmn : m ≤ n) {d : ℕ → ℝ}
    (hd : ∀ {k}, m ≤ k → k < n → dist (f k) (f (k + 1)) ≤ d k) :
    dist (f m) (f n) ≤ ∑ i ∈ Finset.Ico m n, d i :=
  le_trans (dist_le_Ico_sum_dist f hmn) <|
    Finset.sum_le_sum fun _k hk => hd (Finset.mem_Ico.1 hk).1 (Finset.mem_Ico.1 hk).2

/-- A version of `dist_le_range_sum_dist` with each intermediate distance replaced
with an upper estimate. -/
theorem dist_le_range_sum_of_dist_le {f : ℕ → α} (n : ℕ) {d : ℕ → ℝ}
    (hd : ∀ {k}, k < n → dist (f k) (f (k + 1)) ≤ d k) :
    dist (f 0) (f n) ≤ ∑ i ∈ Finset.range n, d i :=
  Nat.Ico_zero_eq_range ▸ dist_le_Ico_sum_of_dist_le (zero_le n) fun _ => hd

namespace Metric

-- instantiate pseudometric space as a topology

nonrec theorem isUniformInducing_iff [PseudoMetricSpace β] {f : α → β} :
    IsUniformInducing f ↔ UniformContinuous f ∧
      ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, dist (f a) (f b) < ε → dist a b < δ :=
  isUniformInducing_iff'.trans <| Iff.rfl.and <|
    ((uniformity_basis_dist.comap _).le_basis_iff uniformity_basis_dist).trans <| by
      simp only [subset_def, Prod.forall, gt_iff_lt, preimage_setOf_eq, Prod.map_apply, mem_setOf]

nonrec theorem isUniformEmbedding_iff [PseudoMetricSpace β] {f : α → β} :
    IsUniformEmbedding f ↔ Function.Injective f ∧ UniformContinuous f ∧
      ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, dist (f a) (f b) < ε → dist a b < δ := by
  rw [isUniformEmbedding_iff, and_comm, isUniformInducing_iff]

/-- If a map between pseudometric spaces is a uniform embedding then the distance between `f x`
and `f y` is controlled in terms of the distance between `x` and `y`. -/
theorem controlled_of_isUniformEmbedding [PseudoMetricSpace β] {f : α → β}
    (h : IsUniformEmbedding f) :
    (∀ ε > 0, ∃ δ > 0, ∀ {a b : α}, dist a b < δ → dist (f a) (f b) < ε) ∧
      ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, dist (f a) (f b) < ε → dist a b < δ :=
  ⟨uniformContinuous_iff.1 h.uniformContinuous, (isUniformEmbedding_iff.1 h).2.2⟩

theorem totallyBounded_iff {s : Set α} :
    TotallyBounded s ↔ ∀ ε > 0, ∃ t : Set α, t.Finite ∧ s ⊆ ⋃ y ∈ t, ball y ε :=
  uniformity_basis_dist.totallyBounded_iff

/-- A pseudometric space is totally bounded if one can reconstruct up to any ε>0 any element of the
space from finitely many data. -/
theorem totallyBounded_of_finite_discretization {s : Set α}
    (H : ∀ ε > (0 : ℝ),
        ∃ (β : Type u) (_ : Fintype β) (F : s → β), ∀ x y, F x = F y → dist (x : α) y < ε) :
    TotallyBounded s := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · rw [hs]
    exact totallyBounded_empty
  rcases hs with ⟨x0, hx0⟩
  haveI : Inhabited s := ⟨⟨x0, hx0⟩⟩
  refine totallyBounded_iff.2 fun ε ε0 => ?_
  rcases H ε ε0 with ⟨β, fβ, F, hF⟩
  let Finv := Function.invFun F
  refine ⟨range (Subtype.val ∘ Finv), finite_range _, fun x xs => ?_⟩
  let x' := Finv (F ⟨x, xs⟩)
  have : F x' = F ⟨x, xs⟩ := Function.invFun_eq ⟨⟨x, xs⟩, rfl⟩
  simp only [Set.mem_iUnion, Set.mem_range]
  exact ⟨_, ⟨F ⟨x, xs⟩, rfl⟩, hF _ _ this.symm⟩

theorem finite_approx_of_totallyBounded {s : Set α} (hs : TotallyBounded s) :
    ∀ ε > 0, ∃ t, t ⊆ s ∧ Set.Finite t ∧ s ⊆ ⋃ y ∈ t, ball y ε := by
  intro ε ε_pos
  rw [totallyBounded_iff_subset] at hs
  exact hs _ (dist_mem_uniformity ε_pos)

/-- Expressing uniform convergence using `dist` -/
theorem tendstoUniformlyOnFilter_iff {F : ι → β → α} {f : β → α} {p : Filter ι} {p' : Filter β} :
    TendstoUniformlyOnFilter F f p p' ↔
      ∀ ε > 0, ∀ᶠ n : ι × β in p ×ˢ p', dist (f n.snd) (F n.fst n.snd) < ε := by
  refine ⟨fun H ε hε => H _ (dist_mem_uniformity hε), fun H u hu => ?_⟩
  rcases mem_uniformity_dist.1 hu with ⟨ε, εpos, hε⟩
  exact (H ε εpos).mono fun n hn => hε hn

/-- Expressing locally uniform convergence on a set using `dist`. -/
theorem tendstoLocallyUniformlyOn_iff [TopologicalSpace β] {F : ι → β → α} {f : β → α}
    {p : Filter ι} {s : Set β} :
    TendstoLocallyUniformlyOn F f p s ↔
      ∀ ε > 0, ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, ∀ᶠ n in p, ∀ y ∈ t, dist (f y) (F n y) < ε := by
  refine ⟨fun H ε hε => H _ (dist_mem_uniformity hε), fun H u hu x hx => ?_⟩
  rcases mem_uniformity_dist.1 hu with ⟨ε, εpos, hε⟩
  rcases H ε εpos x hx with ⟨t, ht, Ht⟩
  exact ⟨t, ht, Ht.mono fun n hs x hx => hε (hs x hx)⟩

/-- Expressing uniform convergence on a set using `dist`. -/
theorem tendstoUniformlyOn_iff {F : ι → β → α} {f : β → α} {p : Filter ι} {s : Set β} :
    TendstoUniformlyOn F f p s ↔ ∀ ε > 0, ∀ᶠ n in p, ∀ x ∈ s, dist (f x) (F n x) < ε := by
  refine ⟨fun H ε hε => H _ (dist_mem_uniformity hε), fun H u hu => ?_⟩
  rcases mem_uniformity_dist.1 hu with ⟨ε, εpos, hε⟩
  exact (H ε εpos).mono fun n hs x hx => hε (hs x hx)

theorem tendstoUniformlyOn_of_dist_le_tendsto_zero' {α β M : Type*} [PseudoMetricSpace M]
    {u : α → ℝ}
    {F : α → β → M} {f : β → M} {s : Set β} {l : Filter α}
    (hfu : ∀ᶠ n in l, ∀ x ∈ s, dist (f x) (F n x) ≤ u n) (h : Tendsto u l (𝓝 0)) :
    TendstoUniformlyOn F f l s := by
  refine Metric.tendstoUniformlyOn_iff.2 fun ε εpos => ?_
  rw [Metric.tendsto_nhds] at h
  specialize h ε εpos
  filter_upwards [hfu, h] with x hn hu n hs
  specialize hn n hs
  rw [Real.dist_0_eq_abs, abs_of_nonneg <|le_trans dist_nonneg hn] at hu
  exact lt_of_le_of_lt hn hu

theorem tendstoUniformlyOn_of_dist_le_tendsto_zero {α β M : Type*} [PseudoMetricSpace M] {u : α → ℝ}
    {F : α → β → M} {f : β → M} {s : Set β} {l : Filter α}
    (hfu : ∀ n x, x ∈ s → dist (f x) (F n x) ≤ u n) (h : Tendsto u l (𝓝 0)) :
    TendstoUniformlyOn F f l s :=
  tendstoUniformlyOn_of_dist_le_tendsto_zero' (Eventually.of_forall hfu) h

/-- Expressing locally uniform convergence using `dist`. -/
theorem tendstoLocallyUniformly_iff [TopologicalSpace β] {F : ι → β → α} {f : β → α}
    {p : Filter ι} :
    TendstoLocallyUniformly F f p ↔
      ∀ ε > 0, ∀ x : β, ∃ t ∈ 𝓝 x, ∀ᶠ n in p, ∀ y ∈ t, dist (f y) (F n y) < ε := by
  simp only [← tendstoLocallyUniformlyOn_univ, tendstoLocallyUniformlyOn_iff, nhdsWithin_univ,
    mem_univ, forall_const]

/-- Expressing uniform convergence using `dist`. -/
theorem tendstoUniformly_iff {F : ι → β → α} {f : β → α} {p : Filter ι} :
    TendstoUniformly F f p ↔ ∀ ε > 0, ∀ᶠ n in p, ∀ x, dist (f x) (F n x) < ε := by
  rw [← tendstoUniformlyOn_univ, tendstoUniformlyOn_iff]
  simp

theorem tendstoUniformly_of_dist_le_tendsto_zero {α β M : Type*} [PseudoMetricSpace M] {u : α → ℝ}
    {F : α → β → M} {f : β → M} {l : Filter α} (hfu : ∀ n x, dist (f x) (F n x) ≤ u n)
    (h : Tendsto u l (𝓝 0)) : TendstoUniformly F f l :=
  tendstoUniformlyOn_univ.mp <|tendstoUniformlyOn_of_dist_le_tendsto_zero (fun n x _ ↦ hfu n x) h

theorem tendstoUniformly_of_dist_le_tendsto_zero' {α β M : Type*} [PseudoMetricSpace M] {u : α → ℝ}
    {F : α → β → M} {f : β → M} {l : Filter α} (hfu : ∀ᶠ n in l, ∀ x, dist (f x) (F n x) ≤ u n)
    (h : Tendsto u l (𝓝 0)) : TendstoUniformly F f l :=
  tendstoUniformlyOn_univ.mp <|tendstoUniformlyOn_of_dist_le_tendsto_zero'
    (Eventually.mono hfu (fun _ h x _ ↦ h x)) h

protected theorem cauchy_iff {f : Filter α} :
    Cauchy f ↔ NeBot f ∧ ∀ ε > 0, ∃ t ∈ f, ∀ x ∈ t, ∀ y ∈ t, dist x y < ε :=
  uniformity_basis_dist.cauchy_iff

variable {s : Set α}

/-- Given a point `x` in a discrete subset `s` of a pseudometric space, there is an open ball
centered at `x` and intersecting `s` only at `x`. -/
theorem exists_ball_inter_eq_singleton_of_mem_discrete (hs : IsDiscrete s) {x : α} (hx : x ∈ s) :
    ∃ ε > 0, Metric.ball x ε ∩ s = {x} :=
  nhds_basis_ball.exists_inter_eq_singleton_of_mem_discrete hs hx

/-- Given a point `x` in a discrete subset `s` of a pseudometric space, there is a closed ball
of positive radius centered at `x` and intersecting `s` only at `x`. -/
theorem exists_closedBall_inter_eq_singleton_of_discrete (hs : IsDiscrete s) {x : α} (hx : x ∈ s) :
    ∃ ε > 0, Metric.closedBall x ε ∩ s = {x} :=
  nhds_basis_closedBall.exists_inter_eq_singleton_of_mem_discrete hs hx

end Metric

open Metric

theorem Metric.inseparable_iff_nndist {x y : α} : Inseparable x y ↔ nndist x y = 0 := by
  rw [EMetric.inseparable_iff, edist_nndist, ENNReal.coe_eq_zero]

alias ⟨Inseparable.nndist_eq_zero, _⟩ := Metric.inseparable_iff_nndist

theorem Metric.inseparable_iff {x y : α} : Inseparable x y ↔ dist x y = 0 := by
  rw [Metric.inseparable_iff_nndist, dist_nndist, NNReal.coe_eq_zero]

alias ⟨Inseparable.dist_eq_zero, _⟩ := Metric.inseparable_iff

/-- A weaker version of `tendsto_nhds_unique` for `PseudoMetricSpace`. -/
theorem tendsto_nhds_unique_dist {f : β → α} {l : Filter β} {x y : α} [NeBot l]
    (ha : Tendsto f l (𝓝 x)) (hb : Tendsto f l (𝓝 y)) : dist x y = 0 :=
  (tendsto_nhds_unique_inseparable ha hb).dist_eq_zero

section Real

theorem cauchySeq_iff_tendsto_dist_atTop_0 [Nonempty β] [SemilatticeSup β] {u : β → α} :
    CauchySeq u ↔ Tendsto (fun n : β × β => dist (u n.1) (u n.2)) atTop (𝓝 0) := by
  rw [cauchySeq_iff_tendsto, Metric.uniformity_eq_comap_nhds_zero, tendsto_comap_iff,
    Function.comp_def]
  simp_rw [Prod.map_fst, Prod.map_snd]

end Real

namespace Topology

/-- The preimage of a separable set by an inducing map is separable. -/
protected lemma IsInducing.isSeparable_preimage {α : Type*} [TopologicalSpace α]
    [PseudoMetrizableSpace α] {f : β → α} [TopologicalSpace β]
    (hf : IsInducing f) {s : Set α} (hs : IsSeparable s) : IsSeparable (f ⁻¹' s) := by
  letI : UniformSpace α := TopologicalSpace.pseudoMetrizableSpaceUniformity α
  have := pseudoMetrizableSpaceUniformity_countably_generated
  have : SeparableSpace s := hs.separableSpace
  have : SecondCountableTopology s := UniformSpace.secondCountable_of_separable _
  have : IsInducing ((mapsTo_preimage f s).restrict _ _ _) :=
    (hf.comp IsInducing.subtypeVal).codRestrict _
  have := this.secondCountableTopology
  exact .of_subtype _

protected theorem IsEmbedding.isSeparable_preimage {α : Type*} [TopologicalSpace α]
    [PseudoMetrizableSpace α] {f : β → α} [TopologicalSpace β]
    (hf : IsEmbedding f) {s : Set α} (hs : IsSeparable s) : IsSeparable (f ⁻¹' s) :=
  hf.isInducing.isSeparable_preimage hs

end Topology

/-- A compact set is separable. -/
theorem IsCompact.isSeparable {α : Type*} [TopologicalSpace α] [PseudoMetrizableSpace α]
    {s : Set α} (hs : IsCompact s) : IsSeparable s :=
  haveI : CompactSpace s := isCompact_iff_compactSpace.mp hs
  .of_subtype s

namespace Metric

section SecondCountable

open TopologicalSpace

/-- A pseudometric space is second countable if, for every `ε > 0`, there is a countable set which
is `ε`-dense. -/
theorem secondCountable_of_almost_dense_set
    (H : ∀ ε > (0 : ℝ), ∃ s : Set α, s.Countable ∧ ∀ x, ∃ y ∈ s, dist x y ≤ ε) :
    SecondCountableTopology α := by
  refine EMetric.secondCountable_of_almost_dense_set fun ε ε0 => ?_
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 ε0 with ⟨ε', ε'0, ε'ε⟩
  choose s hsc y hys hyx using H ε' (mod_cast ε'0)
  refine ⟨s, hsc, iUnion₂_eq_univ_iff.2 fun x => ⟨y x, hys _, le_trans ?_ ε'ε.le⟩⟩
  exact mod_cast hyx x

end SecondCountable

end Metric

section Compact
variable {X : Type*} [PseudoMetricSpace X] {s : Set X} {ε : ℝ}

/-- Any compact set in a pseudometric space can be covered by finitely many balls of a given
positive radius -/
theorem finite_cover_balls_of_compact (hs : IsCompact s) {e : ℝ} (he : 0 < e) :
    ∃ t ⊆ s, t.Finite ∧ s ⊆ ⋃ x ∈ t, ball x e :=
  let ⟨t, hts, ht⟩ := hs.elim_nhds_subcover _ (fun x _ => ball_mem_nhds x he)
  ⟨t, hts, t.finite_toSet, ht⟩

alias IsCompact.finite_cover_balls := finite_cover_balls_of_compact

/-- Any relatively compact set in a pseudometric space can be covered by finitely many balls of a
given positive radius. -/
lemma exists_finite_cover_balls_of_isCompact_closure (hs : IsCompact (closure s)) (hε : 0 < ε) :
    ∃ t ⊆ s, t.Finite ∧ s ⊆ ⋃ x ∈ t, ball x ε := by
  obtain ⟨t, hst⟩ := hs.elim_finite_subcover (fun x : s ↦ ball x ε) (fun _ ↦ isOpen_ball) fun x hx ↦
    let ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx _ hε; mem_iUnion.2 ⟨⟨y, hy⟩, hxy⟩
  refine ⟨t.map ⟨Subtype.val, Subtype.val_injective⟩, by simp, Finset.finite_toSet _, ?_⟩
  simpa using subset_closure.trans hst

end Compact

/-- If a map is continuous on a separable set `s`, then the image of `s` is also separable. -/
theorem ContinuousOn.isSeparable_image {α : Type*} [TopologicalSpace α] [PseudoMetrizableSpace α]
    [TopologicalSpace β] {f : α → β} {s : Set α}
    (hf : ContinuousOn f s) (hs : IsSeparable s) : IsSeparable (f '' s) := by
  rw [image_eq_range, ← image_univ]
  exact (isSeparable_univ_iff.2 hs.separableSpace).image hf.restrict
