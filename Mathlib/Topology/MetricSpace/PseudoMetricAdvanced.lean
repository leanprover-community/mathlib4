/-
Copyright (c) 2015, 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/

import Mathlib.Topology.MetricSpace.Real
import Mathlib.Topology.Bornology.Constructions

/-! ## Further results about metric spaces

This file is a continuation of `PseudoMetric`, but with heavier imports.

TODO: add main definitions and results!

-/

open Set Filter TopologicalSpace Bornology
open scoped BigOperators ENNReal NNReal Uniformity Topology

universe u v w

variable {α : Type u} {β : Type v} {X ι : Type*}

variable [PseudoMetricSpace α]

open Metric

/-- Pseudometric space structure pulled back by a function. -/
@[reducible]
def PseudoMetricSpace.induced {α β} (f : α → β) (m : PseudoMetricSpace β) :
    PseudoMetricSpace α where
  dist x y := dist (f x) (f y)
  dist_self x := dist_self _
  dist_comm x y := dist_comm _ _
  dist_triangle x y z := dist_triangle _ _ _
  edist x y := edist (f x) (f y)
  edist_dist x y := edist_dist _ _
  toUniformSpace := UniformSpace.comap f m.toUniformSpace
  uniformity_dist := (uniformity_basis_dist.comap _).eq_biInf
  toBornology := Bornology.induced f
  cobounded_sets := Set.ext fun s => mem_comap_iff_compl.trans <| by
    simp only [← isBounded_def, isBounded_iff, ball_image_iff, mem_setOf]
#align pseudo_metric_space.induced PseudoMetricSpace.induced

/-- Pull back a pseudometric space structure by an inducing map. This is a version of
`PseudoMetricSpace.induced` useful in case if the domain already has a `TopologicalSpace`
structure. -/
def Inducing.comapPseudoMetricSpace {α β} [TopologicalSpace α] [m : PseudoMetricSpace β] {f : α → β}
    (hf : Inducing f) : PseudoMetricSpace α :=
  .replaceTopology (.induced f m) hf.induced
#align inducing.comap_pseudo_metric_space Inducing.comapPseudoMetricSpace

/-- Pull back a pseudometric space structure by a uniform inducing map. This is a version of
`PseudoMetricSpace.induced` useful in case if the domain already has a `UniformSpace`
structure. -/
def UniformInducing.comapPseudoMetricSpace {α β} [UniformSpace α] [m : PseudoMetricSpace β]
    (f : α → β) (h : UniformInducing f) : PseudoMetricSpace α :=
  .replaceUniformity (.induced f m) h.comap_uniformity.symm
#align uniform_inducing.comap_pseudo_metric_space UniformInducing.comapPseudoMetricSpace

instance Subtype.pseudoMetricSpace {p : α → Prop} : PseudoMetricSpace (Subtype p) :=
  PseudoMetricSpace.induced Subtype.val ‹_›
#align subtype.pseudo_metric_space Subtype.pseudoMetricSpace

theorem Subtype.dist_eq {p : α → Prop} (x y : Subtype p) : dist x y = dist (x : α) y :=
  rfl
#align subtype.dist_eq Subtype.dist_eq

theorem Subtype.nndist_eq {p : α → Prop} (x y : Subtype p) : nndist x y = nndist (x : α) y :=
  rfl
#align subtype.nndist_eq Subtype.nndist_eq

namespace MulOpposite

@[to_additive]
instance instPseudoMetricSpace : PseudoMetricSpace αᵐᵒᵖ :=
  PseudoMetricSpace.induced MulOpposite.unop ‹_›

@[to_additive (attr := simp)]
theorem dist_unop (x y : αᵐᵒᵖ) : dist (unop x) (unop y) = dist x y := rfl
#align mul_opposite.dist_unop MulOpposite.dist_unop
#align add_opposite.dist_unop AddOpposite.dist_unop

@[to_additive (attr := simp)]
theorem dist_op (x y : α) : dist (op x) (op y) = dist x y := rfl
#align mul_opposite.dist_op MulOpposite.dist_op
#align add_opposite.dist_op AddOpposite.dist_op

@[to_additive (attr := simp)]
theorem nndist_unop (x y : αᵐᵒᵖ) : nndist (unop x) (unop y) = nndist x y := rfl
#align mul_opposite.nndist_unop MulOpposite.nndist_unop
#align add_opposite.nndist_unop AddOpposite.nndist_unop

@[to_additive (attr := simp)]
theorem nndist_op (x y : α) : nndist (op x) (op y) = nndist x y := rfl
#align mul_opposite.nndist_op MulOpposite.nndist_op
#align add_opposite.nndist_op AddOpposite.nndist_op

end MulOpposite

section NNReal

instance : PseudoMetricSpace ℝ≥0 := Subtype.pseudoMetricSpace

theorem NNReal.dist_eq (a b : ℝ≥0) : dist a b = |(a : ℝ) - b| := rfl
#align nnreal.dist_eq NNReal.dist_eq

theorem NNReal.nndist_eq (a b : ℝ≥0) : nndist a b = max (a - b) (b - a) :=
  eq_of_forall_ge_iff fun _ => by
    simp only [max_le_iff, tsub_le_iff_right (α := ℝ≥0)]
    simp only [← NNReal.coe_le_coe, coe_nndist, dist_eq, abs_sub_le_iff,
      tsub_le_iff_right, NNReal.coe_add]
#align nnreal.nndist_eq NNReal.nndist_eq

@[simp]
theorem NNReal.nndist_zero_eq_val (z : ℝ≥0) : nndist 0 z = z := by
  simp only [NNReal.nndist_eq, max_eq_right, tsub_zero, zero_tsub, zero_le']
#align nnreal.nndist_zero_eq_val NNReal.nndist_zero_eq_val

@[simp]
theorem NNReal.nndist_zero_eq_val' (z : ℝ≥0) : nndist z 0 = z := by
  rw [nndist_comm]
  exact NNReal.nndist_zero_eq_val z
#align nnreal.nndist_zero_eq_val' NNReal.nndist_zero_eq_val'

theorem NNReal.le_add_nndist (a b : ℝ≥0) : a ≤ b + nndist a b := by
  suffices (a : ℝ) ≤ (b : ℝ) + dist a b by
    rwa [← NNReal.coe_le_coe, NNReal.coe_add, coe_nndist]
  rw [← sub_le_iff_le_add']
  exact le_of_abs_le (dist_eq a b).ge
#align nnreal.le_add_nndist NNReal.le_add_nndist

end NNReal

section ULift

variable [PseudoMetricSpace β]

instance : PseudoMetricSpace (ULift β) :=
  PseudoMetricSpace.induced ULift.down ‹_›

theorem ULift.dist_eq (x y : ULift β) : dist x y = dist x.down y.down := rfl
#align ulift.dist_eq ULift.dist_eq

theorem ULift.nndist_eq (x y : ULift β) : nndist x y = nndist x.down y.down := rfl
#align ulift.nndist_eq ULift.nndist_eq

@[simp]
theorem ULift.dist_up_up (x y : β) : dist (ULift.up x) (ULift.up y) = dist x y := rfl
#align ulift.dist_up_up ULift.dist_up_up

@[simp]
theorem ULift.nndist_up_up (x y : β) : nndist (ULift.up x) (ULift.up y) = nndist x y := rfl
#align ulift.nndist_up_up ULift.nndist_up_up

end ULift

section Prod

variable [PseudoMetricSpace β]

-- porting note: added `let`, otherwise `simp` failed
instance Prod.pseudoMetricSpaceMax : PseudoMetricSpace (α × β) :=
  let i := PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun x y : α × β => dist x.1 y.1 ⊔ dist x.2 y.2)
    (fun x y => (max_lt (edist_lt_top _ _) (edist_lt_top _ _)).ne) fun x y => by
      simp only [sup_eq_max, dist_edist, ← ENNReal.toReal_max (edist_ne_top _ _) (edist_ne_top _ _),
        Prod.edist_eq]
  i.replaceBornology fun s => by
    simp only [← isBounded_image_fst_and_snd, isBounded_iff_eventually, ball_image_iff, ←
      eventually_and, ← forall_and, ← max_le_iff]
    rfl
#align prod.pseudo_metric_space_max Prod.pseudoMetricSpaceMax

theorem Prod.dist_eq {x y : α × β} : dist x y = max (dist x.1 y.1) (dist x.2 y.2) := rfl
#align prod.dist_eq Prod.dist_eq

@[simp]
theorem dist_prod_same_left {x : α} {y₁ y₂ : β} : dist (x, y₁) (x, y₂) = dist y₁ y₂ := by
  simp [Prod.dist_eq, dist_nonneg]
#align dist_prod_same_left dist_prod_same_left

@[simp]
theorem dist_prod_same_right {x₁ x₂ : α} {y : β} : dist (x₁, y) (x₂, y) = dist x₁ x₂ := by
  simp [Prod.dist_eq, dist_nonneg]
#align dist_prod_same_right dist_prod_same_right

theorem ball_prod_same (x : α) (y : β) (r : ℝ) : ball x r ×ˢ ball y r = ball (x, y) r :=
  ext fun z => by simp [Prod.dist_eq]
#align ball_prod_same ball_prod_same

theorem closedBall_prod_same (x : α) (y : β) (r : ℝ) :
    closedBall x r ×ˢ closedBall y r = closedBall (x, y) r :=
  ext fun z => by simp [Prod.dist_eq]
#align closed_ball_prod_same closedBall_prod_same

theorem sphere_prod (x : α × β) (r : ℝ) :
    sphere x r = sphere x.1 r ×ˢ closedBall x.2 r ∪ closedBall x.1 r ×ˢ sphere x.2 r := by
  obtain hr | rfl | hr := lt_trichotomy r 0
  · simp [hr]
  · cases x
    simp_rw [← closedBall_eq_sphere_of_nonpos le_rfl, union_self, closedBall_prod_same]
  · ext ⟨x', y'⟩
    simp_rw [Set.mem_union, Set.mem_prod, Metric.mem_closedBall, Metric.mem_sphere, Prod.dist_eq,
      max_eq_iff]
    refine' or_congr (and_congr_right _) (and_comm.trans (and_congr_left _))
    all_goals rintro rfl; rfl
#align sphere_prod sphere_prod

end Prod

-- porting note: 3 new lemmas
theorem dist_dist_dist_le_left (x y z : α) : dist (dist x z) (dist y z) ≤ dist x y :=
  abs_dist_sub_le ..

theorem dist_dist_dist_le_right (x y z : α) : dist (dist x y) (dist x z) ≤ dist y z := by
  simpa only [dist_comm x] using dist_dist_dist_le_left y z x

theorem dist_dist_dist_le (x y x' y' : α) : dist (dist x y) (dist x' y') ≤ dist x x' + dist y y' :=
  (dist_triangle _ _ _).trans <|
    add_le_add (dist_dist_dist_le_left _ _ _) (dist_dist_dist_le_right _ _ _)

theorem uniformContinuous_dist : UniformContinuous fun p : α × α => dist p.1 p.2 :=
  Metric.uniformContinuous_iff.2 fun ε ε0 =>
    ⟨ε / 2, half_pos ε0, fun {a b} h =>
      calc dist (dist a.1 a.2) (dist b.1 b.2) ≤ dist a.1 b.1 + dist a.2 b.2 :=
        dist_dist_dist_le _ _ _ _
      _ ≤ dist a b + dist a b := add_le_add (le_max_left _ _) (le_max_right _ _)
      _ < ε / 2 + ε / 2 := add_lt_add h h
      _ = ε := add_halves ε⟩
#align uniform_continuous_dist uniformContinuous_dist

protected theorem UniformContinuous.dist [UniformSpace β] {f g : β → α} (hf : UniformContinuous f)
    (hg : UniformContinuous g) : UniformContinuous fun b => dist (f b) (g b) :=
  uniformContinuous_dist.comp (hf.prod_mk hg)
#align uniform_continuous.dist UniformContinuous.dist

@[continuity]
theorem continuous_dist : Continuous fun p : α × α => dist p.1 p.2 :=
  uniformContinuous_dist.continuous
#align continuous_dist continuous_dist

@[continuity]
protected theorem Continuous.dist [TopologicalSpace β] {f g : β → α} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun b => dist (f b) (g b) :=
  continuous_dist.comp (hf.prod_mk hg : _)
#align continuous.dist Continuous.dist

protected theorem Filter.Tendsto.dist {f g : β → α} {x : Filter β} {a b : α}
    (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) :
    Tendsto (fun x => dist (f x) (g x)) x (𝓝 (dist a b)) :=
  (continuous_dist.tendsto (a, b)).comp (hf.prod_mk_nhds hg)
#align filter.tendsto.dist Filter.Tendsto.dist

theorem nhds_comap_dist (a : α) : ((𝓝 (0 : ℝ)).comap (dist · a)) = 𝓝 a := by
  simp only [@nhds_eq_comap_uniformity α, Metric.uniformity_eq_comap_nhds_zero, comap_comap,
    (· ∘ ·), dist_comm]
#align nhds_comap_dist nhds_comap_dist

theorem tendsto_iff_dist_tendsto_zero {f : β → α} {x : Filter β} {a : α} :
    Tendsto f x (𝓝 a) ↔ Tendsto (fun b => dist (f b) a) x (𝓝 0) := by
  rw [← nhds_comap_dist a, tendsto_comap_iff, Function.comp_def]
#align tendsto_iff_dist_tendsto_zero tendsto_iff_dist_tendsto_zero

theorem continuous_iff_continuous_dist [TopologicalSpace β] {f : β → α} :
    Continuous f ↔ Continuous fun x : β × β => dist (f x.1) (f x.2) :=
  ⟨fun h => h.fst'.dist h.snd', fun h =>
    continuous_iff_continuousAt.2 fun _ => tendsto_iff_dist_tendsto_zero.2 <|
      (h.comp (continuous_id.prod_mk continuous_const)).tendsto' _ _ <| dist_self _⟩
#align continuous_iff_continuous_dist continuous_iff_continuous_dist

theorem uniformContinuous_nndist : UniformContinuous fun p : α × α => nndist p.1 p.2 :=
  uniformContinuous_dist.subtype_mk _
#align uniform_continuous_nndist uniformContinuous_nndist

protected theorem UniformContinuous.nndist [UniformSpace β] {f g : β → α} (hf : UniformContinuous f)
    (hg : UniformContinuous g) : UniformContinuous fun b => nndist (f b) (g b) :=
  uniformContinuous_nndist.comp (hf.prod_mk hg)
#align uniform_continuous.nndist UniformContinuous.nndist

theorem continuous_nndist : Continuous fun p : α × α => nndist p.1 p.2 :=
  uniformContinuous_nndist.continuous
#align continuous_nndist continuous_nndist

protected theorem Continuous.nndist [TopologicalSpace β] {f g : β → α} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun b => nndist (f b) (g b) :=
  continuous_nndist.comp (hf.prod_mk hg : _)
#align continuous.nndist Continuous.nndist

protected theorem Filter.Tendsto.nndist {f g : β → α} {x : Filter β} {a b : α}
    (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) :
    Tendsto (fun x => nndist (f x) (g x)) x (𝓝 (nndist a b)) :=
  (continuous_nndist.tendsto (a, b)).comp (hf.prod_mk_nhds hg)
#align filter.tendsto.nndist Filter.Tendsto.nndist

namespace Metric

variable {x y z : α} {ε ε₁ ε₂ : ℝ} {s : Set α}

theorem isClosed_ball : IsClosed (closedBall x ε) :=
  isClosed_le (continuous_id.dist continuous_const) continuous_const
#align metric.is_closed_ball Metric.isClosed_ball

theorem isClosed_sphere : IsClosed (sphere x ε) :=
  isClosed_eq (continuous_id.dist continuous_const) continuous_const
#align metric.is_closed_sphere Metric.isClosed_sphere

@[simp]
theorem closure_closedBall : closure (closedBall x ε) = closedBall x ε :=
  isClosed_ball.closure_eq
#align metric.closure_closed_ball Metric.closure_closedBall

@[simp]
theorem closure_sphere : closure (sphere x ε) = sphere x ε :=
  isClosed_sphere.closure_eq
#align metric.closure_sphere Metric.closure_sphere

theorem closure_ball_subset_closedBall : closure (ball x ε) ⊆ closedBall x ε :=
  closure_minimal ball_subset_closedBall isClosed_ball
#align metric.closure_ball_subset_closed_ball Metric.closure_ball_subset_closedBall

theorem frontier_ball_subset_sphere : frontier (ball x ε) ⊆ sphere x ε :=
  frontier_lt_subset_eq (continuous_id.dist continuous_const) continuous_const
#align metric.frontier_ball_subset_sphere Metric.frontier_ball_subset_sphere

theorem frontier_closedBall_subset_sphere : frontier (closedBall x ε) ⊆ sphere x ε :=
  frontier_le_subset_eq (continuous_id.dist continuous_const) continuous_const
#align metric.frontier_closed_ball_subset_sphere Metric.frontier_closedBall_subset_sphere

theorem ball_subset_interior_closedBall : ball x ε ⊆ interior (closedBall x ε) :=
  interior_maximal ball_subset_closedBall isOpen_ball
#align metric.ball_subset_interior_closed_ball Metric.ball_subset_interior_closedBall

/-- ε-characterization of the closure in pseudometric spaces-/
theorem mem_closure_iff {s : Set α} {a : α} : a ∈ closure s ↔ ∀ ε > 0, ∃ b ∈ s, dist a b < ε :=
  (mem_closure_iff_nhds_basis nhds_basis_ball).trans <| by simp only [mem_ball, dist_comm]
#align metric.mem_closure_iff Metric.mem_closure_iff

theorem mem_closure_range_iff {e : β → α} {a : α} :
    a ∈ closure (range e) ↔ ∀ ε > 0, ∃ k : β, dist a (e k) < ε := by
  simp only [mem_closure_iff, exists_range_iff]
#align metric.mem_closure_range_iff Metric.mem_closure_range_iff

theorem mem_closure_range_iff_nat {e : β → α} {a : α} :
    a ∈ closure (range e) ↔ ∀ n : ℕ, ∃ k : β, dist a (e k) < 1 / ((n : ℝ) + 1) :=
  (mem_closure_iff_nhds_basis nhds_basis_ball_inv_nat_succ).trans <| by
    simp only [mem_ball, dist_comm, exists_range_iff, forall_const]
#align metric.mem_closure_range_iff_nat Metric.mem_closure_range_iff_nat

theorem mem_of_closed' {s : Set α} (hs : IsClosed s) {a : α} :
    a ∈ s ↔ ∀ ε > 0, ∃ b ∈ s, dist a b < ε := by
  simpa only [hs.closure_eq] using @mem_closure_iff _ _ s a
#align metric.mem_of_closed' Metric.mem_of_closed'

theorem closedBall_zero' (x : α) : closedBall x 0 = closure {x} :=
  Subset.antisymm
    (fun _y hy =>
      mem_closure_iff.2 fun _ε ε0 => ⟨x, mem_singleton x, (mem_closedBall.1 hy).trans_lt ε0⟩)
    (closure_minimal (singleton_subset_iff.2 (dist_self x).le) isClosed_ball)
#align metric.closed_ball_zero' Metric.closedBall_zero'

lemma eventually_isCompact_closedBall [WeaklyLocallyCompactSpace α] (x : α) :
    ∀ᶠ r in 𝓝 (0 : ℝ), IsCompact (closedBall x r) := by
  rcases exists_compact_mem_nhds x with ⟨s, s_compact, hs⟩
  filter_upwards [eventually_closedBall_subset hs] with r hr
  exact IsCompact.of_isClosed_subset s_compact isClosed_ball hr

lemma exists_isCompact_closedBall [WeaklyLocallyCompactSpace α] (x : α) :
    ∃ r, 0 < r ∧ IsCompact (closedBall x r) := by
  have : ∀ᶠ r in 𝓝[>] 0, IsCompact (closedBall x r) :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_isCompact_closedBall x)
  simpa only [and_comm] using (this.and self_mem_nhdsWithin).exists

theorem dense_iff {s : Set α} : Dense s ↔ ∀ x, ∀ r > 0, (ball x r ∩ s).Nonempty :=
  forall_congr' fun x => by
    simp only [mem_closure_iff, Set.Nonempty, exists_prop, mem_inter_iff, mem_ball', and_comm]
#align metric.dense_iff Metric.dense_iff

theorem denseRange_iff {f : β → α} : DenseRange f ↔ ∀ x, ∀ r > 0, ∃ y, dist x (f y) < r :=
  forall_congr' fun x => by simp only [mem_closure_iff, exists_range_iff]
#align metric.dense_range_iff Metric.denseRange_iff

-- porting note: `TopologicalSpace.IsSeparable.separableSpace` moved to `EMetricSpace`

/-- The preimage of a separable set by an inducing map is separable. -/
protected theorem _root_.Inducing.isSeparable_preimage {f : β → α} [TopologicalSpace β]
    (hf : Inducing f) {s : Set α} (hs : IsSeparable s) : IsSeparable (f ⁻¹' s) := by
  have : SeparableSpace s := hs.separableSpace
  have : SecondCountableTopology s := UniformSpace.secondCountable_of_separable _
  have : Inducing ((mapsTo_preimage f s).restrict _ _ _) :=
    (hf.comp inducing_subtype_val).codRestrict _
  have := this.secondCountableTopology
  exact isSeparable_of_separableSpace_subtype _
#align inducing.is_separable_preimage Inducing.isSeparable_preimage

protected theorem _root_.Embedding.isSeparable_preimage {f : β → α} [TopologicalSpace β]
    (hf : Embedding f) {s : Set α} (hs : IsSeparable s) : IsSeparable (f ⁻¹' s) :=
  hf.toInducing.isSeparable_preimage hs
#align embedding.is_separable_preimage Embedding.isSeparable_preimage

/-- If a map is continuous on a separable set `s`, then the image of `s` is also separable. -/
theorem _root_.ContinuousOn.isSeparable_image [TopologicalSpace β] {f : α → β} {s : Set α}
    (hf : ContinuousOn f s) (hs : IsSeparable s) : IsSeparable (f '' s) := by
  rw [image_eq_range, ← image_univ]
  exact (isSeparable_univ_iff.2 hs.separableSpace).image hf.restrict
#align continuous_on.is_separable_image ContinuousOn.isSeparable_image

end Metric

/-- A compact set is separable. -/
theorem IsCompact.isSeparable {s : Set α} (hs : IsCompact s) : IsSeparable s :=
  haveI : CompactSpace s := isCompact_iff_compactSpace.mp hs
  isSeparable_of_separableSpace_subtype s
#align is_compact.is_separable IsCompact.isSeparable

section Pi

open Finset

variable {π : β → Type*} [Fintype β] [∀ b, PseudoMetricSpace (π b)]

/-- A finite product of pseudometric spaces is a pseudometric space, with the sup distance. -/
instance pseudoMetricSpacePi : PseudoMetricSpace (∀ b, π b) := by
  /- we construct the instance from the pseudoemetric space instance to avoid checking again that
    the uniformity is the same as the product uniformity, but we register nevertheless a nice
    formula for the distance -/
  let i := PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun f g : ∀ b, π b => ((sup univ fun b => nndist (f b) (g b) : ℝ≥0) : ℝ))
    (fun f g => ((Finset.sup_lt_iff bot_lt_top).2 fun b _ => edist_lt_top _ _).ne)
    (fun f g => by
      simp only [edist_pi_def, edist_nndist, ← ENNReal.coe_finset_sup, ENNReal.coe_toReal])
  refine i.replaceBornology fun s => ?_
  simp only [← isBounded_def, isBounded_iff_eventually, ← forall_isBounded_image_eval_iff,
    ball_image_iff, ← Filter.eventually_all, Function.eval_apply, @dist_nndist (π _)]
  refine' eventually_congr ((eventually_ge_atTop 0).mono fun C hC => _)
  lift C to ℝ≥0 using hC
  refine' ⟨fun H x hx y hy => NNReal.coe_le_coe.2 <| Finset.sup_le fun b _ => H b x hx y hy,
    fun H b x hx y hy => NNReal.coe_le_coe.2 _⟩
  simpa only using Finset.sup_le_iff.1 (NNReal.coe_le_coe.1 <| H hx hy) b (Finset.mem_univ b)
#align pseudo_metric_space_pi pseudoMetricSpacePi

theorem nndist_pi_def (f g : ∀ b, π b) : nndist f g = sup univ fun b => nndist (f b) (g b) :=
  NNReal.eq rfl
#align nndist_pi_def nndist_pi_def

theorem dist_pi_def (f g : ∀ b, π b) : dist f g = (sup univ fun b => nndist (f b) (g b) : ℝ≥0) :=
  rfl
#align dist_pi_def dist_pi_def

theorem nndist_pi_le_iff {f g : ∀ b, π b} {r : ℝ≥0} :
    nndist f g ≤ r ↔ ∀ b, nndist (f b) (g b) ≤ r := by simp [nndist_pi_def]
#align nndist_pi_le_iff nndist_pi_le_iff

theorem nndist_pi_lt_iff {f g : ∀ b, π b} {r : ℝ≥0} (hr : 0 < r) :
    nndist f g < r ↔ ∀ b, nndist (f b) (g b) < r := by
  rw [← bot_eq_zero'] at hr
  simp [nndist_pi_def, Finset.sup_lt_iff hr]
#align nndist_pi_lt_iff nndist_pi_lt_iff

theorem nndist_pi_eq_iff {f g : ∀ b, π b} {r : ℝ≥0} (hr : 0 < r) :
    nndist f g = r ↔ (∃ i, nndist (f i) (g i) = r) ∧ ∀ b, nndist (f b) (g b) ≤ r := by
  rw [eq_iff_le_not_lt, nndist_pi_lt_iff hr, nndist_pi_le_iff, not_forall, and_comm]
  simp_rw [not_lt, and_congr_left_iff, le_antisymm_iff]
  intro h
  refine' exists_congr fun b => _
  apply (and_iff_right <| h _).symm
#align nndist_pi_eq_iff nndist_pi_eq_iff

theorem dist_pi_lt_iff {f g : ∀ b, π b} {r : ℝ} (hr : 0 < r) :
    dist f g < r ↔ ∀ b, dist (f b) (g b) < r := by
  lift r to ℝ≥0 using hr.le
  exact nndist_pi_lt_iff hr
#align dist_pi_lt_iff dist_pi_lt_iff

theorem dist_pi_le_iff {f g : ∀ b, π b} {r : ℝ} (hr : 0 ≤ r) :
    dist f g ≤ r ↔ ∀ b, dist (f b) (g b) ≤ r := by
  lift r to ℝ≥0 using hr
  exact nndist_pi_le_iff
#align dist_pi_le_iff dist_pi_le_iff

theorem dist_pi_eq_iff {f g : ∀ b, π b} {r : ℝ} (hr : 0 < r) :
    dist f g = r ↔ (∃ i, dist (f i) (g i) = r) ∧ ∀ b, dist (f b) (g b) ≤ r := by
  lift r to ℝ≥0 using hr.le
  simp_rw [← coe_nndist, NNReal.coe_eq, nndist_pi_eq_iff hr, NNReal.coe_le_coe]
#align dist_pi_eq_iff dist_pi_eq_iff

theorem dist_pi_le_iff' [Nonempty β] {f g : ∀ b, π b} {r : ℝ} :
    dist f g ≤ r ↔ ∀ b, dist (f b) (g b) ≤ r := by
  by_cases hr : 0 ≤ r
  · exact dist_pi_le_iff hr
  · exact iff_of_false (fun h => hr <| dist_nonneg.trans h) fun h =>
      hr <| dist_nonneg.trans <| h <| Classical.arbitrary _
#align dist_pi_le_iff' dist_pi_le_iff'

theorem dist_pi_const_le (a b : α) : (dist (fun _ : β => a) fun _ => b) ≤ dist a b :=
  (dist_pi_le_iff dist_nonneg).2 fun _ => le_rfl
#align dist_pi_const_le dist_pi_const_le

theorem nndist_pi_const_le (a b : α) : (nndist (fun _ : β => a) fun _ => b) ≤ nndist a b :=
  nndist_pi_le_iff.2 fun _ => le_rfl
#align nndist_pi_const_le nndist_pi_const_le

@[simp]
theorem dist_pi_const [Nonempty β] (a b : α) : (dist (fun _ : β => a) fun _ => b) = dist a b := by
  simpa only [dist_edist] using congr_arg ENNReal.toReal (edist_pi_const a b)
#align dist_pi_const dist_pi_const

@[simp]
theorem nndist_pi_const [Nonempty β] (a b : α) :
    (nndist (fun _ : β => a) fun _ => b) = nndist a b :=
  NNReal.eq <| dist_pi_const a b
#align nndist_pi_const nndist_pi_const

theorem nndist_le_pi_nndist (f g : ∀ b, π b) (b : β) : nndist (f b) (g b) ≤ nndist f g := by
  rw [← ENNReal.coe_le_coe, ← edist_nndist, ← edist_nndist]
  exact edist_le_pi_edist f g b
#align nndist_le_pi_nndist nndist_le_pi_nndist

theorem dist_le_pi_dist (f g : ∀ b, π b) (b : β) : dist (f b) (g b) ≤ dist f g := by
  simp only [dist_nndist, NNReal.coe_le_coe, nndist_le_pi_nndist f g b]
#align dist_le_pi_dist dist_le_pi_dist

/-- An open ball in a product space is a product of open balls. See also `ball_pi'`
for a version assuming `Nonempty β` instead of `0 < r`. -/
theorem ball_pi (x : ∀ b, π b) {r : ℝ} (hr : 0 < r) :
    ball x r = Set.pi univ fun b => ball (x b) r := by
  ext p
  simp [dist_pi_lt_iff hr]
#align ball_pi ball_pi

/-- An open ball in a product space is a product of open balls. See also `ball_pi`
for a version assuming `0 < r` instead of `Nonempty β`. -/
theorem ball_pi' [Nonempty β] (x : ∀ b, π b) (r : ℝ) :
    ball x r = Set.pi univ fun b => ball (x b) r :=
  (lt_or_le 0 r).elim (ball_pi x) fun hr => by simp [ball_eq_empty.2 hr]
#align ball_pi' ball_pi'

/-- A closed ball in a product space is a product of closed balls. See also `closedBall_pi'`
for a version assuming `Nonempty β` instead of `0 ≤ r`. -/
theorem closedBall_pi (x : ∀ b, π b) {r : ℝ} (hr : 0 ≤ r) :
    closedBall x r = Set.pi univ fun b => closedBall (x b) r := by
  ext p
  simp [dist_pi_le_iff hr]
#align closed_ball_pi closedBall_pi

/-- A closed ball in a product space is a product of closed balls. See also `closedBall_pi`
for a version assuming `0 ≤ r` instead of `Nonempty β`. -/
theorem closedBall_pi' [Nonempty β] (x : ∀ b, π b) (r : ℝ) :
    closedBall x r = Set.pi univ fun b => closedBall (x b) r :=
  (le_or_lt 0 r).elim (closedBall_pi x) fun hr => by simp [closedBall_eq_empty.2 hr]
#align closed_ball_pi' closedBall_pi'

/-- A sphere in a product space is a union of spheres on each component restricted to the closed
ball. -/
theorem sphere_pi (x : ∀ b, π b) {r : ℝ} (h : 0 < r ∨ Nonempty β) :
    sphere x r = (⋃ i : β, Function.eval i ⁻¹' sphere (x i) r) ∩ closedBall x r := by
  obtain hr | rfl | hr := lt_trichotomy r 0
  · simp [hr]
  · rw [closedBall_eq_sphere_of_nonpos le_rfl, eq_comm, Set.inter_eq_right]
    letI := h.resolve_left (lt_irrefl _)
    inhabit β
    refine' subset_iUnion_of_subset default _
    intro x hx
    replace hx := hx.le
    rw [dist_pi_le_iff le_rfl] at hx
    exact le_antisymm (hx default) dist_nonneg
  · ext
    simp [dist_pi_eq_iff hr, dist_pi_le_iff hr.le]
#align sphere_pi sphere_pi

@[simp]
theorem Fin.nndist_insertNth_insertNth {n : ℕ} {α : Fin (n + 1) → Type*}
    [∀ i, PseudoMetricSpace (α i)] (i : Fin (n + 1)) (x y : α i) (f g : ∀ j, α (i.succAbove j)) :
    nndist (i.insertNth x f) (i.insertNth y g) = max (nndist x y) (nndist f g) :=
  eq_of_forall_ge_iff fun c => by simp [nndist_pi_le_iff, i.forall_iff_succAbove]
#align fin.nndist_insert_nth_insert_nth Fin.nndist_insertNth_insertNth

@[simp]
theorem Fin.dist_insertNth_insertNth {n : ℕ} {α : Fin (n + 1) → Type*}
    [∀ i, PseudoMetricSpace (α i)] (i : Fin (n + 1)) (x y : α i) (f g : ∀ j, α (i.succAbove j)) :
    dist (i.insertNth x f) (i.insertNth y g) = max (dist x y) (dist f g) := by
  simp only [dist_nndist, Fin.nndist_insertNth_insertNth, NNReal.coe_max]
#align fin.dist_insert_nth_insert_nth Fin.dist_insertNth_insertNth

theorem Real.dist_le_of_mem_pi_Icc {x y x' y' : β → ℝ} (hx : x ∈ Icc x' y') (hy : y ∈ Icc x' y') :
    dist x y ≤ dist x' y' := by
  refine' (dist_pi_le_iff dist_nonneg).2 fun b =>
    (Real.dist_le_of_mem_uIcc _ _).trans (dist_le_pi_dist x' y' b) <;> refine' Icc_subset_uIcc _
  exacts [⟨hx.1 _, hx.2 _⟩, ⟨hy.1 _, hy.2 _⟩]
#align real.dist_le_of_mem_pi_Icc Real.dist_le_of_mem_pi_Icc

end Pi

section Compact

/-- Any compact set in a pseudometric space can be covered by finitely many balls of a given
positive radius -/
theorem finite_cover_balls_of_compact {α : Type u} [PseudoMetricSpace α] {s : Set α}
    (hs : IsCompact s) {e : ℝ} (he : 0 < e) :
    ∃ t, t ⊆ s ∧ Set.Finite t ∧ s ⊆ ⋃ x ∈ t, ball x e :=
  let ⟨t, hts, ht⟩ := hs.elim_nhds_subcover _ (fun x _ => ball_mem_nhds x he)
  ⟨t, hts, t.finite_toSet, ht⟩
#align finite_cover_balls_of_compact finite_cover_balls_of_compact

alias IsCompact.finite_cover_balls := finite_cover_balls_of_compact
#align is_compact.finite_cover_balls IsCompact.finite_cover_balls

end Compact

namespace Metric

section SecondCountable

open TopologicalSpace

/-- A pseudometric space is second countable if, for every `ε > 0`, there is a countable set which
is `ε`-dense. -/
theorem secondCountable_of_almost_dense_set
    (H : ∀ ε > (0 : ℝ), ∃ s : Set α, s.Countable ∧ ∀ x, ∃ y ∈ s, dist x y ≤ ε) :
    SecondCountableTopology α := by
  refine' EMetric.secondCountable_of_almost_dense_set fun ε ε0 => _
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 ε0 with ⟨ε', ε'0, ε'ε⟩
  choose s hsc y hys hyx using H ε' (mod_cast ε'0)
  refine' ⟨s, hsc, iUnion₂_eq_univ_iff.2 fun x => ⟨y x, hys _, le_trans _ ε'ε.le⟩⟩
  exact mod_cast hyx x
#align metric.second_countable_of_almost_dense_set Metric.secondCountable_of_almost_dense_set

end SecondCountable

end Metric

theorem lebesgue_number_lemma_of_metric {s : Set α} {ι : Sort*} {c : ι → Set α} (hs : IsCompact s)
    (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : s ⊆ ⋃ i, c i) : ∃ δ > 0, ∀ x ∈ s, ∃ i, ball x δ ⊆ c i :=
  let ⟨_n, en, hn⟩ := lebesgue_number_lemma hs hc₁ hc₂
  let ⟨δ, δ0, hδ⟩ := mem_uniformity_dist.1 en
  ⟨δ, δ0, fun x hx => let ⟨i, hi⟩ := hn x hx; ⟨i, fun _y hy => hi (hδ (mem_ball'.mp hy))⟩⟩
#align lebesgue_number_lemma_of_metric lebesgue_number_lemma_of_metric

theorem lebesgue_number_lemma_of_metric_sUnion {s : Set α} {c : Set (Set α)} (hs : IsCompact s)
    (hc₁ : ∀ t ∈ c, IsOpen t) (hc₂ : s ⊆ ⋃₀ c) : ∃ δ > 0, ∀ x ∈ s, ∃ t ∈ c, ball x δ ⊆ t := by
  rw [sUnion_eq_iUnion] at hc₂; simpa using lebesgue_number_lemma_of_metric hs (by simpa) hc₂
#align lebesgue_number_lemma_of_metric_sUnion lebesgue_number_lemma_of_metric_sUnion
