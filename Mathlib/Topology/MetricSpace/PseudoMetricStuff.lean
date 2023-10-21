/-
Copyright (c) 2015, 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
import Mathlib.Topology.MetricSpace.PseudoMetric

/-!
TODO: this is a placeholder file, to be split/combined further with PseudoMetric!

TODO: insert proper docstring, once I've figured out the right split!
-/

-- TODO: go over copyright, author, imports, variables etc.

open Set Filter TopologicalSpace Bornology
open scoped BigOperators ENNReal NNReal Uniformity Topology

universe u v w

variable {α : Type u} {β : Type v} {X ι : Type*}
variable [PseudoMetricSpace α]

namespace Metric
variable {x y z : α} {δ ε ε₁ ε₂ : ℝ} {s : Set α}

protected theorem cauchy_iff {f : Filter α} :
    Cauchy f ↔ NeBot f ∧ ∀ ε > 0, ∃ t ∈ f, ∀ x ∈ t, ∀ y ∈ t, dist x y < ε :=
  uniformity_basis_dist.cauchy_iff
#align metric.cauchy_iff Metric.cauchy_iff

theorem nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x) :=
  nhds_basis_uniformity uniformity_basis_dist
#align metric.nhds_basis_ball Metric.nhds_basis_ball

theorem mem_nhds_iff : s ∈ 𝓝 x ↔ ∃ ε > 0, ball x ε ⊆ s :=
  nhds_basis_ball.mem_iff
#align metric.mem_nhds_iff Metric.mem_nhds_iff

theorem eventually_nhds_iff {p : α → Prop} :
    (∀ᶠ y in 𝓝 x, p y) ↔ ∃ ε > 0, ∀ ⦃y⦄, dist y x < ε → p y :=
  mem_nhds_iff
#align metric.eventually_nhds_iff Metric.eventually_nhds_iff

theorem eventually_nhds_iff_ball {p : α → Prop} :
    (∀ᶠ y in 𝓝 x, p y) ↔ ∃ ε > 0, ∀ y ∈ ball x ε, p y :=
  mem_nhds_iff
#align metric.eventually_nhds_iff_ball Metric.eventually_nhds_iff_ball

/-- A version of `Filter.eventually_prod_iff` where the first filter consists of neighborhoods
in a pseudo-metric space.-/
theorem eventually_nhds_prod_iff {f : Filter ι} {x₀ : α} {p : α × ι → Prop} :
    (∀ᶠ x in 𝓝 x₀ ×ˢ f, p x) ↔ ∃ ε > (0 : ℝ), ∃ pa : ι → Prop, (∀ᶠ i in f, pa i) ∧
      ∀ {x}, dist x x₀ < ε → ∀ {i}, pa i → p (x, i) := by
  refine (nhds_basis_ball.prod f.basis_sets).eventually_iff.trans ?_
  simp only [Prod.exists, forall_prod_set, id, mem_ball, and_assoc, exists_and_left, and_imp]
  rfl
#align metric.eventually_nhds_prod_iff Metric.eventually_nhds_prod_iff

/-- A version of `Filter.eventually_prod_iff` where the second filter consists of neighborhoods
in a pseudo-metric space.-/
theorem eventually_prod_nhds_iff {f : Filter ι} {x₀ : α} {p : ι × α → Prop} :
    (∀ᶠ x in f ×ˢ 𝓝 x₀, p x) ↔ ∃ pa : ι → Prop, (∀ᶠ i in f, pa i) ∧
      ∃ ε > 0, ∀ {i}, pa i → ∀ {x}, dist x x₀ < ε → p (i, x) := by
  rw [eventually_swap_iff, Metric.eventually_nhds_prod_iff]
  constructor <;>
    · rintro ⟨a1, a2, a3, a4, a5⟩
      exact ⟨a3, a4, a1, a2, fun b1 b2 b3 => a5 b3 b1⟩
#align metric.eventually_prod_nhds_iff Metric.eventually_prod_nhds_iff

theorem nhds_basis_closedBall : (𝓝 x).HasBasis (fun ε : ℝ => 0 < ε) (closedBall x) :=
  nhds_basis_uniformity uniformity_basis_dist_le
#align metric.nhds_basis_closed_ball Metric.nhds_basis_closedBall

theorem nhds_basis_ball_inv_nat_succ :
    (𝓝 x).HasBasis (fun _ => True) fun n : ℕ => ball x (1 / (↑n + 1)) :=
  nhds_basis_uniformity uniformity_basis_dist_inv_nat_succ
#align metric.nhds_basis_ball_inv_nat_succ Metric.nhds_basis_ball_inv_nat_succ

theorem nhds_basis_ball_inv_nat_pos :
    (𝓝 x).HasBasis (fun n => 0 < n) fun n : ℕ => ball x (1 / ↑n) :=
  nhds_basis_uniformity uniformity_basis_dist_inv_nat_pos
#align metric.nhds_basis_ball_inv_nat_pos Metric.nhds_basis_ball_inv_nat_pos

theorem nhds_basis_ball_pow {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
    (𝓝 x).HasBasis (fun _ => True) fun n : ℕ => ball x (r ^ n) :=
  nhds_basis_uniformity (uniformity_basis_dist_pow h0 h1)
#align metric.nhds_basis_ball_pow Metric.nhds_basis_ball_pow

theorem nhds_basis_closedBall_pow {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
    (𝓝 x).HasBasis (fun _ => True) fun n : ℕ => closedBall x (r ^ n) :=
  nhds_basis_uniformity (uniformity_basis_dist_le_pow h0 h1)
#align metric.nhds_basis_closed_ball_pow Metric.nhds_basis_closedBall_pow

theorem isOpen_iff : IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ball x ε ⊆ s := by
  simp only [isOpen_iff_mem_nhds, mem_nhds_iff]
#align metric.is_open_iff Metric.isOpen_iff

theorem isOpen_ball : IsOpen (ball x ε) :=
  isOpen_iff.2 fun _ => exists_ball_subset_ball
#align metric.is_open_ball Metric.isOpen_ball

theorem ball_mem_nhds (x : α) {ε : ℝ} (ε0 : 0 < ε) : ball x ε ∈ 𝓝 x :=
  isOpen_ball.mem_nhds (mem_ball_self ε0)
#align metric.ball_mem_nhds Metric.ball_mem_nhds

theorem closedBall_mem_nhds (x : α) {ε : ℝ} (ε0 : 0 < ε) : closedBall x ε ∈ 𝓝 x :=
  mem_of_superset (ball_mem_nhds x ε0) ball_subset_closedBall
#align metric.closed_ball_mem_nhds Metric.closedBall_mem_nhds

theorem closedBall_mem_nhds_of_mem {x c : α} {ε : ℝ} (h : x ∈ ball c ε) : closedBall c ε ∈ 𝓝 x :=
  mem_of_superset (isOpen_ball.mem_nhds h) ball_subset_closedBall
#align metric.closed_ball_mem_nhds_of_mem Metric.closedBall_mem_nhds_of_mem

theorem nhdsWithin_basis_ball {s : Set α} :
    (𝓝[s] x).HasBasis (fun ε : ℝ => 0 < ε) fun ε => ball x ε ∩ s :=
  nhdsWithin_hasBasis nhds_basis_ball s
#align metric.nhds_within_basis_ball Metric.nhdsWithin_basis_ball

theorem mem_nhdsWithin_iff {t : Set α} : s ∈ 𝓝[t] x ↔ ∃ ε > 0, ball x ε ∩ t ⊆ s :=
  nhdsWithin_basis_ball.mem_iff
#align metric.mem_nhds_within_iff Metric.mem_nhdsWithin_iff

theorem tendsto_nhdsWithin_nhdsWithin [PseudoMetricSpace β] {t : Set β} {f : α → β} {a b} :
    Tendsto f (𝓝[s] a) (𝓝[t] b) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ {x : α}, x ∈ s → dist x a < δ → f x ∈ t ∧ dist (f x) b < ε :=
  (nhdsWithin_basis_ball.tendsto_iff nhdsWithin_basis_ball).trans <| by
    simp only [inter_comm _ s, inter_comm _ t, mem_inter_iff, and_imp]; rfl
#align metric.tendsto_nhds_within_nhds_within Metric.tendsto_nhdsWithin_nhdsWithin

theorem tendsto_nhdsWithin_nhds [PseudoMetricSpace β] {f : α → β} {a b} :
    Tendsto f (𝓝[s] a) (𝓝 b) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ {x : α}, x ∈ s → dist x a < δ → dist (f x) b < ε := by
  rw [← nhdsWithin_univ b, tendsto_nhdsWithin_nhdsWithin]
  simp only [mem_univ, true_and_iff]
#align metric.tendsto_nhds_within_nhds Metric.tendsto_nhdsWithin_nhds

theorem tendsto_nhds_nhds [PseudoMetricSpace β] {f : α → β} {a b} :
    Tendsto f (𝓝 a) (𝓝 b) ↔ ∀ ε > 0, ∃ δ > 0, ∀ {x : α}, dist x a < δ → dist (f x) b < ε :=
  nhds_basis_ball.tendsto_iff nhds_basis_ball
#align metric.tendsto_nhds_nhds Metric.tendsto_nhds_nhds

theorem continuousAt_iff [PseudoMetricSpace β] {f : α → β} {a : α} :
    ContinuousAt f a ↔ ∀ ε > 0, ∃ δ > 0, ∀ {x : α}, dist x a < δ → dist (f x) (f a) < ε := by
  rw [ContinuousAt, tendsto_nhds_nhds]
#align metric.continuous_at_iff Metric.continuousAt_iff

theorem continuousWithinAt_iff [PseudoMetricSpace β] {f : α → β} {a : α} {s : Set α} :
    ContinuousWithinAt f s a ↔
      ∀ ε > 0, ∃ δ > 0, ∀ {x : α}, x ∈ s → dist x a < δ → dist (f x) (f a) < ε :=
  by rw [ContinuousWithinAt, tendsto_nhdsWithin_nhds]
#align metric.continuous_within_at_iff Metric.continuousWithinAt_iff

theorem continuousOn_iff [PseudoMetricSpace β] {f : α → β} {s : Set α} :
    ContinuousOn f s ↔ ∀ b ∈ s, ∀ ε > 0, ∃ δ > 0, ∀ a ∈ s, dist a b < δ → dist (f a) (f b) < ε := by
  simp [ContinuousOn, continuousWithinAt_iff]
#align metric.continuous_on_iff Metric.continuousOn_iff

theorem continuous_iff [PseudoMetricSpace β] {f : α → β} :
    Continuous f ↔ ∀ b, ∀ ε > 0, ∃ δ > 0, ∀ a, dist a b < δ → dist (f a) (f b) < ε :=
  continuous_iff_continuousAt.trans <| forall_congr' fun _ => tendsto_nhds_nhds
#align metric.continuous_iff Metric.continuous_iff

theorem tendsto_nhds {f : Filter β} {u : β → α} {a : α} :
    Tendsto u f (𝓝 a) ↔ ∀ ε > 0, ∀ᶠ x in f, dist (u x) a < ε :=
  nhds_basis_ball.tendsto_right_iff
#align metric.tendsto_nhds Metric.tendsto_nhds

theorem continuousAt_iff' [TopologicalSpace β] {f : β → α} {b : β} :
    ContinuousAt f b ↔ ∀ ε > 0, ∀ᶠ x in 𝓝 b, dist (f x) (f b) < ε := by
  rw [ContinuousAt, tendsto_nhds]
#align metric.continuous_at_iff' Metric.continuousAt_iff'

theorem continuousWithinAt_iff' [TopologicalSpace β] {f : β → α} {b : β} {s : Set β} :
    ContinuousWithinAt f s b ↔ ∀ ε > 0, ∀ᶠ x in 𝓝[s] b, dist (f x) (f b) < ε := by
  rw [ContinuousWithinAt, tendsto_nhds]
#align metric.continuous_within_at_iff' Metric.continuousWithinAt_iff'

theorem continuousOn_iff' [TopologicalSpace β] {f : β → α} {s : Set β} :
    ContinuousOn f s ↔ ∀ b ∈ s, ∀ ε > 0, ∀ᶠ x in 𝓝[s] b, dist (f x) (f b) < ε := by
  simp [ContinuousOn, continuousWithinAt_iff']
#align metric.continuous_on_iff' Metric.continuousOn_iff'

theorem continuous_iff' [TopologicalSpace β] {f : β → α} :
    Continuous f ↔ ∀ (a), ∀ ε > 0, ∀ᶠ x in 𝓝 a, dist (f x) (f a) < ε :=
  continuous_iff_continuousAt.trans <| forall_congr' fun _ => tendsto_nhds
#align metric.continuous_iff' Metric.continuous_iff'

theorem tendsto_atTop [Nonempty β] [SemilatticeSup β] {u : β → α} {a : α} :
    Tendsto u atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε :=
  (atTop_basis.tendsto_iff nhds_basis_ball).trans <| by
    simp only [true_and]; rfl
#align metric.tendsto_at_top Metric.tendsto_atTop

/-- A variant of `tendsto_atTop` that
uses `∃ N, ∀ n > N, ...` rather than `∃ N, ∀ n ≥ N, ...`
-/
theorem tendsto_atTop' [Nonempty β] [SemilatticeSup β] [NoMaxOrder β] {u : β → α} {a : α} :
    Tendsto u atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n > N, dist (u n) a < ε :=
  (atTop_basis_Ioi.tendsto_iff nhds_basis_ball).trans <| by
    simp only [true_and, gt_iff_lt, mem_Ioi, mem_ball]
#align metric.tendsto_at_top' Metric.tendsto_atTop'

theorem isOpen_singleton_iff {α : Type*} [PseudoMetricSpace α] {x : α} :
    IsOpen ({x} : Set α) ↔ ∃ ε > 0, ∀ y, dist y x < ε → y = x := by
  simp [isOpen_iff, subset_singleton_iff, mem_ball]
#align metric.is_open_singleton_iff Metric.isOpen_singleton_iff

/-- Given a point `x` in a discrete subset `s` of a pseudometric space, there is an open ball
centered at `x` and intersecting `s` only at `x`. -/
theorem exists_ball_inter_eq_singleton_of_mem_discrete [DiscreteTopology s] {x : α} (hx : x ∈ s) :
    ∃ ε > 0, Metric.ball x ε ∩ s = {x} :=
  nhds_basis_ball.exists_inter_eq_singleton_of_mem_discrete hx
#align metric.exists_ball_inter_eq_singleton_of_mem_discrete Metric.exists_ball_inter_eq_singleton_of_mem_discrete

/-- Given a point `x` in a discrete subset `s` of a pseudometric space, there is a closed ball
of positive radius centered at `x` and intersecting `s` only at `x`. -/
theorem exists_closedBall_inter_eq_singleton_of_discrete [DiscreteTopology s] {x : α} (hx : x ∈ s) :
    ∃ ε > 0, Metric.closedBall x ε ∩ s = {x} :=
  nhds_basis_closedBall.exists_inter_eq_singleton_of_mem_discrete hx
#align metric.exists_closed_ball_inter_eq_singleton_of_discrete Metric.exists_closedBall_inter_eq_singleton_of_discrete

theorem _root_.Dense.exists_dist_lt {s : Set α} (hs : Dense s) (x : α) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ s, dist x y < ε := by
  have : (ball x ε).Nonempty := by simp [hε]
  simpa only [mem_ball'] using hs.exists_mem_open isOpen_ball this
#align dense.exists_dist_lt Dense.exists_dist_lt

nonrec theorem _root_.DenseRange.exists_dist_lt {β : Type*} {f : β → α} (hf : DenseRange f) (x : α)
    {ε : ℝ} (hε : 0 < ε) : ∃ y, dist x (f y) < ε :=
  exists_range_iff.1 (hf.exists_dist_lt x hε)
#align dense_range.exists_dist_lt DenseRange.exists_dist_lt

end Metric

open Metric

/-Instantiate a pseudometric space as a pseudoemetric space. Before we can state the instance,
we need to show that the uniform structure coming from the edistance and the
distance coincide. -/

-- porting note: new
theorem Metric.uniformity_edist_aux {α} (d : α → α → ℝ≥0) :
    ⨅ ε > (0 : ℝ), 𝓟 { p : α × α | ↑(d p.1 p.2) < ε } =
      ⨅ ε > (0 : ℝ≥0∞), 𝓟 { p : α × α | ↑(d p.1 p.2) < ε } := by
  simp only [le_antisymm_iff, le_iInf_iff, le_principal_iff]
  refine ⟨fun ε hε => ?_, fun ε hε => ?_⟩
  · rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hε with ⟨ε', ε'0, ε'ε⟩
    refine mem_iInf_of_mem (ε' : ℝ) (mem_iInf_of_mem (ENNReal.coe_pos.1 ε'0) ?_)
    exact fun x hx => lt_trans (ENNReal.coe_lt_coe.2 hx) ε'ε
  · lift ε to ℝ≥0 using le_of_lt hε
    refine mem_iInf_of_mem (ε : ℝ≥0∞) (mem_iInf_of_mem (ENNReal.coe_pos.2 hε) ?_)
    exact fun _ => ENNReal.coe_lt_coe.1

theorem Metric.uniformity_edist : 𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α | edist p.1 p.2 < ε } := by
  simp only [PseudoMetricSpace.uniformity_dist, dist_nndist, edist_nndist,
    Metric.uniformity_edist_aux]
#align metric.uniformity_edist Metric.uniformity_edist

-- see Note [lower instance priority]
/-- A pseudometric space induces a pseudoemetric space -/
instance (priority := 100) PseudoMetricSpace.toPseudoEMetricSpace : PseudoEMetricSpace α :=
  { ‹PseudoMetricSpace α› with
    edist_self := by simp [edist_dist]
    edist_comm := fun _ _ => by simp only [edist_dist, dist_comm]
    edist_triangle := fun x y z => by
      simp only [edist_dist, ← ENNReal.ofReal_add, dist_nonneg]
      rw [ENNReal.ofReal_le_ofReal_iff _]
      · exact dist_triangle _ _ _
      · simpa using add_le_add (dist_nonneg : 0 ≤ dist x y) dist_nonneg
    uniformity_edist := Metric.uniformity_edist }
#align pseudo_metric_space.to_pseudo_emetric_space PseudoMetricSpace.toPseudoEMetricSpace

/-- Expressing the uniformity in terms of `edist` -/
@[deprecated _root_.uniformity_basis_edist]
protected theorem Metric.uniformity_basis_edist :
    (𝓤 α).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) fun ε => { p | edist p.1 p.2 < ε } :=
  uniformity_basis_edist
#align pseudo_metric.uniformity_basis_edist Metric.uniformity_basis_edist

/-- In a pseudometric space, an open ball of infinite radius is the whole space -/
theorem Metric.eball_top_eq_univ (x : α) : EMetric.ball x ∞ = Set.univ :=
  Set.eq_univ_iff_forall.mpr fun y => edist_lt_top y x
#align metric.eball_top_eq_univ Metric.eball_top_eq_univ

/-- Balls defined using the distance or the edistance coincide -/
@[simp]
theorem Metric.emetric_ball {x : α} {ε : ℝ} : EMetric.ball x (ENNReal.ofReal ε) = ball x ε := by
  ext y
  simp only [EMetric.mem_ball, mem_ball, edist_dist]
  exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg
#align metric.emetric_ball Metric.emetric_ball

/-- Balls defined using the distance or the edistance coincide -/
@[simp]
theorem Metric.emetric_ball_nnreal {x : α} {ε : ℝ≥0} : EMetric.ball x ε = ball x ε := by
  rw [← Metric.emetric_ball]
  simp
#align metric.emetric_ball_nnreal Metric.emetric_ball_nnreal

/-- Closed balls defined using the distance or the edistance coincide -/
theorem Metric.emetric_closedBall {x : α} {ε : ℝ} (h : 0 ≤ ε) :
    EMetric.closedBall x (ENNReal.ofReal ε) = closedBall x ε := by
  ext y; simp [edist_le_ofReal h]
#align metric.emetric_closed_ball Metric.emetric_closedBall

/-- Closed balls defined using the distance or the edistance coincide -/
@[simp]
theorem Metric.emetric_closedBall_nnreal {x : α} {ε : ℝ≥0} :
    EMetric.closedBall x ε = closedBall x ε := by
  rw [← Metric.emetric_closedBall ε.coe_nonneg, ENNReal.ofReal_coe_nnreal]
#align metric.emetric_closed_ball_nnreal Metric.emetric_closedBall_nnreal

@[simp]
theorem Metric.emetric_ball_top (x : α) : EMetric.ball x ⊤ = univ :=
  eq_univ_of_forall fun _ => edist_lt_top _ _
#align metric.emetric_ball_top Metric.emetric_ball_top

theorem Metric.inseparable_iff {x y : α} : Inseparable x y ↔ dist x y = 0 := by
  rw [EMetric.inseparable_iff, edist_nndist, dist_nndist, ENNReal.coe_eq_zero, NNReal.coe_eq_zero]
#align metric.inseparable_iff Metric.inseparable_iff

/-- Build a new pseudometric space from an old one where the bundled uniform structure is provably
(but typically non-definitionaly) equal to some given uniform structure.
See Note [forgetful inheritance].
-/
@[reducible]
def PseudoMetricSpace.replaceUniformity {α} [U : UniformSpace α] (m : PseudoMetricSpace α)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : PseudoMetricSpace α :=
  { m with
    toUniformSpace := U
    uniformity_dist := H.trans PseudoMetricSpace.uniformity_dist }
#align pseudo_metric_space.replace_uniformity PseudoMetricSpace.replaceUniformity

theorem PseudoMetricSpace.replaceUniformity_eq {α} [U : UniformSpace α] (m : PseudoMetricSpace α)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : m.replaceUniformity H = m := by
  ext
  rfl
#align pseudo_metric_space.replace_uniformity_eq PseudoMetricSpace.replaceUniformity_eq

-- ensure that the bornology is unchanged when replacing the uniformity.
example {α} [U : UniformSpace α] (m : PseudoMetricSpace α)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) :
  (PseudoMetricSpace.replaceUniformity m H).toBornology = m.toBornology := rfl

/-- Build a new pseudo metric space from an old one where the bundled topological structure is
provably (but typically non-definitionaly) equal to some given topological structure.
See Note [forgetful inheritance].
-/
@[reducible]
def PseudoMetricSpace.replaceTopology {γ} [U : TopologicalSpace γ] (m : PseudoMetricSpace γ)
    (H : U = m.toUniformSpace.toTopologicalSpace) : PseudoMetricSpace γ :=
  @PseudoMetricSpace.replaceUniformity γ (m.toUniformSpace.replaceTopology H) m rfl
#align pseudo_metric_space.replace_topology PseudoMetricSpace.replaceTopology

theorem PseudoMetricSpace.replaceTopology_eq {γ} [U : TopologicalSpace γ] (m : PseudoMetricSpace γ)
    (H : U = m.toUniformSpace.toTopologicalSpace) : m.replaceTopology H = m := by
  ext
  rfl
#align pseudo_metric_space.replace_topology_eq PseudoMetricSpace.replaceTopology_eq

/-- One gets a pseudometric space from an emetric space if the edistance
is everywhere finite, by pushing the edistance to reals. We set it up so that the edist and the
uniformity are defeq in the pseudometric space and the pseudoemetric space. In this definition, the
distance is given separately, to be able to prescribe some expression which is not defeq to the
push-forward of the edistance to reals. -/
def PseudoEMetricSpace.toPseudoMetricSpaceOfDist {α : Type u} [e : PseudoEMetricSpace α]
    (dist : α → α → ℝ) (edist_ne_top : ∀ x y : α, edist x y ≠ ⊤)
    (h : ∀ x y, dist x y = ENNReal.toReal (edist x y)) : PseudoMetricSpace α where
  dist := dist
  dist_self x := by simp [h]
  dist_comm x y := by simp [h, edist_comm]
  dist_triangle x y z := by
    simp only [h]
    exact ENNReal.toReal_le_add (edist_triangle _ _ _) (edist_ne_top _ _) (edist_ne_top _ _)
  edist := edist
  edist_dist _ _ := by simp only [h, ENNReal.ofReal_toReal (edist_ne_top _ _)]
  toUniformSpace := e.toUniformSpace
  uniformity_dist := e.uniformity_edist.trans <| by
    simpa only [ENNReal.coe_toNNReal (edist_ne_top _ _), h]
      using (Metric.uniformity_edist_aux fun x y : α => (edist x y).toNNReal).symm
#align pseudo_emetric_space.to_pseudo_metric_space_of_dist PseudoEMetricSpace.toPseudoMetricSpaceOfDist

/-- One gets a pseudometric space from an emetric space if the edistance
is everywhere finite, by pushing the edistance to reals. We set it up so that the edist and the
uniformity are defeq in the pseudometric space and the emetric space. -/
@[reducible]
def PseudoEMetricSpace.toPseudoMetricSpace {α : Type u} [PseudoEMetricSpace α]
    (h : ∀ x y : α, edist x y ≠ ⊤) : PseudoMetricSpace α :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist (fun x y => ENNReal.toReal (edist x y)) h fun _ _ =>
    rfl
#align pseudo_emetric_space.to_pseudo_metric_space PseudoEMetricSpace.toPseudoMetricSpace

/-- Build a new pseudometric space from an old one where the bundled bornology structure is provably
(but typically non-definitionaly) equal to some given bornology structure.
See Note [forgetful inheritance].
-/
@[reducible]
def PseudoMetricSpace.replaceBornology {α} [B : Bornology α] (m : PseudoMetricSpace α)
    (H : ∀ s, @IsBounded _ B s ↔ @IsBounded _ PseudoMetricSpace.toBornology s) :
    PseudoMetricSpace α :=
  { m with
    toBornology := B
    cobounded_sets := Set.ext <| compl_surjective.forall.2 fun s =>
        (H s).trans <| by rw [isBounded_iff, mem_setOf_eq, compl_compl] }
#align pseudo_metric_space.replace_bornology PseudoMetricSpace.replaceBornology

theorem PseudoMetricSpace.replaceBornology_eq {α} [m : PseudoMetricSpace α] [B : Bornology α]
    (H : ∀ s, @IsBounded _ B s ↔ @IsBounded _ PseudoMetricSpace.toBornology s) :
    PseudoMetricSpace.replaceBornology _ H = m := by
  ext
  rfl
#align pseudo_metric_space.replace_bornology_eq PseudoMetricSpace.replaceBornology_eq

-- ensure that the uniformity is unchanged when replacing the bornology.
example {α} [B : Bornology α] (m : PseudoMetricSpace α)
    (H : ∀ s, @IsBounded _ B s ↔ @IsBounded _ PseudoMetricSpace.toBornology s) :
  (PseudoMetricSpace.replaceBornology m H).toUniformSpace = m.toUniformSpace := rfl

section Real

/-- Instantiate the reals as a pseudometric space. -/
instance Real.pseudoMetricSpace : PseudoMetricSpace ℝ where
  dist x y := |x - y|
  dist_self := by simp [abs_zero]
  dist_comm x y := abs_sub_comm _ _
  dist_triangle x y z := abs_sub_le _ _ _
  edist_dist := fun x y => by exact ENNReal.coe_nnreal_eq _
#align real.pseudo_metric_space Real.pseudoMetricSpace

theorem Real.dist_eq (x y : ℝ) : dist x y = |x - y| := rfl
#align real.dist_eq Real.dist_eq

theorem Real.nndist_eq (x y : ℝ) : nndist x y = Real.nnabs (x - y) := rfl
#align real.nndist_eq Real.nndist_eq

theorem Real.nndist_eq' (x y : ℝ) : nndist x y = Real.nnabs (y - x) :=
  nndist_comm _ _
#align real.nndist_eq' Real.nndist_eq'

theorem Real.dist_0_eq_abs (x : ℝ) : dist x 0 = |x| := by simp [Real.dist_eq]
#align real.dist_0_eq_abs Real.dist_0_eq_abs

theorem Real.dist_left_le_of_mem_uIcc {x y z : ℝ} (h : y ∈ uIcc x z) : dist x y ≤ dist x z := by
  simpa only [dist_comm x] using abs_sub_left_of_mem_uIcc h
#align real.dist_left_le_of_mem_uIcc Real.dist_left_le_of_mem_uIcc

theorem Real.dist_right_le_of_mem_uIcc {x y z : ℝ} (h : y ∈ uIcc x z) : dist y z ≤ dist x z := by
  simpa only [dist_comm _ z] using abs_sub_right_of_mem_uIcc h
#align real.dist_right_le_of_mem_uIcc Real.dist_right_le_of_mem_uIcc

theorem Real.dist_le_of_mem_uIcc {x y x' y' : ℝ} (hx : x ∈ uIcc x' y') (hy : y ∈ uIcc x' y') :
    dist x y ≤ dist x' y' :=
  abs_sub_le_of_uIcc_subset_uIcc <| uIcc_subset_uIcc (by rwa [uIcc_comm]) (by rwa [uIcc_comm])
#align real.dist_le_of_mem_uIcc Real.dist_le_of_mem_uIcc

theorem Real.dist_le_of_mem_Icc {x y x' y' : ℝ} (hx : x ∈ Icc x' y') (hy : y ∈ Icc x' y') :
    dist x y ≤ y' - x' := by
  simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.2 <| hx.1.trans hx.2), neg_sub] using
    Real.dist_le_of_mem_uIcc (Icc_subset_uIcc hx) (Icc_subset_uIcc hy)
#align real.dist_le_of_mem_Icc Real.dist_le_of_mem_Icc

theorem Real.dist_le_of_mem_Icc_01 {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    dist x y ≤ 1 := by simpa only [sub_zero] using Real.dist_le_of_mem_Icc hx hy
#align real.dist_le_of_mem_Icc_01 Real.dist_le_of_mem_Icc_01

instance : OrderTopology ℝ :=
  orderTopology_of_nhds_abs fun x => by
    simp only [nhds_basis_ball.eq_biInf, ball, Real.dist_eq, abs_sub_comm]

theorem Real.ball_eq_Ioo (x r : ℝ) : ball x r = Ioo (x - r) (x + r) :=
  Set.ext fun y => by
    rw [mem_ball, dist_comm, Real.dist_eq, abs_sub_lt_iff, mem_Ioo, ← sub_lt_iff_lt_add',
      sub_lt_comm]
#align real.ball_eq_Ioo Real.ball_eq_Ioo

theorem Real.closedBall_eq_Icc {x r : ℝ} : closedBall x r = Icc (x - r) (x + r) := by
  ext y
  rw [mem_closedBall, dist_comm, Real.dist_eq, abs_sub_le_iff, mem_Icc, ← sub_le_iff_le_add',
    sub_le_comm]
#align real.closed_ball_eq_Icc Real.closedBall_eq_Icc

theorem Real.Ioo_eq_ball (x y : ℝ) : Ioo x y = ball ((x + y) / 2) ((y - x) / 2) := by
  rw [Real.ball_eq_Ioo, ← sub_div, add_comm, ← sub_add, add_sub_cancel', add_self_div_two,
    ← add_div, add_assoc, add_sub_cancel'_right, add_self_div_two]
#align real.Ioo_eq_ball Real.Ioo_eq_ball

theorem Real.Icc_eq_closedBall (x y : ℝ) : Icc x y = closedBall ((x + y) / 2) ((y - x) / 2) := by
  rw [Real.closedBall_eq_Icc, ← sub_div, add_comm, ← sub_add, add_sub_cancel', add_self_div_two, ←
    add_div, add_assoc, add_sub_cancel'_right, add_self_div_two]
#align real.Icc_eq_closed_ball Real.Icc_eq_closedBall

section MetricOrdered

variable [Preorder α] [CompactIccSpace α]

theorem totallyBounded_Icc (a b : α) : TotallyBounded (Icc a b) :=
  isCompact_Icc.totallyBounded
#align totally_bounded_Icc totallyBounded_Icc

theorem totallyBounded_Ico (a b : α) : TotallyBounded (Ico a b) :=
  totallyBounded_subset Ico_subset_Icc_self (totallyBounded_Icc a b)
#align totally_bounded_Ico totallyBounded_Ico

theorem totallyBounded_Ioc (a b : α) : TotallyBounded (Ioc a b) :=
  totallyBounded_subset Ioc_subset_Icc_self (totallyBounded_Icc a b)
#align totally_bounded_Ioc totallyBounded_Ioc

theorem totallyBounded_Ioo (a b : α) : TotallyBounded (Ioo a b) :=
  totallyBounded_subset Ioo_subset_Icc_self (totallyBounded_Icc a b)
#align totally_bounded_Ioo totallyBounded_Ioo

end MetricOrdered

/-- Special case of the sandwich theorem; see `tendsto_of_tendsto_of_tendsto_of_le_of_le'` for the
general case. -/
theorem squeeze_zero' {α} {f g : α → ℝ} {t₀ : Filter α} (hf : ∀ᶠ t in t₀, 0 ≤ f t)
    (hft : ∀ᶠ t in t₀, f t ≤ g t) (g0 : Tendsto g t₀ (nhds 0)) : Tendsto f t₀ (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds g0 hf hft
#align squeeze_zero' squeeze_zero'

/-- Special case of the sandwich theorem; see `tendsto_of_tendsto_of_tendsto_of_le_of_le`
and `tendsto_of_tendsto_of_tendsto_of_le_of_le'` for the general case. -/
theorem squeeze_zero {α} {f g : α → ℝ} {t₀ : Filter α} (hf : ∀ t, 0 ≤ f t) (hft : ∀ t, f t ≤ g t)
    (g0 : Tendsto g t₀ (𝓝 0)) : Tendsto f t₀ (𝓝 0) :=
  squeeze_zero' (eventually_of_forall hf) (eventually_of_forall hft) g0
#align squeeze_zero squeeze_zero

theorem Metric.uniformity_eq_comap_nhds_zero :
    𝓤 α = comap (fun p : α × α => dist p.1 p.2) (𝓝 (0 : ℝ)) := by
  ext s
  simp only [mem_uniformity_dist, (nhds_basis_ball.comap _).mem_iff]
  simp [subset_def, Real.dist_0_eq_abs]
#align metric.uniformity_eq_comap_nhds_zero Metric.uniformity_eq_comap_nhds_zero

theorem cauchySeq_iff_tendsto_dist_atTop_0 [Nonempty β] [SemilatticeSup β] {u : β → α} :
    CauchySeq u ↔ Tendsto (fun n : β × β => dist (u n.1) (u n.2)) atTop (𝓝 0) := by
  rw [cauchySeq_iff_tendsto, Metric.uniformity_eq_comap_nhds_zero, tendsto_comap_iff]; rfl
#align cauchy_seq_iff_tendsto_dist_at_top_0 cauchySeq_iff_tendsto_dist_atTop_0

theorem tendsto_uniformity_iff_dist_tendsto_zero {f : ι → α × α} {p : Filter ι} :
    Tendsto f p (𝓤 α) ↔ Tendsto (fun x => dist (f x).1 (f x).2) p (𝓝 0) := by
  rw [Metric.uniformity_eq_comap_nhds_zero, tendsto_comap_iff]; rfl
#align tendsto_uniformity_iff_dist_tendsto_zero tendsto_uniformity_iff_dist_tendsto_zero

theorem Filter.Tendsto.congr_dist {f₁ f₂ : ι → α} {p : Filter ι} {a : α}
    (h₁ : Tendsto f₁ p (𝓝 a)) (h : Tendsto (fun x => dist (f₁ x) (f₂ x)) p (𝓝 0)) :
    Tendsto f₂ p (𝓝 a) :=
  h₁.congr_uniformity <| tendsto_uniformity_iff_dist_tendsto_zero.2 h
#align filter.tendsto.congr_dist Filter.Tendsto.congr_dist

alias tendsto_of_tendsto_of_dist := Filter.Tendsto.congr_dist
#align tendsto_of_tendsto_of_dist tendsto_of_tendsto_of_dist

theorem tendsto_iff_of_dist {f₁ f₂ : ι → α} {p : Filter ι} {a : α}
    (h : Tendsto (fun x => dist (f₁ x) (f₂ x)) p (𝓝 0)) : Tendsto f₁ p (𝓝 a) ↔ Tendsto f₂ p (𝓝 a) :=
  Uniform.tendsto_congr <| tendsto_uniformity_iff_dist_tendsto_zero.2 h
#align tendsto_iff_of_dist tendsto_iff_of_dist

/-- If `u` is a neighborhood of `x`, then for small enough `r`, the closed ball
`Metric.closedBall x r` is contained in `u`. -/
theorem eventually_closedBall_subset {x : α} {u : Set α} (hu : u ∈ 𝓝 x) :
    ∀ᶠ r in 𝓝 (0 : ℝ), closedBall x r ⊆ u := by
  obtain ⟨ε, εpos, hε⟩ : ∃ ε, 0 < ε ∧ closedBall x ε ⊆ u := nhds_basis_closedBall.mem_iff.1 hu
  have : Iic ε ∈ 𝓝 (0 : ℝ) := Iic_mem_nhds εpos
  filter_upwards [this] with _ hr using Subset.trans (closedBall_subset_closedBall hr) hε
#align eventually_closed_ball_subset eventually_closedBall_subset

end Real

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
instance instPseudoMetricSpaceMulOpposite : PseudoMetricSpace αᵐᵒᵖ :=
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
    simp only [← NNReal.coe_le_coe, coe_nndist, dist_eq, max_le_iff, abs_sub_le_iff,
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
  rw [← nhds_comap_dist a, tendsto_comap_iff]; rfl
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

lemma eventually_isCompact_closedBall [LocallyCompactSpace α] (x : α) :
    ∀ᶠ r in 𝓝 (0 : ℝ), IsCompact (closedBall x r) := by
  rcases local_compact_nhds (x := x) (n := univ) univ_mem with ⟨s, hs, -, s_compact⟩
  filter_upwards [eventually_closedBall_subset hs] with r hr
  exact IsCompact.of_isClosed_subset s_compact isClosed_ball hr

lemma exists_isCompact_closedBall [LocallyCompactSpace α] (x : α) :
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
  simp [nndist_pi_def, Finset.sup_lt_iff (show ⊥ < r from hr)]
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

section ProperSpace

open Metric

/-- A pseudometric space is proper if all closed balls are compact. -/
class ProperSpace (α : Type u) [PseudoMetricSpace α] : Prop where
  isCompact_closedBall : ∀ x : α, ∀ r, IsCompact (closedBall x r)
#align proper_space ProperSpace

export ProperSpace (isCompact_closedBall)

/-- In a proper pseudometric space, all spheres are compact. -/
theorem isCompact_sphere {α : Type*} [PseudoMetricSpace α] [ProperSpace α] (x : α) (r : ℝ) :
    IsCompact (sphere x r) :=
  (isCompact_closedBall x r).of_isClosed_subset isClosed_sphere sphere_subset_closedBall
#align is_compact_sphere isCompact_sphere

/-- In a proper pseudometric space, any sphere is a `CompactSpace` when considered as a subtype. -/
instance Metric.sphere.compactSpace {α : Type*} [PseudoMetricSpace α] [ProperSpace α]
    (x : α) (r : ℝ) : CompactSpace (sphere x r) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere _ _)

-- see Note [lower instance priority]
/-- A proper pseudo metric space is sigma compact, and therefore second countable. -/
instance (priority := 100) secondCountable_of_proper [ProperSpace α] :
    SecondCountableTopology α := by
  -- We already have `sigmaCompactSpace_of_locallyCompact_secondCountable`, so we don't
  -- add an instance for `SigmaCompactSpace`.
  suffices SigmaCompactSpace α by exact EMetric.secondCountable_of_sigmaCompact α
  rcases em (Nonempty α) with (⟨⟨x⟩⟩ | hn)
  · exact ⟨⟨fun n => closedBall x n, fun n => isCompact_closedBall _ _, iUnion_closedBall_nat _⟩⟩
  · exact ⟨⟨fun _ => ∅, fun _ => isCompact_empty, iUnion_eq_univ_iff.2 fun x => (hn ⟨x⟩).elim⟩⟩
#align second_countable_of_proper secondCountable_of_proper

/-- If all closed balls of large enough radius are compact, then the space is proper. Especially
useful when the lower bound for the radius is 0. -/
theorem properSpace_of_compact_closedBall_of_le (R : ℝ)
    (h : ∀ x : α, ∀ r, R ≤ r → IsCompact (closedBall x r)) : ProperSpace α :=
  ⟨fun x r => IsCompact.of_isClosed_subset (h x (max r R) (le_max_right _ _)) isClosed_ball
    (closedBall_subset_closedBall <| le_max_left _ _)⟩
#align proper_space_of_compact_closed_ball_of_le properSpace_of_compact_closedBall_of_le

-- A compact pseudometric space is proper
-- see Note [lower instance priority]
instance (priority := 100) proper_of_compact [CompactSpace α] : ProperSpace α :=
  ⟨fun _ _ => isClosed_ball.isCompact⟩
#align proper_of_compact proper_of_compact

-- see Note [lower instance priority]
/-- A proper space is locally compact -/
instance (priority := 100) locally_compact_of_proper [ProperSpace α] : LocallyCompactSpace α :=
  locallyCompactSpace_of_hasBasis (fun _ => nhds_basis_closedBall) fun _ _ _ =>
    isCompact_closedBall _ _
#align locally_compact_of_proper locally_compact_of_proper

-- see Note [lower instance priority]
/-- A proper space is complete -/
instance (priority := 100) complete_of_proper [ProperSpace α] : CompleteSpace α :=
  ⟨fun {f} hf => by
    /- We want to show that the Cauchy filter `f` is converging. It suffices to find a closed
      ball (therefore compact by properness) where it is nontrivial. -/
    obtain ⟨t, t_fset, ht⟩ : ∃ t ∈ f, ∀ x ∈ t, ∀ y ∈ t, dist x y < 1 :=
      (Metric.cauchy_iff.1 hf).2 1 zero_lt_one
    rcases hf.1.nonempty_of_mem t_fset with ⟨x, xt⟩
    have : closedBall x 1 ∈ f := mem_of_superset t_fset fun y yt => (ht y yt x xt).le
    rcases (isCompact_iff_totallyBounded_isComplete.1 (isCompact_closedBall x 1)).2 f hf
        (le_principal_iff.2 this) with
      ⟨y, -, hy⟩
    exact ⟨y, hy⟩⟩
#align complete_of_proper complete_of_proper

/-- A binary product of proper spaces is proper. -/
instance prod_properSpace {α : Type*} {β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    [ProperSpace α] [ProperSpace β] : ProperSpace (α × β) where
  isCompact_closedBall := by
    rintro ⟨x, y⟩ r
    rw [← closedBall_prod_same x y]
    exact (isCompact_closedBall x r).prod (isCompact_closedBall y r)
#align prod_proper_space prod_properSpace

/-- A finite product of proper spaces is proper. -/
instance pi_properSpace {π : β → Type*} [Fintype β] [∀ b, PseudoMetricSpace (π b)]
    [h : ∀ b, ProperSpace (π b)] : ProperSpace (∀ b, π b) := by
  refine' properSpace_of_compact_closedBall_of_le 0 fun x r hr => _
  rw [closedBall_pi _ hr]
  exact isCompact_univ_pi fun _ => isCompact_closedBall _ _
#align pi_proper_space pi_properSpace

variable [ProperSpace α] {x : α} {r : ℝ} {s : Set α}

/-- If a nonempty ball in a proper space includes a closed set `s`, then there exists a nonempty
ball with the same center and a strictly smaller radius that includes `s`. -/
theorem exists_pos_lt_subset_ball (hr : 0 < r) (hs : IsClosed s) (h : s ⊆ ball x r) :
    ∃ r' ∈ Ioo 0 r, s ⊆ ball x r' := by
  rcases eq_empty_or_nonempty s with (rfl | hne)
  · exact ⟨r / 2, ⟨half_pos hr, half_lt_self hr⟩, empty_subset _⟩
  have : IsCompact s :=
    (isCompact_closedBall x r).of_isClosed_subset hs (h.trans ball_subset_closedBall)
  obtain ⟨y, hys, hy⟩ : ∃ y ∈ s, s ⊆ closedBall x (dist y x) :=
    this.exists_forall_ge hne (continuous_id.dist continuous_const).continuousOn
  have hyr : dist y x < r := h hys
  rcases exists_between hyr with ⟨r', hyr', hrr'⟩
  exact ⟨r', ⟨dist_nonneg.trans_lt hyr', hrr'⟩, hy.trans <| closedBall_subset_ball hyr'⟩
#align exists_pos_lt_subset_ball exists_pos_lt_subset_ball

/-- If a ball in a proper space includes a closed set `s`, then there exists a ball with the same
center and a strictly smaller radius that includes `s`. -/
theorem exists_lt_subset_ball (hs : IsClosed s) (h : s ⊆ ball x r) : ∃ r' < r, s ⊆ ball x r' := by
  cases' le_or_lt r 0 with hr hr
  · rw [ball_eq_empty.2 hr, subset_empty_iff] at h
    subst s
    exact (exists_lt r).imp fun r' hr' => ⟨hr', empty_subset _⟩
  · exact (exists_pos_lt_subset_ball hr hs h).imp fun r' hr' => ⟨hr'.1.2, hr'.2⟩
#align exists_lt_subset_ball exists_lt_subset_ball

end ProperSpace

theorem IsCompact.isSeparable {s : Set α} (hs : IsCompact s) : IsSeparable s :=
  haveI : CompactSpace s := isCompact_iff_compactSpace.mp hs
  isSeparable_of_separableSpace_subtype s
#align is_compact.is_separable IsCompact.isSeparable

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
  choose s hsc y hys hyx using H ε' (by exact_mod_cast ε'0)
  refine' ⟨s, hsc, iUnion₂_eq_univ_iff.2 fun x => ⟨y x, hys _, le_trans _ ε'ε.le⟩⟩
  exact_mod_cast hyx x
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

namespace Metric
theorem exists_isLocalMin_mem_ball [ProperSpace α] [TopologicalSpace β]
    [ConditionallyCompleteLinearOrder β] [OrderTopology β] {f : α → β} {a z : α} {r : ℝ}
    (hf : ContinuousOn f (closedBall a r)) (hz : z ∈ closedBall a r)
    (hf1 : ∀ z' ∈ sphere a r, f z < f z') : ∃ z ∈ ball a r, IsLocalMin f z := by
  simp_rw [← closedBall_diff_ball] at hf1
  exact (isCompact_closedBall a r).exists_isLocalMin_mem_open ball_subset_closedBall hf hz hf1
    isOpen_ball
#align metric.exists_local_min_mem_ball Metric.exists_isLocalMin_mem_ball

end Metric
