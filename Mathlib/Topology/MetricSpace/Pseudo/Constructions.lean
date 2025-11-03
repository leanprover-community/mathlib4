/-
Copyright (c) 2015, 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
import Mathlib.Topology.Bornology.Constructions
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Products of pseudometric spaces and other constructions

This file constructs the supremum distance on binary products of pseudometric spaces and provides
instances for type synonyms.
-/

open Bornology Filter Metric Set Topology
open scoped NNReal

variable {α β : Type*} [PseudoMetricSpace α]

/-- Pseudometric space structure pulled back by a function. -/
abbrev PseudoMetricSpace.induced {α β} (f : α → β) (m : PseudoMetricSpace β) :
    PseudoMetricSpace α where
  dist x y := dist (f x) (f y)
  dist_self _ := dist_self _
  dist_comm _ _ := dist_comm _ _
  dist_triangle _ _ _ := dist_triangle _ _ _
  edist x y := edist (f x) (f y)
  edist_dist _ _ := edist_dist _ _
  toUniformSpace := UniformSpace.comap f m.toUniformSpace
  uniformity_dist := (uniformity_basis_dist.comap _).eq_biInf
  toBornology := Bornology.induced f
  cobounded_sets := Set.ext fun s => mem_comap_iff_compl.trans <| by
    simp only [← isBounded_def, isBounded_iff, forall_mem_image, mem_setOf]

/-- Pull back a pseudometric space structure by an inducing map. This is a version of
`PseudoMetricSpace.induced` useful in case if the domain already has a `TopologicalSpace`
structure. -/
def Topology.IsInducing.comapPseudoMetricSpace {α β : Type*} [TopologicalSpace α]
    [m : PseudoMetricSpace β] {f : α → β} (hf : IsInducing f) : PseudoMetricSpace α :=
  .replaceTopology (.induced f m) hf.eq_induced

/-- Pull back a pseudometric space structure by a uniform inducing map. This is a version of
`PseudoMetricSpace.induced` useful in case if the domain already has a `UniformSpace`
structure. -/
def IsUniformInducing.comapPseudoMetricSpace {α β} [UniformSpace α] [m : PseudoMetricSpace β]
    (f : α → β) (h : IsUniformInducing f) : PseudoMetricSpace α :=
  .replaceUniformity (.induced f m) h.comap_uniformity.symm

instance Subtype.pseudoMetricSpace {p : α → Prop} : PseudoMetricSpace (Subtype p) :=
  PseudoMetricSpace.induced Subtype.val ‹_›

lemma Subtype.dist_eq {p : α → Prop} (x y : Subtype p) : dist x y = dist (x : α) y := rfl

lemma Subtype.nndist_eq {p : α → Prop} (x y : Subtype p) : nndist x y = nndist (x : α) y := rfl

namespace MulOpposite

@[to_additive]
instance instPseudoMetricSpace : PseudoMetricSpace αᵐᵒᵖ :=
  PseudoMetricSpace.induced MulOpposite.unop ‹_›

@[to_additive (attr := simp)]
lemma dist_unop (x y : αᵐᵒᵖ) : dist (unop x) (unop y) = dist x y := rfl

@[to_additive (attr := simp)]
lemma dist_op (x y : α) : dist (op x) (op y) = dist x y := rfl

@[to_additive (attr := simp)]
lemma nndist_unop (x y : αᵐᵒᵖ) : nndist (unop x) (unop y) = nndist x y := rfl

@[to_additive (attr := simp)]
lemma nndist_op (x y : α) : nndist (op x) (op y) = nndist x y := rfl

end MulOpposite

section NNReal

instance : PseudoMetricSpace ℝ≥0 := Subtype.pseudoMetricSpace

lemma NNReal.dist_eq (a b : ℝ≥0) : dist a b = |(a : ℝ) - b| := rfl

lemma NNReal.nndist_eq (a b : ℝ≥0) : nndist a b = max (a - b) (b - a) :=
  eq_of_forall_ge_iff fun _ => by
    simp only [max_le_iff, tsub_le_iff_right (α := ℝ≥0)]
    simp only [← NNReal.coe_le_coe, coe_nndist, dist_eq, abs_sub_le_iff,
      tsub_le_iff_right, NNReal.coe_add]

@[simp]
lemma NNReal.nndist_zero_eq_val (z : ℝ≥0) : nndist 0 z = z := by
  simp only [NNReal.nndist_eq, max_eq_right, tsub_zero, zero_tsub, zero_le']

@[simp]
lemma NNReal.nndist_zero_eq_val' (z : ℝ≥0) : nndist z 0 = z := by
  rw [nndist_comm]
  exact NNReal.nndist_zero_eq_val z

lemma NNReal.le_add_nndist (a b : ℝ≥0) : a ≤ b + nndist a b := by
  suffices (a : ℝ) ≤ (b : ℝ) + dist a b by
    rwa [← NNReal.coe_le_coe, NNReal.coe_add, coe_nndist]
  rw [← sub_le_iff_le_add']
  exact le_of_abs_le (dist_eq a b).ge

lemma NNReal.ball_zero_eq_Ico' (c : ℝ≥0) :
    Metric.ball (0 : ℝ≥0) c.toReal = Set.Ico 0 c := by ext x; simp

lemma NNReal.ball_zero_eq_Ico (c : ℝ) :
    Metric.ball (0 : ℝ≥0) c = Set.Ico 0 c.toNNReal := by
  by_cases c_pos : 0 < c
  · convert NNReal.ball_zero_eq_Ico' ⟨c, c_pos.le⟩
    simp [Real.toNNReal, c_pos.le]
  simp [not_lt.mp c_pos]

lemma NNReal.closedBall_zero_eq_Icc' (c : ℝ≥0) :
    Metric.closedBall (0 : ℝ≥0) c.toReal = Set.Icc 0 c := by ext x; simp

lemma NNReal.closedBall_zero_eq_Icc {c : ℝ} (c_nn : 0 ≤ c) :
    Metric.closedBall (0 : ℝ≥0) c = Set.Icc 0 c.toNNReal := by
  convert NNReal.closedBall_zero_eq_Icc' ⟨c, c_nn⟩
  simp [Real.toNNReal, c_nn]

end NNReal

namespace ULift
variable [PseudoMetricSpace β]

instance : PseudoMetricSpace (ULift β) := PseudoMetricSpace.induced ULift.down ‹_›

lemma dist_eq (x y : ULift β) : dist x y = dist x.down y.down := rfl

lemma nndist_eq (x y : ULift β) : nndist x y = nndist x.down y.down := rfl

@[simp] lemma dist_up_up (x y : β) : dist (ULift.up x) (ULift.up y) = dist x y := rfl

@[simp] lemma nndist_up_up (x y : β) : nndist (ULift.up x) (ULift.up y) = nndist x y := rfl

end ULift

section Prod
variable [PseudoMetricSpace β]

instance Prod.pseudoMetricSpaceMax : PseudoMetricSpace (α × β) :=
  let i := PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun x y : α × β => dist x.1 y.1 ⊔ dist x.2 y.2)
    (fun x y ↦ by positivity) fun x y => by
      simp only [ENNReal.ofReal_max, Prod.edist_eq, edist_dist]
  i.replaceBornology fun s => by
    simp only [← isBounded_image_fst_and_snd, isBounded_iff_eventually, forall_mem_image, ←
      eventually_and, ← forall_and, ← max_le_iff]
    rfl

lemma Prod.dist_eq {x y : α × β} : dist x y = max (dist x.1 y.1) (dist x.2 y.2) := rfl

@[simp]
lemma dist_prod_same_left {x : α} {y₁ y₂ : β} : dist (x, y₁) (x, y₂) = dist y₁ y₂ := by
  simp [Prod.dist_eq]

@[simp]
lemma dist_prod_same_right {x₁ x₂ : α} {y : β} : dist (x₁, y) (x₂, y) = dist x₁ x₂ := by
  simp [Prod.dist_eq]

lemma ball_prod_same (x : α) (y : β) (r : ℝ) : ball x r ×ˢ ball y r = ball (x, y) r :=
  ext fun z => by simp [Prod.dist_eq]

lemma closedBall_prod_same (x : α) (y : β) (r : ℝ) :
    closedBall x r ×ˢ closedBall y r = closedBall (x, y) r := ext fun z => by simp [Prod.dist_eq]

lemma sphere_prod (x : α × β) (r : ℝ) :
    sphere x r = sphere x.1 r ×ˢ closedBall x.2 r ∪ closedBall x.1 r ×ˢ sphere x.2 r := by
  obtain hr | rfl | hr := lt_trichotomy r 0
  · simp [hr]
  · cases x
    simp_rw [← closedBall_eq_sphere_of_nonpos le_rfl, union_self, closedBall_prod_same]
  · ext ⟨x', y'⟩
    simp_rw [Set.mem_union, Set.mem_prod, Metric.mem_closedBall, Metric.mem_sphere, Prod.dist_eq,
      max_eq_iff]
    refine or_congr (and_congr_right ?_) (and_comm.trans (and_congr_left ?_))
    all_goals rintro rfl; rfl

end Prod

lemma uniformContinuous_dist : UniformContinuous fun p : α × α => dist p.1 p.2 :=
  Metric.uniformContinuous_iff.2 fun ε ε0 =>
    ⟨ε / 2, half_pos ε0, fun {a b} h =>
      calc dist (dist a.1 a.2) (dist b.1 b.2) ≤ dist a.1 b.1 + dist a.2 b.2 :=
        dist_dist_dist_le _ _ _ _
      _ ≤ dist a b + dist a b := add_le_add (le_max_left _ _) (le_max_right _ _)
      _ < ε / 2 + ε / 2 := add_lt_add h h
      _ = ε := add_halves ε⟩

protected lemma UniformContinuous.dist [UniformSpace β] {f g : β → α} (hf : UniformContinuous f)
    (hg : UniformContinuous g) : UniformContinuous fun b => dist (f b) (g b) :=
  uniformContinuous_dist.comp (hf.prodMk hg)

@[continuity]
lemma continuous_dist : Continuous fun p : α × α ↦ dist p.1 p.2 := uniformContinuous_dist.continuous

@[continuity, fun_prop]
protected lemma Continuous.dist [TopologicalSpace β] {f g : β → α} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun b => dist (f b) (g b) :=
  continuous_dist.comp₂ hf hg

protected lemma Filter.Tendsto.dist {f g : β → α} {x : Filter β} {a b : α}
    (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) :
    Tendsto (fun x => dist (f x) (g x)) x (𝓝 (dist a b)) :=
  (continuous_dist.tendsto (a, b)).comp (hf.prodMk_nhds hg)

lemma continuous_iff_continuous_dist [TopologicalSpace β] {f : β → α} :
    Continuous f ↔ Continuous fun x : β × β => dist (f x.1) (f x.2) :=
  ⟨fun h => h.fst'.dist h.snd', fun h =>
    continuous_iff_continuousAt.2 fun _ => tendsto_iff_dist_tendsto_zero.2 <|
      (h.comp (.prodMk_left _)).tendsto' _ _ <| dist_self _⟩

lemma uniformContinuous_nndist : UniformContinuous fun p : α × α => nndist p.1 p.2 :=
  uniformContinuous_dist.subtype_mk _

protected lemma UniformContinuous.nndist [UniformSpace β] {f g : β → α} (hf : UniformContinuous f)
    (hg : UniformContinuous g) : UniformContinuous fun b => nndist (f b) (g b) :=
  uniformContinuous_nndist.comp (hf.prodMk hg)

lemma continuous_nndist : Continuous fun p : α × α => nndist p.1 p.2 :=
  uniformContinuous_nndist.continuous

@[fun_prop]
protected lemma Continuous.nndist [TopologicalSpace β] {f g : β → α} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun b => nndist (f b) (g b) :=
  continuous_nndist.comp₂ hf hg

protected lemma Filter.Tendsto.nndist {f g : β → α} {x : Filter β} {a b : α}
    (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) :
    Tendsto (fun x => nndist (f x) (g x)) x (𝓝 (nndist a b)) :=
  (continuous_nndist.tendsto (a, b)).comp (hf.prodMk_nhds hg)
