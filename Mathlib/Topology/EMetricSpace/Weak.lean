/-
Copyright (c) 2025 Felix Pernegger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Pernegger
-/
module

public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# One point compactifications of Weak (pseudo) extended metric spaces

In this file we prove that one-point compactifications
of weak (pseudo) extended metric spaces are again weak (pseudo) extended metric spaces.
-/

@[expose] public section


open Set Filter

open scoped Uniformity Topology Filter NNReal Pointwise OnePoint

universe u v w

namespace WeakEMetric

namespace OnePoint

section

variable {α : Type u} [EDist α]

instance toEDist : EDist (OnePoint α) where
  edist := fun
    | (a : α), (b : α) => edist a b
    | ∞, (_ : α) => ⊤
    | (_ : α), ∞ => ⊤
    | ∞, ∞ => 0

@[simp]
theorem edist_top_top : edist (self := OnePoint.toEDist (α := α))
   ∞ ∞ = 0 := rfl

@[simp]
theorem edist_top_left {a : α} :
    edist (self := OnePoint.toEDist (α := α)) ∞ a = ⊤ := rfl

@[simp]
theorem edist_top_right {a : α} :
    edist (self := OnePoint.toEDist (α := α)) a ∞ = ⊤ := rfl

@[simp]
theorem edist_cast_cast {a b : α} :
    edist (self := OnePoint.toEDist (α := α)) a b = edist a b := rfl

theorem im_ball (a : α) (r : ENNReal) :
    OnePoint.some '' EMetric.ball a r = EMetric.ball (α := OnePoint α) a r := by
  ext x
  dsimp
  constructor <;> intro h
  · obtain ⟨y, yh, yx⟩ := h
    rw [← yx]
    simpa
  match x with
  | ∞ => simp at h
  | (y : α) =>
    use y
    simpa

end

section

variable {α : Type u} [TopologicalSpace α] [WeakPseudoEMetricSpace α] {x : OnePoint α}

theorem ball_infty_of_pos {r : ENNReal} (hr : 0 < r) :
    EMetric.ball (∞ : OnePoint α) r = {∞} := by
  refine eq_singleton_iff_unique_mem.mpr ⟨EMetric.mem_ball.mpr hr, ?_⟩
  intro x
  match x with
  | (_ : α) => simp
  | ∞ => tauto

theorem infty_not_mem_ball (r : ENNReal) (hx : x ≠ ∞) : ∞ ∉ EMetric.ball x r := by
  match x with
  | (_ : α) => simp
  | ∞ => contradiction

private lemma edist_self' {α : Type u} [TopologicalSpace α] (m : WeakPseudoEMetricSpace α) :
    ∀ x : OnePoint α, edist x x = 0
  | (_ : α) => by simp
  | ∞ => rfl

private lemma edist_comm' {α : Type u} [TopologicalSpace α] (m : WeakPseudoEMetricSpace α) :
    ∀ x y : OnePoint α, edist x y = edist y x
  | (_ : α), (_ : α) => by simp [m.edist_comm]
  | (_ : α), ∞ => by simp
  | ∞, (_ : α) => by simp
  | ∞, ∞ => by simp

private lemma edist_triangle' {α : Type u} [TopologicalSpace α] (m : WeakPseudoEMetricSpace α) :
    ∀ x y z : OnePoint α, edist x z ≤ edist x y + edist y z
  | (_ : α), (_ : α), (_ : α) => by simp [m.edist_triangle]
  | ∞, (_ : α), (_ : α) => by simp
  | (_ : α), ∞, _ => by simp
  | ∞, ∞, _ => by simp
  | _, (_ : α), ∞ => by simp

private lemma eq_of_edist_eq_zero' {α : Type u} [TopologicalSpace α] (m : WeakEMetricSpace α) :
    ∀ {x y : OnePoint α}, edist x y = 0 → x = y
  | (_ : α), (_ : α) => by
    intro eq
    rw [edist_cast_cast] at eq
    congr
    exact m.eq_of_edist_eq_zero eq
  | (_ : α), ∞ => by simp
  | ∞, (_ : α) => by simp
  | ∞, ∞ => by simp

private lemma prod_open_iff {α : Type u} {m : PseudoEMetricSpace α} (s : Set (OnePoint α)) :
    IsOpen[(pseudoEMetricSpaceOfEDist (edist_self' m.toWeakPseudoEMetricSpace)
    (edist_comm' m.toWeakPseudoEMetricSpace)
    (edist_triangle' m.toWeakPseudoEMetricSpace)).toUniformSpace.toTopologicalSpace] s
    ↔ IsOpen (OnePoint.some ⁻¹' s) := by
  rw [@EMetric.isOpen_iff _ m, @EMetric.isOpen_iff _ (pseudoEMetricSpaceOfEDist
    (edist_self' m.toWeakPseudoEMetricSpace) (edist_comm' m.toWeakPseudoEMetricSpace)
    (edist_triangle' m.toWeakPseudoEMetricSpace))]
  constructor <;> intro h x xh
  · obtain ⟨ε, εp, εh⟩ := h x xh
    use ε
    refine ⟨εp, ?_⟩
    rw [← im_ball] at εh
    exact image_subset_iff.mp εh
  · match x with
    | ∞ =>
      simp only [mem_preimage, gt_iff_lt] at h
      use 1
      simpa [ball_infty_of_pos]
    | (x : α) =>
      obtain ⟨ε, εp, εh⟩ := h x (mem_preimage.mpr xh)
      use ε
      refine ⟨εp, ?_⟩
      rw [← im_ball]
      exact image_subset_iff.mpr εh

instance toWeakPseudoEMetricSpace
    {α : Type u} [TopologicalSpace α] [m : WeakPseudoEMetricSpace α] :
    WeakPseudoEMetricSpace (OnePoint α) where
  edist := edist
  edist_self := private edist_self' m
  edist_comm := private edist_comm' m
  edist_triangle := private edist_triangle' m
  topology_le := by
    rw [EMetric.Uniformity_eq]
    intro s sh
    apply (@EMetric.isOpen_iff (OnePoint α) (pseudoEMetricSpaceOfEDist
      (edist_self' m) (edist_comm' m) (edist_triangle' m))).2
    intro x xs
    match x with
    | ∞ =>
      use 1
      simpa [ball_infty_of_pos]
    | (x : α) =>
      let t := (EMetric.ball (α := OnePoint α) x 1 ∩ s)
      have op: IsOpen[(pseudoEMetricSpaceOfEDist
          m.edist_self m.edist_comm m.edist_triangle).toUniformSpace.toTopologicalSpace]
          (OnePoint.some ⁻¹' s) := by
        apply m.topology_le
        refine Continuous.isOpen_preimage ?_ s sh
        exact OnePoint.continuous_coe
      obtain ⟨ε, εp, εt⟩ := (@EMetric.isOpen_iff α (pseudoEMetricSpaceOfEDist
        m.edist_self m.edist_comm m.edist_triangle)).1 op x (mem_preimage.mpr xs)
      use ε
      refine ⟨εp, ?_⟩
      rw [← im_ball]
      exact image_subset_iff.mpr εt
  topology_eq_on_restrict := by
    intro x r
    match x with
    | (x : α) =>
      obtain ⟨s, so, s's⟩ := m.topology_eq_on_restrict x r
      use OnePoint.some '' s
      constructor
      · exact OnePoint.isOpen_image_coe.mpr so
      ext ⟨y, yh⟩
      match y with
      | ∞ => contradiction
      | (z : α) =>
        apply Set.ext_iff.1 at s's
        simp only [mem_preimage, Subtype.forall, EMetric.mem_ball, mem_image] at s's ⊢ yh
        specialize s's z yh
        constructor <;> intro h
        · obtain ⟨r, rh, rh'⟩ := h
          rw [(OnePoint.isOpenEmbedding_coe).injective rh'] at rh
          exact s's.1 rh
        · use z
          tauto
    | ∞ =>
      apply discreteTopology_iff_forall_isOpen.1
      rw [ball_infty_of_pos ENNReal.zero_lt_top]
      exact Subsingleton.discreteTopology

instance toWeakEMetricSpace {α : Type u} [TopologicalSpace α] [m : WeakEMetricSpace α] :
    WeakEMetricSpace (OnePoint α) where
  edist := edist
  edist_self := private edist_self' _
  edist_comm := private edist_comm' _
  edist_triangle := private edist_triangle' _
  topology_le := (@toWeakPseudoEMetricSpace α _ _).topology_le
  topology_eq_on_restrict := (@toWeakPseudoEMetricSpace α _ _).topology_eq_on_restrict
  eq_of_edist_eq_zero := private eq_of_edist_eq_zero' m

end

end OnePoint

end WeakEMetric
