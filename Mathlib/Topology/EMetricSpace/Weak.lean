/-
Copyright (c) 2025 Felix Pernegger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Pernegger
-/
module

public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Weak (extended) metric spaces

In this file we prove products and One-point compactifications
of weak (pseudo) extended metric spaces are weak (pseudo) extended metric spaces.
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
    | some a, some b => edist a b
    | ∞, some _ => ⊤
    | some _, ∞ => ⊤
    | ∞, ∞ => 0

@[simp]
theorem edist_top_top : edist (self := OnePoint.toEDist (α := α))
   ∞ ∞ = 0 := rfl

@[simp]
theorem edist_top_left {a : α} :
    edist (self := OnePoint.toEDist (α := α)) ∞ (some a) = ⊤ := rfl

@[simp]
theorem edist_top_left' {a : α} :
    edist (self := OnePoint.toEDist (α := α)) ∞ ↑a = ⊤ := rfl

@[simp]
theorem edist_top_left'' {a : α} :
    edist (self := OnePoint.toEDist (α := α)) none (some a) = ⊤ := rfl

@[simp]
theorem edist_top_right {a : α} :
    edist (self := OnePoint.toEDist (α := α)) (some a) ∞ = ⊤ := rfl

@[simp]
theorem edist_top_right' {a : α} :
    edist (self := OnePoint.toEDist (α := α)) ↑a ∞ = ⊤ := rfl

@[simp]
theorem edist_some_some {a b : α} :
    edist (self := OnePoint.toEDist (α := α)) (some a) (some b) = edist a b := rfl

@[simp]
theorem edist_some_some' {a b : α} :
    edist (self := OnePoint.toEDist (α := α)) (some a) ↑b = edist a b := rfl

@[simp]
theorem edist_some_some'' {a b : α} :
    edist (self := OnePoint.toEDist (α := α)) ↑a ↑b = edist a b := rfl

theorem im_ball (a : α) (r : ENNReal) :
    OnePoint.some '' ball a r = ball (α := OnePoint α) ((some a) : (OnePoint α)) r := by
  ext x
  dsimp
  constructor <;> intro h
  · obtain ⟨y, yh, yx⟩ := h
    rw [← yx]
    simpa
  match x with
  | none => {simp at h}
  | some y => {
    use y
    constructor
    · simpa
    · rfl
  }

end

section

variable {α : Type u} [TopologicalSpace α] [WeakPseudoEMetricSpace α] {x : OnePoint α}

theorem ball_infty_of_pos {r : ENNReal} (hr : 0 < r) :
    ball (∞ : OnePoint α) r = {∞} := by
  refine eq_singleton_iff_unique_mem.mpr ⟨mem_ball.mpr hr, ?_⟩
  intro x
  match x with
  | some _ => simp
  | none => tauto

theorem infty_not_mem_ball (r : ENNReal) (hx : x ≠ ∞) : ∞ ∉ ball x r := by
  match x with
  | some a => simp
  | ∞ => contradiction

@[simp]
theorem infty_not_mem_ball' {x : α} (r : ENNReal) : ∞ ∉ ball (↑x : OnePoint α) r :=
  infty_not_mem_ball r (OnePoint.coe_ne_infty x)

private theorem edist_self' {α : Type u} [TopologicalSpace α] (m : WeakPseudoEMetricSpace α) :
    ∀ x : OnePoint α, edist x x = 0
  | some a => by simp [m.edist_self]
  | ∞ => rfl

private theorem edist_comm' {α : Type u} [TopologicalSpace α] (m : WeakPseudoEMetricSpace α) :
    ∀ x y : OnePoint α, edist x y = edist y x
  | some _, some _ => by simp [m.edist_comm]
  | some _, ∞ => by simp
  | ∞, some _ => by simp
  | ∞, ∞ => by simp

private theorem edist_triangle' {α : Type u} [TopologicalSpace α] (m : WeakPseudoEMetricSpace α) :
    ∀ x y z : OnePoint α, edist x z ≤ edist x y + edist y z
  | some a, some b, some c => by simp [m.edist_triangle]
  | ∞, some _, some _ => by simp
  | some _, ∞, some _ => by simp
  | ∞, ∞, some _ => by simp
  | some _, some _, ∞ => by simp
  | ∞, some _, ∞ => by simp
  | some _, ∞, ∞ => by simp
  | ∞, ∞, ∞ => by simp

instance toWeakPseudoEMetricSpace
    {α : Type u} [TopologicalSpace α] {m : WeakPseudoEMetricSpace α} :
    WeakPseudoEMetricSpace (OnePoint α) where
  edist := edist
  edist_self := edist_self' m
  edist_comm := edist_comm' m
  edist_triangle := edist_triangle' m
  topology_le := by
    rw [EMetric.Uniformity_eq]
    intro s sh
    apply (@EMetric.isOpen_iff (OnePoint α) (PseudoEMetricSpace_def
      (edist_self' m) (edist_comm' m) (edist_triangle' m))).2
    intro x xs
    match x with
    | ∞ => {
      use 1
      simpa [ball_infty_of_pos]
      }
    | some x => {
      let t := (ball (α := OnePoint α) (some x) 1 ∩ s)
      have aux : some x = (↑x : OnePoint α) := by rfl
      have op: IsOpen[(PseudoEMetricSpace_def
          m.edist_self m.edist_comm m.edist_triangle).toUniformSpace.toTopologicalSpace]
          (OnePoint.some ⁻¹' s) := by
        apply m.topology_le
        refine Continuous.isOpen_preimage ?_ s sh
        exact OnePoint.continuous_coe
      obtain ⟨ε, εp, εt⟩ := (@EMetric.isOpen_iff α (PseudoEMetricSpace_def
        m.edist_self m.edist_comm m.edist_triangle)).1 op x (mem_preimage.mpr xs)
      use ε
      refine ⟨εp, ?_⟩
      rw [← im_ball]
      exact image_subset_iff.mpr εt
      }
  topology_eq_on_restrict := by
    intro x s sO
    match x with
    | some x => {

      have po : IsOpen[(PseudoEMetricSpace_def
          m.edist_self m.edist_comm m.edist_triangle).toUniformSpace.toTopologicalSpace]
          (OnePoint.some ⁻¹' s) := by
        sorry
      obtain ⟨t, th⟩ := m.topology_eq_on_restrict (x := x) po
      sorry
      }
    | ∞ =>
      apply discreteTopology_iff_forall_isOpen.1
      rw [ball_infty_of_pos ENNReal.zero_lt_top]
      exact Subsingleton.discreteTopology

end

#check OnePoint
example : 0 = 0 := by sorry

#check WeakPseudoEMetricSpace

#check WithTop

end OnePoint

end WeakEMetric
