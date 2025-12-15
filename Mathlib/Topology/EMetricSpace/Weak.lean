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
theorem edist_top_right {a : α} :
    edist (self := OnePoint.toEDist (α := α)) (some a) ∞ = ⊤ := rfl

@[simp]
theorem edist_some_some {a b : α} :
    edist (self := OnePoint.toEDist (α := α)) (some a) (some b) = edist a b := rfl

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

instance toWeakPseudoEMetricSpace
    {α : Type u} [TopologicalSpace α] {m : WeakPseudoEMetricSpace α} :
    WeakPseudoEMetricSpace (OnePoint α) where
  edist := edist
  edist_self
  | some a => by simp [m.edist_self]
  | ∞ => rfl
  edist_comm
  | some _, some _ => by simp [m.edist_comm]
  | some _, ∞ => by simp
  | ∞, some _ => by simp
  | ∞, ∞ => by simp
  edist_triangle
  | some a, some b, some c => by simp [m.edist_triangle]
  | ∞, some _, some _ => by simp
  | some _, ∞, some _ => by simp
  | ∞, ∞, some _ => by simp
  | some _, some _, ∞ => by simp
  | ∞, some _, ∞ => by simp
  | some _, ∞, ∞ => by simp
  | ∞, ∞, ∞ => by simp
  topology_le := by
    intro s sh
    let τ := (uniformSpaceOfEDist
          m.edist m.edist_self m.edist_comm m.edist_triangle).toTopologicalSpace

    sorry
  topology_eq_on_restrict := by
    intro x s sO
    match x with
    | some x =>
      refine (IsOpen.inter_preimage_val_iff ?_).mpr ?_
      · refine (OnePoint.isOpen_iff_of_notMem ?_).mpr ?_
        · apply infty_not_mem_ball ⊤
          tauto
        have e : OnePoint.some ⁻¹' ball (some x) ⊤ = ball x ⊤ := by
          ext y
          have : (↑y : OnePoint α) = some y := by congr
          simp [this]
        rw [e]
        let τ := (uniformSpaceOfEDist
          m.edist m.edist_self m.edist_comm m.edist_triangle).toTopologicalSpace
        have : IsOpen[τ] (ball x ⊤) := by
          -- toPseudoEMetricSpaceToUniformSpace_uniformSpaceOfEDist
          sorry

        sorry
      · sorry
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
