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

open scoped Uniformity Topology Filter NNReal ENNReal Pointwise OnePoint

universe u v w

namespace WeakEMetric


instance OnePoint.EDist {α : Type u} [EDist α] :
    EDist (OnePoint α) where
  edist := fun
    | some a, some b => edist a b
    | ∞, some _ => ⊤
    | some _, ∞ => ⊤
    | ∞, ∞ => 0

section

variable {α : Type u} [TopologicalSpace α] [WeakPseudoEMetricSpace α]

#check EDist α

@[simp]
theorem OnePoint.edist_top_top : edist (self := OnePoint.EDist (α := α))
   ∞ ∞ = 0 := rfl

@[simp]
theorem OnePoint.edist_top_left {a : α} :
    edist (self := OnePoint.EDist (α := α)) ∞ (some a) = ⊤ := rfl

@[simp]
theorem OnePoint.edist_top_right {a : α} :
    edist (self := OnePoint.EDist (α := α)) (some a) ∞ = ⊤ := rfl

@[simp]
theorem OnePoint.edist_some_some {a b : α} :
    edist (self := OnePoint.EDist (α := α)) (some a) (some b) = edist a b := rfl

end

variable {α : Type u} [TopologicalSpace α] [PseudoEMetricSpace α]

instance OnePoint.toWeakPseudoEMetricSpace
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

    sorry
  topology_eq_on_restrict := by
    intro x s sO
    match x with
    | some x =>
      rw [← toPseudoEMetricSpaceToUniformSpace_uniformSpaceOfEDist] at sO
      sorry
    | ∞ =>
      sorry

#check OnePoint
example : 0 = 0 := by sorry

#check WeakPseudoEMetricSpace

#check WithTop

end WeakEMetric


theorem toPseudoEMetricSpaceToUniformSpace_uniformSpaceOfEDist
    (α : Type u) [TopologicalSpace α] {m : WeakPseudoEMetricSpace α} :
    (WeakPseudoEMetricSpace.toPseudoEMetricSpace α).toUniformSpace =
    (uniformSpaceOfEDist m.edist m.edist_self m.edist_comm m.edist_triangle) := by rfl
