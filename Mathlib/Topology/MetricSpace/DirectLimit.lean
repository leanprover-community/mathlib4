/-
Copyright (c) 2026 Matthew Corbelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Corbelli
-/
module

public import Mathlib.Order.DirectedInverseSystem
public import Mathlib.Topology.MetricSpace.Isometry

/-!
# Metrics on direct limits

This file defines a `MetricSpace` instance on `DirectLimit G f` when `G` and `f` form a directed
system of metric spaces and the transition maps `f` are isometries (using `IsometryClass`).

See also `Metric.InductiveLimit` in `Mathlib/Topology/MetricSpace/Gluing.lean`, which
handles sequential inductive limits of metric spaces.
-/
@[expose] public section

namespace DirectLimit

variable {ι : Type*} [Preorder ι] {G : ι → Type*}
variable {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ _ _ h, T h}
variable [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)] [DirectedSystem G (f · · ·)]
variable [IsDirectedOrder ι]

section PseudoEMetricSpace

variable [∀ i, PseudoEMetricSpace (G i)]
variable [∀ i j h, IsometryClass (T h) (G i) (G j)]

noncomputable instance : PseudoEMetricSpace (DirectLimit G f) where
  edist := DirectLimit.lift₂ f f (fun i ↦ edist (α := G i))
    (fun i j h x y ↦ (IsometryClass.edist_eq (f i j h) x y).symm)
  edist_self := DirectLimit.induction f fun i x ↦ by rw [← edist_self x, lift₂_def]
  edist_comm := DirectLimit.induction₂ f fun i x y ↦ by simp_rw [lift₂_def, edist_comm x y]
  edist_triangle := DirectLimit.induction₃ f fun i x y z ↦ by simp_rw [lift₂_def, edist_triangle]

lemma edist_def (i : ι) (x y : G i) :
    edist (α := DirectLimit G f) ⟦⟨i,x⟩⟧ ⟦⟨i,y⟩⟧ = edist x y := by
  change DirectLimit.lift₂ f f _
    (fun i j h x y ↦ (IsometryClass.edist_eq (f i j h) x y).symm)
    ⟦⟨i, x⟩⟧ ⟦⟨i, y⟩⟧ = edist x y
  rw [lift₂_def]

end PseudoEMetricSpace

section EMetricSpace

variable [∀ i, EMetricSpace (G i)]
variable [∀ i j h, IsometryClass (T h) (G i) (G j)]

noncomputable instance : EMetricSpace (DirectLimit G f) where
  __ := (inferInstance : PseudoEMetricSpace (DirectLimit G f))
  eq_of_edist_eq_zero {x y} h := DirectLimit.induction₂ f (fun i x' y' h' ↦ by
    rw [edist_def] at h'
    simp [eq_of_edist_eq_zero h']) x y h

end EMetricSpace

section PseudoMetricSpace

variable [∀ i, PseudoMetricSpace (G i)]
variable [∀ i j h, IsometryClass (T h) (G i) (G j)]

noncomputable instance : PseudoMetricSpace (DirectLimit G f) where
  dist := DirectLimit.lift₂ f f (fun i ↦ dist (α := G i))
    (fun i j h x y ↦ (IsometryClass.dist_eq (f i j h) x y).symm)
  dist_self := DirectLimit.induction f fun i x ↦ by rw [← dist_self x, lift₂_def]
  dist_comm := DirectLimit.induction₂ f fun i x y ↦ by simp_rw [lift₂_def, dist_comm x y]
  dist_triangle := DirectLimit.induction₃ f fun i x y z ↦ by simp_rw [lift₂_def, dist_triangle]

lemma dist_def (i : ι) (x y : G i) :
    dist (α := DirectLimit G f) ⟦⟨i,x⟩⟧ ⟦⟨i,y⟩⟧ = dist x y := by
  change DirectLimit.lift₂ f f _
    (fun i j h x y ↦ (IsometryClass.dist_eq (f i j h) x y).symm)
    ⟦⟨i, x⟩⟧ ⟦⟨i, y⟩⟧ = dist x y
  rw [lift₂_def]

lemma nndist_def (i : ι) (x y : G i) :
    nndist (α := DirectLimit G f) ⟦⟨i,x⟩⟧ ⟦⟨i,y⟩⟧ = nndist x y := by
  simp_rw [nndist_dist, dist_def]

end PseudoMetricSpace

section MetricSpace

variable [∀ i, MetricSpace (G i)]
variable [∀ i j h, IsometryClass (T h) (G i) (G j)]

noncomputable instance : MetricSpace (DirectLimit G f) where
  __ := (inferInstance : PseudoMetricSpace (DirectLimit G f))
  eq_of_dist_eq_zero {x y} h := DirectLimit.induction₂ f (fun i x' y' h' ↦ by
    rw [dist_def] at h'
    simp [eq_of_dist_eq_zero h']) x y h

end MetricSpace

end DirectLimit
