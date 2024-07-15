/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
## Ultrametric spaces are totally disconnected

In a metric space with an ultrametric, the space is totally disconnected.

## Tags

ultrametric, nonarchimedean, totally disconnected
-/
open Metric IsUltrametricDist

instance {X : Type*} [MetricSpace X] [IsUltrametricDist X] : TotallyDisconnectedSpace X :=
  totallyDisconnectedSpace_iff_connectedComponent_subsingleton.mpr fun x =>
  suffices IsTotallyDisconnected (connectedComponent x) from
    this _ Set.Subset.rfl isPreconnected_connectedComponent
      by
    intro t _ ht' y hy z hz
    contrapose! ht'
    intro H
    specialize H (ball y (dist y z / 2)) (ball y (dist y z / 2))ᶜ
      isOpen_ball (isClosed_ball _ _).isOpen_compl
    simp only [Set.union_compl_self, Set.subset_univ, Set.inter_compl_self, Set.inter_empty,
      Set.not_nonempty_empty, imp_false, true_implies] at H
    refine H ⟨y, hy, mem_ball.mpr ?_⟩ ⟨z, hz, ?_⟩
    · simpa using ht'
    · simp [dist_comm, dist_nonneg]
