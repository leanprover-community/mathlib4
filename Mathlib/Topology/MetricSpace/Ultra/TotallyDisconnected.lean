/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, David Loeffler
-/
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# Ultrametric spaces are totally disconnected

In a metric space with an ultrametric, the space is totally disconnected.

## Tags

ultrametric, nonarchimedean, totally disconnected
-/
open Metric IsUltrametricDist

instance {X : Type*} [MetricSpace X] [IsUltrametricDist X] : TotallyDisconnectedSpace X := by
  refine (totallyDisconnectedSpace_iff X).mpr (isTotallyDisconnected_of_isClopen_set fun x y h ↦ ?_)
  obtain ⟨r, hr, hr'⟩ := exists_between (dist_pos.mpr h)
  refine ⟨_, IsUltrametricDist.isClopen_ball x r, ?_, ?_⟩
  · simp only [mem_ball, dist_self, hr]
  · simp only [mem_ball, dist_comm, not_lt, hr'.le]
