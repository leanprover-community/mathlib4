/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, David Loeffler
-/
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# Ultrametric spaces are totally separated

In a metric space with an ultrametric, the space is totally separated, hence totally disconnected.

## Tags

ultrametric, nonarchimedean, totally separated, totally disconnected
-/
open Metric IsUltrametricDist

instance {X : Type*} [MetricSpace X] [IsUltrametricDist X] : TotallySeparatedSpace X :=
  totallySeparatedSpace_iff_exists_isClopen.mpr fun x y h ↦ by
    obtain ⟨r, hr, hr'⟩ := exists_between (dist_pos.mpr h)
    refine ⟨_, IsUltrametricDist.isClopen_ball x r, ?_, ?_⟩
    · simp only [mem_ball, dist_self, hr]
    · simp only [Set.mem_compl, mem_ball, dist_comm, not_lt, hr'.le]

example {X : Type*} [MetricSpace X] [IsUltrametricDist X] : TotallyDisconnectedSpace X :=
  inferInstance
