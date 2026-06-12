/-
Copyright (c) 2025 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Topology.Algebra.Group.AddTorsor
public import Mathlib.Topology.Algebra.ProperAction.Basic

/-!
# The action underlying a topological torsor is proper.
-/

public section

variable {V P : Type*} [Group V] [Torsor V P]
variable [TopologicalSpace V] [TopologicalSpace P] [IsTopologicalTorsor P]

/-- If `P` is a topological torsor over `V`, the action of `V` on `P` is proper. -/
@[to_additive /-- If `P` is a topological additive torsor over `V`, the additive action of `V` on
`P` is proper. -/]
instance : ProperSMul V P where
  isProperMap_smul_pair := by
    let Φ : V × P ≃ₜ P × P :=
    { toFun vp := (vp.1 • vp.2, vp.2)
      invFun pq := (pq.1 /ₛ pq.2, pq.2)
      left_inv _ := by simp
      right_inv _ := by simp }
    exact Φ.isProperMap
