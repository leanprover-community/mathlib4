/-
Copyright (c) 2025 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Topology.Algebra.Group.AddTorsor
import Mathlib.Topology.Algebra.ProperAction.Basic

/-!
# The action underlying a topological additive torsor is proper.
-/

variable {V P : Type*} [AddGroup V] [AddTorsor V P]
variable [TopologicalSpace V] [TopologicalSpace P] [IsTopologicalAddTorsor P]

/-- If `P` is a topological torsor over `V`, the action of `V` on `P` is proper. -/
instance : ProperVAdd V P where
  isProperMap_vadd_pair := by
    let Φ : V × P ≃ₜ P × P :=
    { toFun vp := (vp.1 +ᵥ vp.2, vp.2)
      invFun pq := (pq.1 -ᵥ pq.2, pq.2)
      left_inv _ := by simp
      right_inv _ := by simp }
    exact Φ.isProperMap
