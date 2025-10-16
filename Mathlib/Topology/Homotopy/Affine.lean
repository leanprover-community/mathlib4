/-
Copyright (c) 2025 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Topology.Homotopy.Path
import Mathlib.Analysis.Convex.PathConnected

/-!
# Affine homotopy between two continuous maps

In this file we define `ContinuousMap.Homotopy.affine f g`
to be the homotopy between `f` and `g`
such that `affine f g (t, x) = AffineMap.lineMap (f x) (g x) t`.
-/

variable {X E : Type*} [TopologicalSpace X]
  [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module ℝ E] [ContinuousSMul ℝ E]

namespace ContinuousMap.Homotopy

/-- The homotopy between `f` and `g`
such that `affine f g (t, x) = AffineMap.lineMap (f x) (g x) t`. -/
@[simps +simpRhs]
def affine (f g : C(X, E)) : f.Homotopy g where
  toFun x := Path.segment (f x.2) (g x.2) x.1
  continuous_toFun := by dsimp [AffineMap.lineMap_apply]; fun_prop
  map_zero_left := by simp
  map_one_left := by simp

@[simp]
theorem evalAt_affine (f g : C(X, E)) (x : X) : (affine f g).evalAt x = .segment (f x) (g x) := rfl

end ContinuousMap.Homotopy
