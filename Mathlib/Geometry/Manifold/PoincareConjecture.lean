/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Homotopy.Equiv

/-!
# Statement of the generalized Poincaré conjecture

https://en.wikipedia.org/wiki/Generalized_Poincar%C3%A9_conjecture
-/

open scoped Manifold
open Metric (sphere)

variable (M : Type*) [TopologicalSpace M] [CompactSpace M] [T2Space M]

/-- The generalized topological Poincaré conjecture.
 - For n = 2 it follows from the classification of surfaces.
 - For n ≥ 5 it was proven by Stephen Smale in 1961.
 - For n = 4 it was proven by Michael Freedman in 1982.
 - For n = 3 it was proven by Grigori Perelman in 2003. -/
proof_wanted ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere
    (n : ℕ) [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] :
    letI S := sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1
    ContinuousMap.HomotopyEquiv M S → Nonempty (Homeomorph M S)

/-- The 3-dimensional topological Poincaré conjecture (proven by Perelman) -/
proof_wanted SimplyConnectedSpace.nonempty_homeomorph_sphere_fin4
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [SimplyConnectedSpace M] :
    Nonempty (Homeomorph M <| sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)

/-- The 3-dimensional smooth Poincaré conjecture (proven by Perelman) -/
proof_wanted SimplyConnectedSpace.nonempty_diffeomorph_sphere_fin4
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [SmoothManifoldWithCorners (𝓡 3) M]
    [SimplyConnectedSpace M] :
    Nonempty (Diffeomorph (𝓡 3) (𝓡 3) M (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ∞)

/-- The 4-dimensional smooth Poincaré conjecture (still open) -/
def ContinuousMap.HomotopyEquiv.nonempty_diffeomorph_sphere_fin5 : Prop :=
  ∀ (_ : ChartedSpace (EuclideanSpace ℝ (Fin 4)) M) (_ : SmoothManifoldWithCorners (𝓡 4) M),
    letI S := sphere (0 : EuclideanSpace ℝ (Fin 5)) 1
    ContinuousMap.HomotopyEquiv M S → Nonempty (Diffeomorph (𝓡 4) (𝓡 4) M S ∞)

/-- The existence of an exotic 7-sphere (due to John Milnor) -/
proof_wanted exists_homeomorph_not_diffeomorph_sphere_fin8 :
    letI S := sphere (0 : EuclideanSpace ℝ (Fin 8)) 1
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace (EuclideanSpace ℝ (Fin 7)) M)
      (_ : SmoothManifoldWithCorners (𝓡 7) M) (_homeo : Homeomorph M S),
      IsEmpty (Diffeomorph (𝓡 7) (𝓡 7) M S ∞)
