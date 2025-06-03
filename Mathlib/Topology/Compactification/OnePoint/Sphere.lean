/-
Copyright (c) 2025 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen, Oliver Nash
-/
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!

# One-point compactification of Euclidean space is homeomorphic to the sphere.

-/

open Function Metric Module Set Submodule

noncomputable section

variable {n : ℕ} {v : EuclideanSpace ℝ (Fin n.succ)} (hv : ‖v‖ = 1)

/-- The orthogonal complement of the span of a point on the sphere
is homeomorphic to a Euclidean space of codimension 1. -/
noncomputable def Submodule_homeo_Euclidean {n : ℕ}
    (v : sphere (0 : (EuclideanSpace ℝ (Fin n.succ))) 1) :
    Homeomorph ((span ℝ {v.1})ᗮ) (EuclideanSpace ℝ (Fin n)) :=
  letI fact {n : ℕ} : Fact (finrank ℝ (EuclideanSpace ℝ (Fin n.succ)) = n + 1) := ⟨by simp⟩
  (OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere v)).repr.toHomeomorph

/-- The one-point compactification of ℝⁿ, in the form of a codimension 1 subspace,
 is homeomorphic to the n-sphere. -/
def onePointHyperplaneHomeoUnitSphere :
    OnePoint (ℝ ∙ v)ᗮ ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin n.succ)) 1 :=
  OnePoint.equivOfIsEmbeddingOfRangeEq _ _
    (isEmbedding_stereographic_symm hv) (range_stereographic_symm hv)

/-- The one-point compactification of Euclidean space is homeomorphic to the sphere. -/
noncomputable def OnePointEuclidean_homeo_sphere : Homeomorph
    (OnePoint (EuclideanSpace ℝ (Fin n))) ((sphere (0 : EuclideanSpace ℝ (Fin n.succ)) 1)) := by
  have hv' : v ∈ sphere 0 (1:ℝ) := by simpa
  exact ((Submodule_homeo_Euclidean ⟨v,hv'⟩).symm.onePointCongr).trans
    <| onePointHyperplaneHomeoUnitSphere hv
