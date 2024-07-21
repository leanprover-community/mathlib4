/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.InteriorBoundary

/-!
# Closed `n`-dimensional manifolds

We define closed `n`-dimensional manifolds and show a few basic properties.

## Main definitions
* `ClosedManifold M I`: a topological manifold `M` is closed if it is compact and boundaryless
* `NManifold n M I`: an n-manifold is a smooth `n`-dimensional manifold `M`.
* `ClosedNManifold n M I`: a closed n-manifold `M` is both closed and an `n`-manifold

## Main results
* `ClosedManifold.prod`: the product of closed manifolds is closed
* `NManifold.prod`: the product of an `n`-manifold and an `m`-manifold is an `n+m`-manifold
* `ClosedNManifold.prod`: the product of a closed `n`-manifold and a closed `m`-manifold is a closed
`n+m`-manifold
* We prove a few basic examples
  - the empty set is closed and an `n`-manifold, for every `n` (TODO insert!)
  - Euclidean n-space is an n-manifold
  - the standard n-sphere is a closed n-manifold
  - the standard two-torus `S¹ × S¹` is a closed 2-manifold

TODO: investigate why the spheres fail!
-/

open scoped Manifold
open Metric (sphere)
open FiniteDimensional Set

noncomputable section

variable (n : ℕ) {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare a smooth manifold `M` over the pair `(E, H)`.
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners 𝕜 E H) [SmoothManifoldWithCorners I M]

/-- A topological manifold is called **closed** iff it is compact without boundary. -/
structure ClosedManifold [CompactSpace M] [BoundarylessManifold I M]

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] (N : Type*) [TopologicalSpace N] [ChartedSpace H' N]
  (J : ModelWithCorners 𝕜 E' H') [SmoothManifoldWithCorners J N]

instance ClosedManifold.prod [CompactSpace M] [BoundarylessManifold I M]
    [CompactSpace N] [BoundarylessManifold J N] :
  ClosedManifold (M × N) (I.prod J) where

/-- An **n-manifold** is a smooth `n`-dimensional manifold. -/
structure NManifold [NormedAddCommGroup E]  [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    {H : Type*} [TopologicalSpace H] (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners 𝕜 E H) [SmoothManifoldWithCorners I M] where
  hdim : finrank 𝕜 E = n

/-- The product of an `n`- and and an `m`-manifold is an `n+m`-manifold. -/
instance NManifold.prod {m n : ℕ} [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E']
    (s : NManifold m M I) (t : NManifold n N J) : NManifold (m + n) (M × N) (I.prod J) where
  hdim := by rw [s.hdim.symm, t.hdim.symm]; apply finrank_prod

structure ClosedNManifold [CompactSpace M] [BoundarylessManifold I M] [FiniteDimensional 𝕜 E]
  extends NManifold n M I

instance ClosedNManifold.ClosedManifold [CompactSpace M] [BoundarylessManifold I M]
  [FiniteDimensional 𝕜 E] : ClosedManifold M I where

variable {n}

/-- The product of a closed `n`- and a closed closed `m`-manifold is a closed `n+m`-manifold. -/
instance ClosedNManifold.prod {m n : ℕ} [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E']
    [CompactSpace M] [BoundarylessManifold I M] [CompactSpace N] [BoundarylessManifold J N]
    (s : ClosedNManifold m M I) (t : ClosedNManifold n N J) :
    ClosedNManifold (m + n) (M × N) (I.prod J) where
  -- TODO: can I inherit this from `NManifold.prod`?
  hdim := by rw [s.hdim.symm, t.hdim.symm]; apply finrank_prod

section examples

/-- The empty manifold is closed. -/
instance [IsEmpty M] : ClosedManifold M I where

-- The empty manifold, modelled on an `n`-dimensional space, is a closed `n`-manifold.
-- FIXME: is requiring the model space to be n-dimensional the right design decision?
instance {n : ℕ} [FiniteDimensional 𝕜 E] (h : finrank 𝕜 E = n) [IsEmpty M] :
    ClosedNManifold n M I where
  hdim := h

-- Let `E` be a finite-dimensional real normed space.
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- TODO: these two examples worked when ClosedManifold only demanded `I.Boundaryless`;
-- diagnose and fix this!
/-- The standard `n`-sphere is a closed manifold. -/
example {n : ℕ} [FiniteDimensional ℝ E] [Fact (finrank ℝ E = n + 1)] :
  ClosedManifold (sphere (0 : E) 1) (𝓡 n) where

/-- The standard `2`-torus is a closed manifold. -/
example [FiniteDimensional ℝ E] [Fact (finrank ℝ E = 1 + 1)] :
    ClosedManifold ((sphere (0 : E) 1) × (sphere (0 : E) 1)) ((𝓡 2).prod (𝓡 2)) where
-/

-- The standard Euclidean space is an `n`-manifold. -/
example {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [SmoothManifoldWithCorners (𝓡 n) M] : NManifold n M (𝓡 n) where
  hdim := finrank_euclideanSpace_fin

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The standard `n`-sphere is a closed `n`-manifold. -/
example {n : ℕ} [Fact (finrank ℝ F = n + 1)] : ClosedNManifold n (sphere (0 : F) 1) (𝓡 n) where
  hdim := finrank_euclideanSpace_fin

/-- The standard 2-torus is a closed two-manifold. -/
example [Fact (finrank ℝ F = 1 + 1)] :
    ClosedNManifold 2 ((sphere (0 : F) 1) × (sphere (0 : F) 1)) ((𝓡 1).prod (𝓡 1)) where
  hdim := by rw [finrank_prod, finrank_euclideanSpace_fin]

end examples
