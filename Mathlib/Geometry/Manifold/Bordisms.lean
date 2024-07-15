/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Util.Superscript

/-!
# Unoriented bordism theory

In this file, we sketch the beginnings of unoriented bordism theory.
This is not ready for mathlib yet (as we still need the instance that the boundary
of a manifold is a manifold again, might might need some hypotheses to be true).
-/

open scoped Manifold
open Metric (sphere)

-- Let us start with some preliminaries, which should go in other files later.

section ClosedManifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare a smooth manifold `M` over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M]

-- A topological manifold is closed iff it is compact without boundary.
-- XXX: how to say this in Lean?
--structure ClosedManifold (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
--  [SmoothManifoldWithCorners I M] extends [CompactSpace M] [I.Boundaryless] where

end ClosedManifold

section Basic

variable (M : Type*) [TopologicalSpace M] [T2Space M]
local macro:max "ℝ"n:superscript(term) : term => `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

-- n-manifold, bad definition: better def is "E is n-dimensional"
structure NManifold (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

-- not quite what I want yet...
structure ClosedNManifold (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [SmoothManifoldWithCorners (𝓡 n) M] extends NManifold n M

end Basic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare a smooth manifold `M` over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [hM : TopologicalSpace M] [ChartedSpace H M]
  [hI : SmoothManifoldWithCorners I M]

-- SingularNManifold n X M
/-- A singular `n`-manifold on a topological space `X` consists of a closed smooth `n`-manifold `M`
and a continuous map `f : M → X`.-/
structure SingularNManifold {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (X : Type*) [TopologicalSpace X] (n : ℕ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    {H : Type*} [TopologicalSpace H]
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners 𝕜 E H) [SmoothManifoldWithCorners I M] where
  hdim : FiniteDimensional.finrank 𝕜 E = n
  hcompact : CompactSpace M
  hbd : I.Boundaryless
  f : M → X
  hf : Continuous f

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare a smooth manifold `M` over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [hM : TopologicalSpace M] [ChartedSpace H M]
  [hI : SmoothManifoldWithCorners I M] {n : ℕ}


/-- If `M` is `n`-dimensional and closed, it is a singular `n`-manifold over itself. -/
def trivialSingularNManifold [I.Boundaryless] [CompactSpace M]
    (hdim : FiniteDimensional.finrank 𝕜 E = n) : SingularNManifold (n := n) (𝕜 := 𝕜) M M where
  E := E
  M := M
  I := I
  h₃ := sorry
  hM1 := hM
  hM2 := sorry
  hM3 := sorry --hI
  -- slightly less boring
  hdim := hdim
  hcompact := sorry
  hbd := sorry
  -- now comes the itneresting part
  f := id
  hf := continuous_id (X := M)

-- Equivalence: two singular n-manifolds are bordant if there exists's a cobordism between them...
