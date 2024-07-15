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
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners 𝕜 E H) [SmoothManifoldWithCorners I M]

/-- A topological manifold is closed iff it is compact without boundary. -/
structure ClosedManifold [CompactSpace M] [I.Boundaryless]

/-- An **n-manifold** is a smooth `n`-dimensional manifold. -/
-- xxx: does this mention all data? is there a nicer way to do this?
structure NManifold (n : ℕ) [NormedAddCommGroup E]  [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    {H : Type*} [TopologicalSpace H] (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners 𝕜 E H) [SmoothManifoldWithCorners I M]
 where
  hdim : FiniteDimensional.finrank 𝕜 E = n

structure ClosedNManifold (n : ℕ) [CompactSpace M] [I.Boundaryless] [FiniteDimensional 𝕜 E]
    extends ClosedManifold M I where
  hdim : FiniteDimensional.finrank 𝕜 E = n

end ClosedManifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  (M : Type*) [hM : TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners 𝕜 E H) [SmoothManifoldWithCorners I M]

-- current order is `SingularNManifold M I X n`, right? would prefer `SingularNManifold n X M I`...
/-- A **singular `n`-manifold** on a topological space `X` consists of a
closed smooth `n`-manifold `M` and a continuous map `f : M → X`. -/
structure SingularNManifold (X : Type*) [TopologicalSpace X] (n : ℕ)
    [CompactSpace M] [I.Boundaryless] [FiniteDimensional 𝕜 E] extends ClosedNManifold M I n where
  f : M → X
  hf : Continuous f

variable {n : ℕ}

/-- If `M` is `n`-dimensional and closed, it is a singular `n`-manifold over itself. -/
def trivialSingularNManifold [I.Boundaryless] [CompactSpace M] [FiniteDimensional 𝕜 E]
    (hdim : FiniteDimensional.finrank 𝕜 E = n) : SingularNManifold M I M n where
  hdim := hdim
  f := id
  hf := continuous_id (X := M)

-- Equivalence: two singular n-manifolds are bordant if there exists's a cobordism between them...
