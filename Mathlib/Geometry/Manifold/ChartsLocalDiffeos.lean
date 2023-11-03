/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners

/-!
# Charts are structomorphisms

We prove that charts of a charted space are `Structomorph`s.
For a `C^n` manifold in particular, this implies charts are `C^n` diffeomorphisms.
-/

open Function Manifold Set SmoothManifoldWithCorners TopologicalSpace Topology
set_option autoImplicit false

-- Let `M` be a charted space modelled on `H`, with structure groupoid `G`.
variable {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {G : StructureGroupoid H} [HasGroupoid M G]
  {e e' : LocalHomeomorph M H}

-- TODO: Generalise this to all extended charts, if `I` is boundaryless.
