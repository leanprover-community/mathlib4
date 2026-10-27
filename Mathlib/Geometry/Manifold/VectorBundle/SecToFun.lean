/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Topology.FiberBundle.SecToFun
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Geometry.Manifold.Notation

/-!
# Converting a function into a section of the trivial bundle

TODO: make a proper doc-string for all of this, and describe what's happening here.

TODO: clean up this file, and make sure all lemmas that belong here actually are

-/

@[expose] public section

open Topology

open scoped Manifold ContDiff

namespace Bundle.Trivialization

section trivilization_topology

variable {B F Z : Type*} [TopologicalSpace B] [TopologicalSpace F]

section fiber_bundle

variable {E : B → Type*} [TopologicalSpace (TotalSpace F E)] (e : Trivialization F (π F E))

section
variable [(x : B) → Nonempty (E x)]

end

end fiber_bundle

end trivilization_topology

end Bundle.Trivialization
