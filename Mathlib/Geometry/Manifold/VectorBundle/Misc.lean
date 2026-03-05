/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.Notation
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

/-!
# Miscellaneous pre-requisites for covariant derivatives

TODO: this file should not exist; move everything in here to a proper place
(and PR it accordingly)

-/

@[expose] public section -- TODO: think if we want to expose all definitions!

section prerequisites

open Bundle Filter Function Topology Set

open scoped Bundle Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]


set_option backward.isDefEq.respectTransparency false in
def bar (a : 𝕜) : TangentSpace 𝓘(𝕜) a ≃L[𝕜] 𝕜 where
  toFun v := v
  invFun v := v
  map_add' := by simp
  map_smul' := by simp



end prerequisites
