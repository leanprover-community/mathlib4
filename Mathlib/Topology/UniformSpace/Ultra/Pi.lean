/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Topology.UniformSpace.Ultra.Prod

/-!
# Indexed products of ultrametric (nonarchimedean) uniform spaces

## Main results

* `IsUltraUniformity.pi`: an indexed product of uniform spaces with nonarchimedean uniformities
  has a nonarchimedean uniformity.

-/

/-- The indexed product of uniform spaces with nonarchimedean uniformities has a
nonarchimedean uniformity. -/
instance IsUltraUniformity.pi {ι : Type*} {X : ι → Type*} [U : Π i, UniformSpace (X i)]
    [h : ∀ i, IsUltraUniformity (X i)] :
    IsUltraUniformity (Π i, X i) := by
  suffices @IsUltraUniformity _ (⨅ i, UniformSpace.comap (Function.eval i) (U i)) by
    simpa [Pi.uniformSpace_eq _] using this
  exact .iInf fun i ↦ .comap (h i) (Function.eval i)
