/-
Copyright (c) 2026 Michał Pacholski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Pacholski
-/
module

public import Mathlib.Analysis.Normed.Operator.Nuclear
/-!
# Nuclear spaces
-/

@[expose] public section

open ContinuousLinearMap

universe u v

variable (𝕜 X : Type*)
variable [NontriviallyNormedField 𝕜]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]

/-- A topological vector space is nuclear if every continuous linear map
into a Banach space is a nuclear operator. -/
class NuclearSpace : Prop where
  isNuclear_map : ∀ (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (T : X →L[𝕜] F), IsNuclear T
