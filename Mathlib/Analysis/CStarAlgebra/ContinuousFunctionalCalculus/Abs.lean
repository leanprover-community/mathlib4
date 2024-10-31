/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon
-/

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Topology.ContinuousMap.StarOrdered

/-! # Abs in CFC

This file defines the map `CFC.abs : A → A`, the absolute value function in continuous functional
calculus for a not-necessarily-unital CStarAlgebra.

We prove the following basic properties:

* Blah
* Blah
* Blah

## TODO

+ No idea yet...

-/

variable {A : Type*} [NonUnitalRing A] [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
variable [StarRing A] [TopologicalSpace A]
variable [NonUnitalContinuousFunctionalCalculus ℝ (IsStarNormal : A → Prop)]

namespace CStarAlgebra

noncomputable def Modulus := cfcₙ (A := A) fun t ↦ √((star t)* t)

end CStarAlgebra
