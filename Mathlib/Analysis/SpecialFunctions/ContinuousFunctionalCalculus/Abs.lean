/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon
-/

import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow

/-!
# Absolute value via nonunital continuous functional calculus

## Main declarations

+ Blah...

## Implementation notes


## TODO

+...

-/

namespace CFC

variable {A : Type*}  [PartialOrder A] [NonUnitalNormedRing A] [StarRing A] [Module NNReal A]
variable [SMulCommClass NNReal A A] [IsScalarTower NNReal A A]
variable [NonUnitalContinuousFunctionalCalculus NNReal fun (a : A) ↦ 0 ≤ a]

/-- The absolute value of an operator, using the nonunital continuous functional calculus. -/
noncomputable def abs (a : A) := sqrt (star a * a)

end CFC
