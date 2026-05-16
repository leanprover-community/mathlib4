/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.LinearAlgebra.InvariantBasisNumber

/-!

# Strong rank condition for commutative rings

We provide a shortcut instance for the fact that that any nontrivial commutative ring
satisfies the strong rank condition.

-/

/-- Shortcut instance for the fact that any nontrivial commutative ring satisfies
the strong rank condition. -/
public instance (priority := 200) commRing_strongRankCondition
    (R : Type*) [CommRing R] [Nontrivial R] : StrongRankCondition R := inferInstance
