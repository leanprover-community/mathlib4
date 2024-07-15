/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Order.Module.OrderedSMul

#align_import algebra.order.algebra from "leanprover-community/mathlib"@"f5a600f8102c8bfdbd22781968a20a539304c1b4"

/-!
# Ordered algebras

An ordered algebra is an ordered semiring, which is an algebra over an ordered commutative semiring,
for which scalar multiplication is "compatible" with the two orders.

The prototypical example is 2x2 matrices over the reals or complexes (or indeed any C^* algebra)
where the ordering the one determined by the positive cone of positive operators,
i.e. `A ≤ B` iff `B - A = star R * R` for some `R`.
(We don't yet have this example in mathlib.)

## Implementation

Because the axioms for an ordered algebra are exactly the same as those for the underlying
module being ordered, we don't actually introduce a new class, but just use the `OrderedSMul`
mixin.

## Tags

ordered algebra
-/

section OrderedAlgebra

variable {R A : Type*} {a b : A} {r : R}



variable [OrderedCommRing R] [OrderedRing A] [Algebra R A]


variable [OrderedSMul R A]

theorem algebraMap_monotone : Monotone (algebraMap R A) := fun a b h => by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← sub_nonneg, ← sub_smul]
  trans (b - a) • (0 : A)
  · simp
  · exact smul_le_smul_of_nonneg_left zero_le_one (sub_nonneg.mpr h)
#align algebra_map_monotone algebraMap_monotone

end OrderedAlgebra
