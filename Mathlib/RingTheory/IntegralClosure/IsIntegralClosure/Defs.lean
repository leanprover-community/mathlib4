/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

#align_import ring_theory.integral_closure from "leanprover-community/mathlib"@"641b6a82006416ec431b2987b354af9311fed4f2"

/-!
# Integral closure as a characteristic predicate

## Main definitions

Let `R` be a `CommRing` and let `A` be an R-algebra.

* `IsIntegralClosure R A` : the characteristic predicate stating `A` is the integral closure of `R`
  in `B`, i.e. that an element of `B` is integral over `R` iff it is an element of
  (the image of) `A`.
-/

open Polynomial
section IsIntegralClosure

/-- `IsIntegralClosure A R B` is the characteristic predicate stating `A` is
the integral closure of `R` in `B`,
i.e. that an element of `B` is integral over `R` iff it is an element of (the image of) `A`.
-/
class IsIntegralClosure (A R B : Type*) [CommRing R] [CommSemiring A] [CommRing B] [Algebra R B]
  [Algebra A B] : Prop where
  algebraMap_injective' : Function.Injective (algebraMap A B)
  isIntegral_iff : ∀ {x : B}, IsIntegral R x ↔ ∃ y, algebraMap A B y = x
#align is_integral_closure IsIntegralClosure

end IsIntegralClosure

#align_import ring_theory.integral_closure from "leanprover-community/mathlib"@"641b6a82006416ec431b2987b354af9311fed4f2"
