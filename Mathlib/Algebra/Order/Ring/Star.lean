/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Star.Basic

/-!
# Commutative star-ordered rings are ordered rings

A noncommutative star-ordered ring is generally not an ordered ring. Indeed, in a star-ordered
ring, nonnegative elements are self-adjoint, but the product of self-adjoint elements is
self-adjoint if and only if they commute. Therefore, a necessary condition for a star-ordered ring
to be an ordered ring is that all nonnegative elements commute.  Consequently, if a star-ordered
ring is spanned by it nonnegative elements (as is the case for C⋆-algebras) and it is also an
ordered ring, then it is commutative.

In this file we prove the converse: a *commutative* star-ordered ring is an ordered ring.
-/

namespace StarOrderedRing

/- This example shows that nonnegative elements in a ordered semiring which is also star-ordered
must commute. We provide this only as an example as opposed to a lemma because we never expect the
type class assumptions to be satisfied without a `CommSemiring` instance already in scope; not that
it is impossible, only that it shouldn't occur in practice. -/
example {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
    [StarRing R] [StarOrderedRing R] {x y : R} (hx : 0 ≤ x)
    (hy : 0 ≤ y) : x * y = y * x := by
  rw [← IsSelfAdjoint.of_nonneg (mul_nonneg hy hx), star_mul, IsSelfAdjoint.of_nonneg hx,
    IsSelfAdjoint.of_nonneg hy]

/-- A commutative star-ordered semiring is an ordered semiring. -/
instance toIsOrderedRing (R : Type*) [CommSemiring R] [PartialOrder R]
    [StarRing R] [StarOrderedRing R] : IsOrderedRing R where
  mul_le_mul_of_nonneg_left _a ha _b _c hbc := smul_le_smul_of_nonneg_left hbc ha
  mul_le_mul_of_nonneg_right _a ha _b _c hbc := smul_le_smul_of_nonneg_right hbc ha

end StarOrderedRing
