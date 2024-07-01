/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Star.Order

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
type class assumptions to be satisfied without a `CommSemiring` intance already in scope; not that
it is impossible, only that it shouldn't occur in practice. -/
example {R : Type*} [OrderedSemiring R] [StarRing R] [StarOrderedRing R] {x y : R} (hx : 0 ≤ x)
    (hy : 0 ≤ y) : x * y = y * x := by
  rw [← IsSelfAdjoint.of_nonneg (mul_nonneg hy hx), star_mul, IsSelfAdjoint.of_nonneg hx,
    IsSelfAdjoint.of_nonneg hy]

/- This will be implied by the instance below, we only prove it to avoid duplicating the
argument in the instance below for `mul_le_mul_of_nonneg_right`. -/
private lemma mul_le_mul_of_nonneg_left {R : Type*} [CommSemiring R] [PartialOrder R]
    [StarRing R] [StarOrderedRing R] {a b c : R} (hab : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b := by
  rw [StarOrderedRing.nonneg_iff] at hc
  induction hc using AddSubmonoid.closure_induction' with
  | mem _ h =>
    obtain ⟨x, rfl⟩ := h
    simp_rw [mul_assoc, mul_comm x, ← mul_assoc]
    exact conjugate_le_conjugate hab x
  | one => simp
  | mul x hx y hy =>
    simp only [← nonneg_iff, add_mul] at hx hy ⊢
    apply add_le_add <;> aesop

/-- A commutative star-ordered semiring is an ordered semiring.

This is not registered as an instance because it introduces a type class loop between `CommSemiring`
and `OrderedCommSemiring`, and it seem loops still cause issues sometimes.

See note [reducible non-instances]. -/
abbrev toOrderedCommSemiring (R : Type*) [CommSemiring R] [PartialOrder R]
    [StarRing R] [StarOrderedRing R] : OrderedCommSemiring R where
  add_le_add_left _ _ := add_le_add_left
  zero_le_one := by simpa using star_mul_self_nonneg (1 : R)
  mul_comm := mul_comm
  mul_le_mul_of_nonneg_left _ _ _ := mul_le_mul_of_nonneg_left
  mul_le_mul_of_nonneg_right a b c := by simpa only [mul_comm _ c] using mul_le_mul_of_nonneg_left

/-- A commutative star-ordered ring is an ordered ring.

This is not registered as an instance because it introduces a type class loop between `CommSemiring`
and `OrderedCommSemiring`, and it seem loops still cause issues sometimes.

See note [reducible non-instances]. -/
abbrev toOrderedCommRing (R : Type*) [CommRing R] [PartialOrder R]
    [StarRing R] [StarOrderedRing R] : OrderedCommRing R where
  add_le_add_left _ _ := add_le_add_left
  zero_le_one := by simpa using star_mul_self_nonneg (1 : R)
  mul_comm := mul_comm
  mul_nonneg _ _ := let _ := toOrderedCommSemiring R; mul_nonneg
