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
to be an ordered ring is that all nonnegative elements commute.

In this file we prove a kind of converse: a *commutative* star-ordered ring is an ordered ring.
-/

namespace StarOrderedRing

/- This example shows that nonnegative elements in a ordered semiring which is also star-ordered
must commute. -/
example {R : Type*} [OrderedSemiring R] [StarOrderedRing R] {x y : R} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x * y = y * x := by
  -- nonnegative elements are self-adjoint; we prove it by hand to avoid adding imports
  have : ∀ z : R, 0 ≤ z → star z = z := by
    intros z hz
    rw [nonneg_iff] at hz
    induction hz using AddSubmonoid.closure_induction' with
    | Hs _ h => obtain ⟨x, rfl⟩ := h; simp
    | H1 => simp
    | Hmul x hx y hy => simp only [←nonneg_iff] at hx hy; aesop
  -- `0 ≤ y * x`, and hence `y * x` is self-adjoint
  have := this _ <| mul_nonneg hy hx
  aesop

/- This will be implied by the instance below, we only prove it to avoid duplicating the
argument in the instance below for `mul_le_mul_of_nonneg_right`. -/
lemma mul_le_mul_of_nonneg_left {R : Type*} [CommSemiring R] [PartialOrder R] [StarOrderedRing R]
    {a b c : R} (hab : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b := by
  rw [StarOrderedRing.nonneg_iff] at hc
  induction hc using AddSubmonoid.closure_induction' with
  | Hs _ h =>
    obtain ⟨x, rfl⟩ := h
    simp_rw [mul_assoc, mul_comm x, ←mul_assoc]
    exact conjugate_le_conjugate hab x
  | H1 => simp
  | Hmul x hx y hy =>
    simp only [←nonneg_iff, add_mul] at hx hy ⊢
    apply add_le_add <;> aesop

/-- A commutative star-ordered semiring is an ordered semiring.

See note [lower instance priority]. -/
instance (priority := 100) {R : Type*} [CommSemiring R] [PartialOrder R] [StarOrderedRing R] :
    OrderedCommSemiring R where
  add_le_add_left _ _ := add_le_add_left
  zero_le_one := by simpa using star_mul_self_nonneg (1 : R)
  mul_comm := mul_comm
  mul_le_mul_of_nonneg_left _ _ _ := mul_le_mul_of_nonneg_left
  mul_le_mul_of_nonneg_right a b c := by simpa only [mul_comm _ c] using mul_le_mul_of_nonneg_left

/-- A commutative star-ordered ring is an ordered ring.

See note [lower instance priority]. -/
instance (priority := 100) {R : Type*} [CommRing R] [PartialOrder R] [StarOrderedRing R] :
    OrderedCommRing R where
  add_le_add_left _ _ := add_le_add_left
  zero_le_one := zero_le_one
  mul_comm := mul_comm
  mul_nonneg _ _ := mul_nonneg
