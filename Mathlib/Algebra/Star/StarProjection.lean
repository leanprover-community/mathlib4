/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Group.Idempotent

/-!
# Star projections

This file defines star projections, which are self-adjoint idempotents.

In star-ordered rings, star projections are non-negative.
(See `IsStarProjection.nonneg` in `Mathlib.Algebra.Order.Star.Basic`.)
-/

variable {M : Type*}

/-- a star projection is a self-adjoint idempotent -/
structure IsStarProjection [Mul M] [Star M] (p : M) : Prop where
  protected mul_self : p * p = p
  protected star_eq : star p = p

theorem IsStarProjection.isSelfAdjoint [Mul M] [Star M] {p : M}
    (hp : IsStarProjection p) : IsSelfAdjoint p := hp.star_eq

theorem IsStarProjection.isIdempotentElem [Mul M] [Star M] {p : M}
    (hp : IsStarProjection p) : IsIdempotentElem p := hp.mul_self

@[simp]
theorem IsStarProjection.zero
    [NonUnitalNonAssocSemiring M] [StarAddMonoid M] : IsStarProjection (0 : M) :=
  ⟨mul_zero _, star_zero _⟩

@[simp]
theorem IsStarProjection.one
    [MulOneClass M] [StarMul M] : IsStarProjection (1 : M) :=
  ⟨one_mul _, star_one _⟩

theorem isStarProjection_one_sub_iff
    [NonAssocRing M] [StarRing M] (p : M) :
    IsStarProjection (1 - p) ↔ IsStarProjection p := by
  constructor
  · rintro ⟨h1, h2⟩
    simp only [mul_sub, mul_one, sub_mul, one_mul, sub_eq_self, sub_eq_zero] at h1
    simp only [star_sub, star_one, sub_right_inj] at h2
    exact ⟨h1.symm, h2⟩
  · rintro ⟨h1, h2⟩
    constructor
    · simp only [mul_sub, mul_one, sub_mul, one_mul, h1, sub_self, sub_zero]
    · simp only [star_sub, star_one, sub_right_inj, h2]

/-- the sum of star projections is a star projection if their product is `0` -/
theorem IsStarProjection.add
    [NonUnitalNonAssocSemiring M] [StarRing M]
    {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : p * q = 0) :
    IsStarProjection (p + q) := by
  have : q * p = 0 := by
    apply star_inj.mp
    rw [star_mul, hp.star_eq, hq.star_eq, star_zero, hpq]
  constructor
  · simp only [mul_add, add_mul, hp.mul_self, this, add_zero, hpq, hq.mul_self, zero_add]
  · simp only [star_add, hp.star_eq, hq.star_eq]

/-- the product of star projections is a star projection if they commute -/
theorem IsStarProjection.mul [Semiring M] [StarRing M]
    {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : Commute p q) : IsStarProjection (p * q) := by
  constructor
  · nth_rw 1 [← mul_assoc]
    nth_rw 2 [mul_assoc]
    rw [← hpq, ← mul_assoc, hp.mul_self, mul_assoc, hq.mul_self]
  · rw [star_mul, hp.star_eq, hq.star_eq, hpq]
