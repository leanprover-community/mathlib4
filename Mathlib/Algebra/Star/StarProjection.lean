/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Ring.Idempotent

/-!
# Star projections

This file defines star projections, which are self-adjoint idempotents.

In star-ordered rings, star projections are non-negative.
(See `IsStarProjection.nonneg` in `Mathlib/Algebra/Order/Star/Basic.lean`.)
-/

variable {R : Type*}

/-- A star projection is a self-adjoint idempotent. -/
@[mk_iff]
structure IsStarProjection [Mul R] [Star R] (p : R) : Prop extends
  isIdempotentElem : IsIdempotentElem p,
  isSelfAdjoint : IsSelfAdjoint p

namespace IsStarProjection

variable {p q : R}

lemma _root_.isStarProjection_iff' [Mul R] [Star R] :
    IsStarProjection p ↔ p * p = p ∧ star p = p := by
  rw [isStarProjection_iff, isSelfAdjoint_iff, isIdempotentElem_iff]

variable (R) in
@[simp]
protected theorem zero [NonUnitalNonAssocSemiring R] [StarAddMonoid R] : IsStarProjection (0 : R) :=
  ⟨.zero _, .zero _⟩

variable (R) in
@[simp]
protected theorem one [MulOneClass R] [StarMul R] : IsStarProjection (1 : R) :=
  ⟨.one _, .one _⟩

section NonAssocRing
variable [NonAssocRing R]

nonrec theorem one_sub [StarRing R] (hp : IsStarProjection p) : IsStarProjection (1 - p) where
  isIdempotentElem := hp.one_sub
  isSelfAdjoint := .sub (.one _) hp.isSelfAdjoint

theorem _root_.isStarProjection_one_sub_iff [StarRing R] :
    IsStarProjection (1 - p) ↔ IsStarProjection p :=
  ⟨fun h ↦ sub_sub_cancel 1 p ▸ h.one_sub, .one_sub⟩

alias ⟨of_one_sub, _⟩ := isStarProjection_one_sub_iff

end NonAssocRing

/-- The sum of star projections is a star projection if their product is `0`. -/
nonrec theorem add [NonUnitalNonAssocSemiring R] [StarRing R]
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p * q = 0) :
    IsStarProjection (p + q) where
  isSelfAdjoint := hp.isSelfAdjoint.add hq.isSelfAdjoint
  isIdempotentElem := hp.isIdempotentElem.add hq.isIdempotentElem <| by
    rw [hpq, zero_add]
    simpa [hp.star_eq, hq.star_eq] using congr(star $(hpq))

/-- The product of star projections is a star projection if they commute. -/
theorem mul [NonUnitalSemiring R] [StarRing R]
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : Commute p q) : IsStarProjection (p * q) where
  isSelfAdjoint := (hp.commute_iff hq.isSelfAdjoint).mp hpq
  isIdempotentElem := hp.mul_of_commute hpq hq.isIdempotentElem

nonrec theorem add_sub_mul_of_commute [Ring R] [StarRing R]
    (hpq : Commute p q) (hp : IsStarProjection p) (hq : IsStarProjection q) :
    IsStarProjection (p + q - p * q) where
  isIdempotentElem := hp.add_sub_mul_of_commute hpq hq.isIdempotentElem
  isSelfAdjoint := .sub (hp.isSelfAdjoint.add hq.isSelfAdjoint)
    ((IsSelfAdjoint.commute_iff hp.isSelfAdjoint hq.isSelfAdjoint).mp hpq)

end IsStarProjection
