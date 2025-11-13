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
structure IsStarProjection [Mul R] [Star R] (p : R) : Prop where
  protected isIdempotentElem : IsIdempotentElem p
  protected isSelfAdjoint : IsSelfAdjoint p

namespace IsStarProjection

variable {p q : R}

lemma _root_.isStarProjection_iff' [Mul R] [Star R] :
    IsStarProjection p ↔ p * p = p ∧ star p = p :=
  isStarProjection_iff _

theorem isStarNormal [Mul R] [Star R]
    (hp : IsStarProjection p) : IsStarNormal p :=
  hp.isSelfAdjoint.isStarNormal

variable (R) in
@[simp]
protected theorem zero [NonUnitalNonAssocSemiring R] [StarAddMonoid R] : IsStarProjection (0 : R) :=
  ⟨.zero, .zero _⟩

variable (R) in
@[simp]
protected theorem one [MulOneClass R] [StarMul R] : IsStarProjection (1 : R) :=
  ⟨.one, .one _⟩

theorem pow_eq [Monoid R] [Star R] (hp : IsStarProjection p) {n : ℕ} (hn : n ≠ 0) : p ^ n = p :=
  hp.isIdempotentElem.pow_eq hn

theorem pow_succ_eq [Monoid R] [Star R] (hp : IsStarProjection p) (n : ℕ) : p ^ (n + 1) = p :=
  hp.isIdempotentElem.pow_succ_eq n

section NonAssocRing
variable [NonAssocRing R]

theorem one_sub [StarRing R] (hp : IsStarProjection p) : IsStarProjection (1 - p) where
  isIdempotentElem := hp.isIdempotentElem.one_sub
  isSelfAdjoint := .sub (.one _) hp.isSelfAdjoint

theorem _root_.isStarProjection_one_sub_iff [StarRing R] :
    IsStarProjection (1 - p) ↔ IsStarProjection p :=
  ⟨fun h ↦ sub_sub_cancel 1 p ▸ h.one_sub, .one_sub⟩

alias ⟨of_one_sub, _⟩ := isStarProjection_one_sub_iff

lemma mul_one_sub_self [Star R] (hp : IsStarProjection p) : p * (1 - p) = 0 :=
  hp.isIdempotentElem.mul_one_sub_self

lemma one_sub_mul_self [Star R] (hp : IsStarProjection p) : (1 - p) * p = 0 :=
  hp.isIdempotentElem.one_sub_mul_self

end NonAssocRing

/-- The sum of star projections is a star projection if their product is `0`. -/
theorem add [NonUnitalNonAssocSemiring R] [StarRing R]
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p * q = 0) :
    IsStarProjection (p + q) where
  isSelfAdjoint := hp.isSelfAdjoint.add hq.isSelfAdjoint
  isIdempotentElem := hp.isIdempotentElem.add hq.isIdempotentElem <| by
    rw [hpq, zero_add]
    simpa [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using congr(star $(hpq))

/-- The product of star projections is a star projection if they commute. -/
theorem mul [NonUnitalSemiring R] [StarRing R]
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : Commute p q) : IsStarProjection (p * q) where
  isSelfAdjoint := (IsSelfAdjoint.commute_iff hp.isSelfAdjoint hq.isSelfAdjoint).mp hpq
  isIdempotentElem := hp.isIdempotentElem.mul_of_commute hpq hq.isIdempotentElem

/-- `q - p` is a star projection when `p * q = p`. -/
theorem sub_of_mul_eq_left [NonUnitalNonAssocRing R] [StarRing R]
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p * q = p) :
    IsStarProjection (q - p) where
  isSelfAdjoint := hq.isSelfAdjoint.sub hp.isSelfAdjoint
  isIdempotentElem := hp.isIdempotentElem.sub
    hq.isIdempotentElem hpq
    (by simpa [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using congr(star $(hpq)))

/-- `q - p` is a star projection when `q * p = p`. -/
theorem sub_of_mul_eq_right [NonUnitalNonAssocRing R] [StarRing R]
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hqp : q * p = p) :
    IsStarProjection (q - p) := hp.sub_of_mul_eq_left hq
  (by simpa [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using congr(star $(hqp)))

/-- `q - p` is a star projection iff `p * q = p`. -/
theorem sub_iff_mul_eq_left [NonUnitalRing R] [StarRing R] [IsAddTorsionFree R]
    {p q : R} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    IsStarProjection (q - p) ↔ p * q = p := by
  rw [isStarProjection_iff, hp.isIdempotentElem.sub_iff hq.isIdempotentElem]
  simp_rw [hq.isSelfAdjoint.sub hp.isSelfAdjoint, and_true]
  nth_rw 3 [← hp.isSelfAdjoint]
  nth_rw 2 [← hq.isSelfAdjoint]
  rw [← star_mul, star_eq_iff_star_eq, hp.isSelfAdjoint, eq_comm]
  simp_rw [and_self]

/-- `q - p` is a star projection iff `q * p = p`. -/
theorem sub_iff_mul_eq_right [NonUnitalRing R] [StarRing R] [IsAddTorsionFree R]
    {p q : R} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    IsStarProjection (q - p) ↔ q * p = p := by
  rw [← star_inj]
  simp [star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq,
    sub_iff_mul_eq_left hp hq]

theorem add_sub_mul_of_commute [NonUnitalRing R] [StarRing R]
    (hpq : Commute p q) (hp : IsStarProjection p) (hq : IsStarProjection q) :
    IsStarProjection (p + q - p * q) where
  isIdempotentElem := hp.isIdempotentElem.add_sub_mul_of_commute hpq hq.isIdempotentElem
  isSelfAdjoint := .sub (hp.isSelfAdjoint.add hq.isSelfAdjoint)
    ((IsSelfAdjoint.commute_iff hp.isSelfAdjoint hq.isSelfAdjoint).mp hpq)

end IsStarProjection
