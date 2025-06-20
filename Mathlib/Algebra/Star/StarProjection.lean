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
(See `IsStarProjection.nonneg` in `Mathlib.Algebra.Order.Star.Basic`.)
-/

variable {R : Type*}

/-- A star projection is a self-adjoint idempotent. -/
@[mk_iff]
structure IsStarProjection [Mul R] [Star R] (p : R) : Prop where
  protected mul_self : p * p = p
  protected star_eq : star p = p

namespace IsStarProjection

variable {p q : R}

theorem isSelfAdjoint [Mul R] [Star R]
    (hp : IsStarProjection p) : IsSelfAdjoint p := hp.star_eq

theorem isIdempotentElem [Mul R] [Star R]
    (hp : IsStarProjection p) : IsIdempotentElem p := hp.mul_self

lemma _root_.isStarProjection_iff' [Mul R] [Star R] :
    IsStarProjection p ↔ IsIdempotentElem p ∧ IsSelfAdjoint p :=
  ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2⟩⟩

theorem isStarNormal [Mul R] [Star R]
    (hp : IsStarProjection p) : IsStarNormal p :=
  hp.isSelfAdjoint.isStarNormal

variable (R) in
@[simp]
protected theorem zero
    [NonUnitalNonAssocSemiring R] [StarAddMonoid R] : IsStarProjection (0 : R) :=
  ⟨mul_zero _, star_zero _⟩

variable (R) in
@[simp]
protected theorem one [MulOneClass R] [StarMul R] : IsStarProjection (1 : R) :=
  ⟨one_mul _, star_one _⟩

theorem one_sub [NonAssocRing R] [StarRing R] (hp : IsStarProjection p) :
    IsStarProjection (1 - p) where
  mul_self := by simp [mul_sub, sub_mul, hp.mul_self]
  star_eq := by simp [hp.star_eq]

theorem _root_.isStarProjection_one_sub_iff [NonAssocRing R] [StarRing R] :
    IsStarProjection (1 - p) ↔ IsStarProjection p :=
  ⟨fun h ↦ sub_sub_cancel 1 p ▸ h.one_sub, .one_sub⟩

alias ⟨of_one_sub, _⟩ := isStarProjection_one_sub_iff

lemma mul_one_sub_self [NonAssocRing R] [Star R]
    (hp : IsStarProjection p) : p * (1 - p) = 0 := hp.isIdempotentElem.mul_one_sub_self

lemma one_sub_mul_self [NonAssocRing R] [Star R]
    (hp : IsStarProjection p) : (1 - p) * p = 0 := hp.isIdempotentElem.one_sub_mul_self

lemma commute_one_sub [NonAssocRing R] [Star R]
    (hp : IsStarProjection p) : Commute p (1 - p) := by
  rw [Commute, SemiconjBy, hp.one_sub_mul_self, hp.mul_one_sub_self]

lemma isStarProjection_iff_isSelfAdjoint_and_mul_one_sub_self [NonAssocRing R] [Star R] :
    IsStarProjection p ↔ IsSelfAdjoint p ∧ p * (1 - p) = 0 := by
  rw [mul_sub, mul_one, sub_eq_zero]
  exact ⟨fun hp => ⟨hp.star_eq, hp.mul_self.symm⟩, fun ⟨hp1, hp2⟩ => ⟨hp2.symm, hp1⟩⟩

lemma isStarProjection_iff_isSelfAdjoint_and_one_sub_mul_self [NonAssocRing R] [StarRing R] :
    IsStarProjection p ↔ IsSelfAdjoint p ∧ (1 - p) * p = 0 := by
  rw [sub_mul, one_mul, sub_eq_zero]
  exact ⟨fun hp => ⟨hp.star_eq, hp.mul_self.symm⟩, fun ⟨hp1, hp2⟩ => ⟨hp2.symm, hp1⟩⟩

/-- The sum of star projections is a star projection if their product is `0`. -/
theorem add [NonUnitalNonAssocSemiring R] [StarRing R]
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p * q = 0) :
    IsStarProjection (p + q) where
  star_eq := by simp [hp.star_eq, hq.star_eq]
  mul_self := by
    have : q * p = 0 := by simpa [hp.star_eq, hq.star_eq] using congr(star $(hpq))
    simp [mul_add, add_mul, hp.mul_self, hq.mul_self, hpq, this]

/-- The product of star projections is a star projection if they commute. -/
theorem mul [Semiring R] [StarRing R]
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : Commute p q) : IsStarProjection (p * q) where
  star_eq := by simpa [hp.star_eq, hq.star_eq] using hpq.eq.symm
  mul_self := by rw [hpq.symm.mul_mul_mul_comm, hp.mul_self, hq.mul_self]

theorem add_sub_mul_of_commute [Ring R] [StarRing R]
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : Commute p q) : IsStarProjection (p + q - p * q) where
  mul_self := hp.isIdempotentElem.add_sub_mul_of_commute hpq hq.isIdempotentElem
  star_eq := by simp only [hpq.eq, star_sub, star_add, hp.star_eq, hq.star_eq, star_mul]

theorem pow [Monoid R] [Star R] (hp : IsStarProjection p)
    {n : ℕ} (hn : n ≠ 0) : p ^ n = p := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
  exact hp.isIdempotentElem.pow_succ_eq _

theorem pow_succ [Monoid R] [Star R] (hp : IsStarProjection p)
    (n : ℕ) : p ^ (n + 1) = p := hp.isIdempotentElem.pow_succ_eq n

end IsStarProjection
