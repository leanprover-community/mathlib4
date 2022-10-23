/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland, Yury Kudryashov
-/
import Mathlib.Tactic.Relation.Symm
import Mathlib.Algebra.Group.Semiconj

/-!
# Commuting pairs of elements in monoids

We define the predicate `commute a b := a * b = b * a` and provide some operations on terms
`(h : commute a b)`.
E.g., if `a`, `b`, and `c` are elements of a semiring, and that `hb : commute a b` and
`hc : commute a c`.  Then `hb.pow_left 5` proves `commute (a ^ 5) b` and `(hb.pow_right 2).add_right
(hb.mul_right hc)` proves `commute a (b ^ 2 + b * c)`.

Lean does not immediately recognise these terms as equations, so for rewriting we need syntax like
`rw [(hb.pow_left 5).eq]` rather than just `rw [hb.pow_left 5]`.

This file defines only a few operations (`mul_left`, `inv_right`, etc).  Other operations
(`pow_right`, field inverse etc) are in the files that define corresponding notions.

## Implementation details

Most of the proofs come from the properties of `semiconj_by`.
-/


variable {G : Type _}

/-- Two elements commute if `a * b = b * a`. -/
@[to_additive AddCommute "Two elements additively commute if `a + b = b + a`"]
def Commute {S : Type _} [Mul S] (a b : S) : Prop :=
  SemiconjBy a b b

namespace Commute

section Mul

variable {S : Type _} [Mul S]

/-- Equality behind `commute a b`; useful for rewriting. -/
@[to_additive "Equality behind `add_commute a b`; useful for rewriting."]
protected theorem eq {a b : S} (h : Commute a b) : a * b = b * a :=
  h

/-- Any element commutes with itself. -/
-- TODO: restore @[refl]
@[simp, to_additive "Any element commutes with itself."]
protected theorem refl (a : S) : Commute a a :=
  Eq.refl (a * a)

/-- If `a` commutes with `b`, then `b` commutes with `a`. -/
@[symm, to_additive "If `a` commutes with `b`, then `b` commutes with `a`."]
protected theorem symm {a b : S} (h : Commute a b) : Commute b a :=
  Eq.symm h

@[to_additive]
protected theorem semiconj_by {a b : S} (h : Commute a b) : SemiconjBy a b b :=
  h

@[to_additive]
protected theorem symm_iff {a b : S} : Commute a b ↔ Commute b a :=
  ⟨Commute.symm, Commute.symm⟩

end Mul

section Semigroup

variable {S : Type _} [Semigroup S] {a b c : S}

/-- If `a` commutes with both `b` and `c`, then it commutes with their product. -/
@[simp, to_additive "If `a` commutes with both `b` and `c`, then it commutes with their sum."]
theorem mul_right (hab : Commute a b) (hac : Commute a c) : Commute a (b * c) :=
  SemiconjBy.mul_right hab hac

/-- If both `a` and `b` commute with `c`, then their product commutes with `c`. -/
@[simp, to_additive "If both `a` and `b` commute with `c`, then their product commutes with `c`."]
theorem mul_left (hac : Commute a c) (hbc : Commute b c) : Commute (a * b) c :=
  SemiconjBy.mul_left hac hbc

protected theorem right_comm (h : Commute b c) (a : S) : a * b * c = a * c * b :=
  by simp only [mul_assoc, h.eq]

protected theorem left_comm (h : Commute a b) (c) : a * (b * c) = b * (a * c) :=
  by simp only [← mul_assoc, h.eq]

end Semigroup

@[to_additive]
protected theorem all {S : Type _} [CommSemigroup S] (a b : S) : Commute a b :=
  mul_comm a b

section MulOneClass

variable {M : Type _} [MulOneClass M]

@[simp]
theorem one_right (a : M) : Commute a 1 :=
  SemiconjBy.one_right a

@[simp]
theorem one_left (a : M) : Commute 1 a :=
  SemiconjBy.one_left a

end MulOneClass

section Monoid

variable {M : Type _} [Monoid M] {a b : M}

@[simp]
theorem pow_right (h : Commute a b) (n : ℕ) : Commute a (b ^ n) :=
  SemiconjBy.pow_right h n

@[simp]
theorem pow_left (h : Commute a b) (n : ℕ) : Commute (a ^ n) b :=
  (h.symm.pow_right n).symm

@[simp]
theorem pow_pow (h : Commute a b) (m n : ℕ) : Commute (a ^ m) (b ^ n) :=
  (h.pow_left m).pow_right n

theorem self_pow (a : M) (n : ℕ) : Commute a (a ^ n) :=
  (Commute.refl a).pow_right n

theorem pow_self (a : M) (n : ℕ) : Commute (a ^ n) a :=
  (Commute.refl a).pow_left n

theorem pow_pow_self (a : M) (m n : ℕ) : Commute (a ^ m) (a ^ n) :=
  (Commute.refl a).pow_pow m n

theorem _root_.pow_succ' (a : M) (n : ℕ) : a ^ (n + 1) = a ^ n * a :=
  (pow_succ a n).trans (self_pow _ _)

end Monoid
