/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Semiconj.Defs

#align_import algebra.group.commute from "leanprover-community/mathlib"@"05101c3df9d9cfe9430edc205860c79b6d660102"

/-!
# Commuting pairs of elements in monoids

We define the predicate `Commute a b := a * b = b * a` and provide some operations on terms
`(h : Commute a b)`. E.g., if `a`, `b`, and c are elements of a semiring, and that
`hb : Commute a b` and `hc : Commute a c`.  Then `hb.pow_left 5` proves `Commute (a ^ 5) b` and
`(hb.pow_right 2).add_right (hb.mul_right hc)` proves `Commute a (b ^ 2 + b * c)`.

Lean does not immediately recognise these terms as equations, so for rewriting we need syntax like
`rw [(hb.pow_left 5).eq]` rather than just `rw [hb.pow_left 5]`.

This file defines only a few operations (`mul_left`, `inv_right`, etc).  Other operations
(`pow_right`, field inverse etc) are in the files that define corresponding notions.

## Implementation details

Most of the proofs come from the properties of `SemiconjBy`.
-/


variable {G : Type*}

/-- Two elements commute if `a * b = b * a`. -/
@[to_additive AddCommute "Two elements additively commute if `a + b = b + a`"]
def Commute {S : Type*} [Mul S] (a b : S) : Prop :=
  SemiconjBy a b b

namespace Commute

section Mul

variable {S : Type*} [Mul S]

/-- Equality behind `Commute a b`; useful for rewriting. -/
@[to_additive "Equality behind `AddCommute a b`; useful for rewriting."]
protected theorem eq {a b : S} (h : Commute a b) : a * b = b * a :=
  h

/-- Any element commutes with itself. -/
@[to_additive (attr := refl, simp) "Any element commutes with itself."]
protected theorem refl (a : S) : Commute a a :=
  Eq.refl (a * a)

/-- If `a` commutes with `b`, then `b` commutes with `a`. -/
@[to_additive (attr := symm) "If `a` commutes with `b`, then `b` commutes with `a`."]
protected theorem symm {a b : S} (h : Commute a b) : Commute b a :=
  Eq.symm h

@[to_additive]
protected theorem semiconjBy {a b : S} (h : Commute a b) : SemiconjBy a b b :=
  h

@[to_additive]
protected theorem symm_iff {a b : S} : Commute a b ↔ Commute b a :=
  ⟨Commute.symm, Commute.symm⟩

@[to_additive]
instance : IsRefl S Commute :=
  ⟨Commute.refl⟩

-- This instance is useful for `Finset.noncommProd`
@[to_additive]
instance on_isRefl {f : G → S} : IsRefl G fun a b => Commute (f a) (f b) :=
  ⟨fun _ => Commute.refl _⟩

end Mul

section Semigroup

variable {S : Type*} [Semigroup S] {a b c : S}

/-- If `a` commutes with both `b` and `c`, then it commutes with their product. -/
@[to_additive (attr := simp)
"If `a` commutes with both `b` and `c`, then it commutes with their sum."]
theorem mul_right (hab : Commute a b) (hac : Commute a c) : Commute a (b * c) :=
  SemiconjBy.mul_right hab hac
-- I think `ₓ` is necessary because of the `mul` vs `HMul` distinction

/-- If both `a` and `b` commute with `c`, then their product commutes with `c`. -/
@[to_additive (attr := simp)
"If both `a` and `b` commute with `c`, then their product commutes with `c`."]
theorem mul_left (hac : Commute a c) (hbc : Commute b c) : Commute (a * b) c :=
  SemiconjBy.mul_left hac hbc
-- I think `ₓ` is necessary because of the `mul` vs `HMul` distinction

@[to_additive]
protected theorem right_comm (h : Commute b c) (a : S) : a * b * c = a * c * b :=
  by simp only [mul_assoc, h.eq]
-- I think `ₓ` is necessary because of the `mul` vs `HMul` distinction

@[to_additive]
protected theorem left_comm (h : Commute a b) (c) : a * (b * c) = b * (a * c) :=
  by simp only [← mul_assoc, h.eq]
-- I think `ₓ` is necessary because of the `mul` vs `HMul` distinction

@[to_additive]
protected theorem mul_mul_mul_comm (hbc : Commute b c) (a d : S) :
    a * b * (c * d) = a * c * (b * d) := by simp only [hbc.left_comm, mul_assoc]

end Semigroup

@[to_additive]
protected theorem all {S : Type*} [CommSemigroup S] (a b : S) : Commute a b :=
  mul_comm a b
-- not sure why this needs an `ₓ`, maybe instance names not aligned?

section MulOneClass

variable {M : Type*} [MulOneClass M]

@[to_additive (attr := simp)]
theorem one_right (a : M) : Commute a 1 :=
  SemiconjBy.one_right a
-- I think `ₓ` is necessary because `One.toOfNat1` appears in the Lean 4 version

@[to_additive (attr := simp)]
theorem one_left (a : M) : Commute 1 a :=
  SemiconjBy.one_left a
-- I think `ₓ` is necessary because `One.toOfNat1` appears in the Lean 4 version

end MulOneClass

section Monoid

variable {M : Type*} [Monoid M] {a b : M}

@[to_additive (attr := simp)]
theorem pow_right (h : Commute a b) (n : ℕ) : Commute a (b ^ n) :=
  SemiconjBy.pow_right h n
-- `MulOneClass.toHasMul` vs. `MulOneClass.toMul`

@[to_additive (attr := simp)]
theorem pow_left (h : Commute a b) (n : ℕ) : Commute (a ^ n) b :=
  (h.symm.pow_right n).symm
-- `MulOneClass.toHasMul` vs. `MulOneClass.toMul`

-- todo: should nat power be called `nsmul` here?
@[to_additive (attr := simp)]
theorem pow_pow (h : Commute a b) (m n : ℕ) : Commute (a ^ m) (b ^ n) :=
  (h.pow_left m).pow_right n
-- `MulOneClass.toHasMul` vs. `MulOneClass.toMul`

-- porting note: `simpNF` told me to remove the `simp` attribute
@[to_additive]
theorem self_pow (a : M) (n : ℕ) : Commute a (a ^ n) :=
  (Commute.refl a).pow_right n
-- `MulOneClass.toHasMul` vs. `MulOneClass.toMul`

-- porting note: `simpNF` told me to remove the `simp` attribute
@[to_additive]
theorem pow_self (a : M) (n : ℕ) : Commute (a ^ n) a :=
  (Commute.refl a).pow_left n
-- `MulOneClass.toHasMul` vs. `MulOneClass.toMul`

-- porting note: `simpNF` told me to remove the `simp` attribute
@[to_additive]
theorem pow_pow_self (a : M) (m n : ℕ) : Commute (a ^ m) (a ^ n) :=
  (Commute.refl a).pow_pow m n
-- `MulOneClass.toHasMul` vs. `MulOneClass.toMul`

@[to_additive succ_nsmul']
theorem _root_.pow_succ' (a : M) (n : ℕ) : a ^ (n + 1) = a ^ n * a :=
  (pow_succ a n).trans (self_pow _ _)

end Monoid

section DivisionMonoid

variable [DivisionMonoid G] {a b c d: G}

@[to_additive]
protected theorem mul_inv (hab : Commute a b) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by rw [hab.eq, mul_inv_rev]

@[to_additive]
protected theorem inv (hab : Commute a b) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by rw [hab.eq, mul_inv_rev]

end DivisionMonoid

section Group

variable [Group G] {a b : G}

@[to_additive]
protected theorem mul_inv_cancel (h : Commute a b) : a * b * a⁻¹ = b := by
  rw [h.eq, mul_inv_cancel_right]

@[to_additive]
theorem mul_inv_cancel_assoc (h : Commute a b) : a * (b * a⁻¹) = b := by
  rw [← mul_assoc, h.mul_inv_cancel]

end Group

end Commute

section CommGroup

variable [CommGroup G] (a b : G)

@[to_additive (attr := simp)]
theorem mul_inv_cancel_comm : a * b * a⁻¹ = b :=
  (Commute.all a b).mul_inv_cancel

@[to_additive (attr := simp)]
theorem mul_inv_cancel_comm_assoc : a * (b * a⁻¹) = b :=
  (Commute.all a b).mul_inv_cancel_assoc

end CommGroup
