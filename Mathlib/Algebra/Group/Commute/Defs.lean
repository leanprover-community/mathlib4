/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Semiconj.Defs
import Mathlib.Init.Algebra.Classes

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

assert_not_exists MonoidWithZero
assert_not_exists DenselyOrdered

variable {G M S : Type*}

/-- Two elements commute if `a * b = b * a`. -/
@[to_additive "Two elements additively commute if `a + b = b + a`"]
def Commute [Mul S] (a b : S) : Prop :=
  SemiconjBy a b b
#align commute Commute
#align add_commute AddCommute

/--
Two elements `a` and `b` commute if `a * b = b * a`.
-/
@[to_additive]
theorem commute_iff_eq [Mul S] (a b : S) : Commute a b ↔ a * b = b * a := Iff.rfl

namespace Commute

section Mul

variable [Mul S]

/-- Equality behind `Commute a b`; useful for rewriting. -/
@[to_additive "Equality behind `AddCommute a b`; useful for rewriting."]
protected theorem eq {a b : S} (h : Commute a b) : a * b = b * a :=
  h
#align commute.eq Commute.eq
#align add_commute.eq AddCommute.eq

/-- Any element commutes with itself. -/
@[to_additive (attr := refl, simp) "Any element commutes with itself."]
protected theorem refl (a : S) : Commute a a :=
  Eq.refl (a * a)
#align commute.refl Commute.refl
#align add_commute.refl AddCommute.refl

/-- If `a` commutes with `b`, then `b` commutes with `a`. -/
@[to_additive (attr := symm) "If `a` commutes with `b`, then `b` commutes with `a`."]
protected theorem symm {a b : S} (h : Commute a b) : Commute b a :=
  Eq.symm h
#align commute.symm Commute.symm
#align add_commute.symm AddCommute.symm

@[to_additive]
protected theorem semiconjBy {a b : S} (h : Commute a b) : SemiconjBy a b b :=
  h
#align commute.semiconj_by Commute.semiconjBy
#align add_commute.semiconj_by AddCommute.addSemiconjBy

@[to_additive]
protected theorem symm_iff {a b : S} : Commute a b ↔ Commute b a :=
  ⟨Commute.symm, Commute.symm⟩
#align commute.symm_iff Commute.symm_iff
#align add_commute.symm_iff AddCommute.symm_iff

@[to_additive]
instance : IsRefl S Commute :=
  ⟨Commute.refl⟩

-- This instance is useful for `Finset.noncommProd`
@[to_additive]
instance on_isRefl {f : G → S} : IsRefl G fun a b => Commute (f a) (f b) :=
  ⟨fun _ => Commute.refl _⟩
#align commute.on_is_refl Commute.on_isRefl
#align add_commute.on_is_refl AddCommute.on_isRefl

end Mul

section Semigroup

variable [Semigroup S] {a b c : S}

/-- If `a` commutes with both `b` and `c`, then it commutes with their product. -/
@[to_additive (attr := simp)
"If `a` commutes with both `b` and `c`, then it commutes with their sum."]
theorem mul_right (hab : Commute a b) (hac : Commute a c) : Commute a (b * c) :=
  SemiconjBy.mul_right hab hac
#align commute.mul_right Commute.mul_rightₓ
#align add_commute.add_right AddCommute.add_rightₓ
-- I think `ₓ` is necessary because of the `mul` vs `HMul` distinction

/-- If both `a` and `b` commute with `c`, then their product commutes with `c`. -/
@[to_additive (attr := simp)
"If both `a` and `b` commute with `c`, then their product commutes with `c`."]
theorem mul_left (hac : Commute a c) (hbc : Commute b c) : Commute (a * b) c :=
  SemiconjBy.mul_left hac hbc
#align commute.mul_left Commute.mul_leftₓ
#align add_commute.add_left AddCommute.add_leftₓ
-- I think `ₓ` is necessary because of the `mul` vs `HMul` distinction

@[to_additive]
protected theorem right_comm (h : Commute b c) (a : S) : a * b * c = a * c * b := by
  simp only [mul_assoc, h.eq]
#align commute.right_comm Commute.right_commₓ
#align add_commute.right_comm AddCommute.right_commₓ
-- I think `ₓ` is necessary because of the `mul` vs `HMul` distinction

@[to_additive]
protected theorem left_comm (h : Commute a b) (c) : a * (b * c) = b * (a * c) := by
  simp only [← mul_assoc, h.eq]
#align commute.left_comm Commute.left_commₓ
#align add_commute.left_comm AddCommute.left_commₓ
-- I think `ₓ` is necessary because of the `mul` vs `HMul` distinction

@[to_additive]
protected theorem mul_mul_mul_comm (hbc : Commute b c) (a d : S) :
    a * b * (c * d) = a * c * (b * d) := by simp only [hbc.left_comm, mul_assoc]
#align commute.mul_mul_mul_comm Commute.mul_mul_mul_comm
#align add_commute.add_add_add_comm AddCommute.add_add_add_comm

end Semigroup

@[to_additive]
protected theorem all [CommMagma S] (a b : S) : Commute a b :=
  mul_comm a b
#align commute.all Commute.allₓ
#align add_commute.all AddCommute.allₓ
-- not sure why this needs an `ₓ`, maybe instance names not aligned?

section MulOneClass

variable [MulOneClass M]

@[to_additive (attr := simp)]
theorem one_right (a : M) : Commute a 1 :=
  SemiconjBy.one_right a
#align commute.one_right Commute.one_rightₓ
#align add_commute.zero_right AddCommute.zero_rightₓ
-- I think `ₓ` is necessary because `One.toOfNat1` appears in the Lean 4 version

@[to_additive (attr := simp)]
theorem one_left (a : M) : Commute 1 a :=
  SemiconjBy.one_left a
#align commute.one_left Commute.one_leftₓ
#align add_commute.zero_left AddCommute.zero_leftₓ
-- I think `ₓ` is necessary because `One.toOfNat1` appears in the Lean 4 version

end MulOneClass

section Monoid

variable [Monoid M] {a b : M}

@[to_additive (attr := simp)]
theorem pow_right (h : Commute a b) (n : ℕ) : Commute a (b ^ n) :=
  SemiconjBy.pow_right h n
#align commute.pow_right Commute.pow_rightₓ
#align add_commute.nsmul_right AddCommute.nsmul_rightₓ
-- `MulOneClass.toHasMul` vs. `MulOneClass.toMul`

@[to_additive (attr := simp)]
theorem pow_left (h : Commute a b) (n : ℕ) : Commute (a ^ n) b :=
  (h.symm.pow_right n).symm
#align commute.pow_left Commute.pow_leftₓ
#align add_commute.nsmul_left AddCommute.nsmul_leftₓ
-- `MulOneClass.toHasMul` vs. `MulOneClass.toMul`

-- todo: should nat power be called `nsmul` here?
@[to_additive (attr := simp)]
theorem pow_pow (h : Commute a b) (m n : ℕ) : Commute (a ^ m) (b ^ n) :=
  (h.pow_left m).pow_right n
#align commute.pow_pow Commute.pow_powₓ
#align add_commute.nsmul_nsmul AddCommute.nsmul_nsmulₓ
-- `MulOneClass.toHasMul` vs. `MulOneClass.toMul`

-- Porting note: `simpNF` told me to remove the `simp` attribute
@[to_additive]
theorem self_pow (a : M) (n : ℕ) : Commute a (a ^ n) :=
  (Commute.refl a).pow_right n
#align commute.self_pow Commute.self_powₓ
#align add_commute.self_nsmul AddCommute.self_nsmulₓ
-- `MulOneClass.toHasMul` vs. `MulOneClass.toMul`

-- Porting note: `simpNF` told me to remove the `simp` attribute
@[to_additive]
theorem pow_self (a : M) (n : ℕ) : Commute (a ^ n) a :=
  (Commute.refl a).pow_left n
#align add_commute.nsmul_self AddCommute.nsmul_selfₓ
-- `MulOneClass.toHasMul` vs. `MulOneClass.toMul`
#align commute.pow_self Commute.pow_self

-- Porting note: `simpNF` told me to remove the `simp` attribute
@[to_additive]
theorem pow_pow_self (a : M) (m n : ℕ) : Commute (a ^ m) (a ^ n) :=
  (Commute.refl a).pow_pow m n
#align commute.pow_pow_self Commute.pow_pow_selfₓ
#align add_commute.nsmul_nsmul_self AddCommute.nsmul_nsmul_selfₓ
-- `MulOneClass.toHasMul` vs. `MulOneClass.toMul`

@[to_additive] lemma mul_pow (h : Commute a b) : ∀ n, (a * b) ^ n = a ^ n * b ^ n
  | 0 => by rw [pow_zero, pow_zero, pow_zero, one_mul]
  | n + 1 => by simp only [pow_succ', h.mul_pow n, ← mul_assoc, (h.pow_left n).right_comm]
#align commute.mul_pow Commute.mul_pow

end Monoid

section DivisionMonoid

variable [DivisionMonoid G] {a b c d: G}

@[to_additive]
protected theorem mul_inv (hab : Commute a b) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by rw [hab.eq, mul_inv_rev]
#align commute.mul_inv Commute.mul_inv
#align add_commute.add_neg AddCommute.add_neg

@[to_additive]
protected theorem inv (hab : Commute a b) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by rw [hab.eq, mul_inv_rev]
#align commute.inv Commute.inv
#align add_commute.neg AddCommute.neg

@[to_additive AddCommute.zsmul_add]
protected lemma mul_zpow (h : Commute a b) : ∀ n : ℤ, (a * b) ^ n = a ^ n * b ^ n
  | (n : ℕ)    => by simp [zpow_natCast, h.mul_pow n]
  | .negSucc n => by simp [h.mul_pow, (h.pow_pow _ _).eq, mul_inv_rev]
#align commute.mul_zpow Commute.mul_zpow
#align add_commute.zsmul_add AddCommute.zsmul_add

end DivisionMonoid

section Group

variable [Group G] {a b : G}

@[to_additive]
protected theorem mul_inv_cancel (h : Commute a b) : a * b * a⁻¹ = b := by
  rw [h.eq, mul_inv_cancel_right]
#align commute.mul_inv_cancel Commute.mul_inv_cancel
#align add_commute.add_neg_cancel AddCommute.add_neg_cancel

@[to_additive]
theorem mul_inv_cancel_assoc (h : Commute a b) : a * (b * a⁻¹) = b := by
  rw [← mul_assoc, h.mul_inv_cancel]
#align commute.mul_inv_cancel_assoc Commute.mul_inv_cancel_assoc
#align add_commute.add_neg_cancel_assoc AddCommute.add_neg_cancel_assoc

end Group

end Commute

set_option linter.deprecated false

section Monoid
variable [Monoid M]

@[to_additive bit0_nsmul]
lemma pow_bit0 (a : M) (n : ℕ) : a ^ bit0 n = a ^ n * a ^ n := pow_add _ _ _
#align pow_bit0 pow_bit0
#align bit0_nsmul bit0_nsmul

@[to_additive bit1_nsmul]
lemma pow_bit1 (a : M) (n : ℕ) : a ^ bit1 n = a ^ n * a ^ n * a := by rw [bit1, pow_succ, pow_bit0]
#align pow_bit1 pow_bit1
#align bit1_nsmul bit1_nsmul

@[to_additive bit0_nsmul']
lemma pow_bit0' (a : M) (n : ℕ) : a ^ bit0 n = (a * a) ^ n := by
  rw [pow_bit0, (Commute.refl a).mul_pow]
#align pow_bit0' pow_bit0'
#align bit0_nsmul' bit0_nsmul'

@[to_additive bit1_nsmul']
lemma pow_bit1' (a : M) (n : ℕ) : a ^ bit1 n = (a * a) ^ n * a := by rw [bit1, pow_succ, pow_bit0']
#align pow_bit1' pow_bit1'
#align bit1_nsmul' bit1_nsmul'

end Monoid
