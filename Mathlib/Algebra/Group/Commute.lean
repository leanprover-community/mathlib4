/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland, Yury Kudryashov
-/
import Mathbin.Algebra.Group.Semiconj

/-!
# Commuting pairs of elements in monoids

We define the predicate `commute a b := a * b = b * a` and provide some operations on terms `(h :
commute a b)`. E.g., if `a`, `b`, and c are elements of a semiring, and that `hb : commute a b` and
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

#print Commute /-
/-- Two elements commute if `a * b = b * a`. -/
@[to_additive AddCommute "Two elements additively commute if `a + b = b + a`"]
def Commute {S : Type _} [Mul S] (a b : S) : Prop :=
  SemiconjBy a b b
#align commute Commute
-/

namespace Commute

section Mul

variable {S : Type _} [Mul S]

#print Commute.eq /-
/-- Equality behind `commute a b`; useful for rewriting. -/
@[to_additive "Equality behind `add_commute a b`; useful for rewriting."]
protected theorem eq {a b : S} (h : Commute a b) : a * b = b * a :=
  h
#align commute.eq Commute.eq
-/

#print Commute.refl /-
/-- Any element commutes with itself. -/
@[refl, simp, to_additive "Any element commutes with itself."]
protected theorem refl (a : S) : Commute a a :=
  Eq.refl (a * a)
#align commute.refl Commute.refl
-/

#print Commute.symm /-
/-- If `a` commutes with `b`, then `b` commutes with `a`. -/
@[symm, to_additive "If `a` commutes with `b`, then `b` commutes with `a`."]
protected theorem symm {a b : S} (h : Commute a b) : Commute b a :=
  Eq.symm h
#align commute.symm Commute.symm
-/

#print Commute.semiconjBy /-
@[to_additive]
protected theorem semiconjBy {a b : S} (h : Commute a b) : SemiconjBy a b b :=
  h
#align commute.semiconj_by Commute.semiconjBy
-/

#print Commute.symm_iff /-
@[to_additive]
protected theorem symm_iff {a b : S} : Commute a b ↔ Commute b a :=
  ⟨Commute.symm, Commute.symm⟩
#align commute.symm_iff Commute.symm_iff
-/

@[to_additive]
instance : IsRefl S Commute :=
  ⟨Commute.refl⟩

-- This instance is useful for `finset.noncomm_prod`
@[to_additive]
instance on_is_refl {f : G → S} : IsRefl G fun a b => Commute (f a) (f b) :=
  ⟨fun _ => Commute.refl _⟩
#align commute.on_is_refl Commute.on_is_refl

end Mul

section Semigroup

variable {S : Type _} [Semigroup S] {a b c : S}

/- warning: commute.mul_right -> Commute.mul_right is a dubious translation:
lean 3 declaration is
  forall {S : Type.{u_2}} [_inst_1 : Semigroup.{u_2} S] {a : S} {b : S} {c : S}, (Commute.{u_2} S (Semigroup.toHasMul.{u_2} S _inst_1) a b) -> (Commute.{u_2} S (Semigroup.toHasMul.{u_2} S _inst_1) a c) -> (Commute.{u_2} S (Semigroup.toHasMul.{u_2} S _inst_1) a (HMul.hMul.{u_2 u_2 u_2} S S S (instHMul.{u_2} S (Semigroup.toHasMul.{u_2} S _inst_1)) b c))
but is expected to have type
  forall {S : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Commute._hyg.141 : Semigroup.{u_1} S] {a : S} {b : S} {c : S}, (Commute.{u_1} S (Semigroup.toMul.{u_1} S inst._@.Mathlib.Algebra.Group.Commute._hyg.141) a b) -> (Commute.{u_1} S (Semigroup.toMul.{u_1} S inst._@.Mathlib.Algebra.Group.Commute._hyg.141) a c) -> (Commute.{u_1} S (Semigroup.toMul.{u_1} S inst._@.Mathlib.Algebra.Group.Commute._hyg.141) a (HMul.hMul.{u_1 u_1 u_1} S S S (instHMul.{u_1} S (Semigroup.toMul.{u_1} S inst._@.Mathlib.Algebra.Group.Commute._hyg.141)) b c))
Case conversion may be inaccurate. Consider using '#align commute.mul_right Commute.mul_rightₓ'. -/
/-- If `a` commutes with both `b` and `c`, then it commutes with their product. -/
@[simp, to_additive "If `a` commutes with both `b` and `c`, then it commutes with their sum."]
theorem mul_right (hab : Commute a b) (hac : Commute a c) : Commute a (b * c) :=
  hab.mul_right hac
#align commute.mul_right Commute.mul_right

/- warning: commute.mul_left -> Commute.mul_left is a dubious translation:
lean 3 declaration is
  forall {S : Type.{u_2}} [_inst_1 : Semigroup.{u_2} S] {a : S} {b : S} {c : S}, (Commute.{u_2} S (Semigroup.toHasMul.{u_2} S _inst_1) a c) -> (Commute.{u_2} S (Semigroup.toHasMul.{u_2} S _inst_1) b c) -> (Commute.{u_2} S (Semigroup.toHasMul.{u_2} S _inst_1) (HMul.hMul.{u_2 u_2 u_2} S S S (instHMul.{u_2} S (Semigroup.toHasMul.{u_2} S _inst_1)) a b) c)
but is expected to have type
  forall {S : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Commute._hyg.168 : Semigroup.{u_1} S] {a : S} {b : S} {c : S}, (Commute.{u_1} S (Semigroup.toMul.{u_1} S inst._@.Mathlib.Algebra.Group.Commute._hyg.168) a c) -> (Commute.{u_1} S (Semigroup.toMul.{u_1} S inst._@.Mathlib.Algebra.Group.Commute._hyg.168) b c) -> (Commute.{u_1} S (Semigroup.toMul.{u_1} S inst._@.Mathlib.Algebra.Group.Commute._hyg.168) (HMul.hMul.{u_1 u_1 u_1} S S S (instHMul.{u_1} S (Semigroup.toMul.{u_1} S inst._@.Mathlib.Algebra.Group.Commute._hyg.168)) a b) c)
Case conversion may be inaccurate. Consider using '#align commute.mul_left Commute.mul_leftₓ'. -/
/-- If both `a` and `b` commute with `c`, then their product commutes with `c`. -/
@[simp, to_additive "If both `a` and `b` commute with `c`, then their product commutes with `c`."]
theorem mul_left (hac : Commute a c) (hbc : Commute b c) : Commute (a * b) c :=
  hac.mul_left hbc
#align commute.mul_left Commute.mul_left

/- warning: commute.right_comm -> Commute.right_comm is a dubious translation:
lean 3 declaration is
  forall {S : Type.{u_2}} [_inst_1 : Semigroup.{u_2} S] {b : S} {c : S}, (Commute.{u_2} S (Semigroup.toHasMul.{u_2} S _inst_1) b c) -> (forall (a : S), Eq.{succ u_2} S (HMul.hMul.{u_2 u_2 u_2} S S S (instHMul.{u_2} S (Semigroup.toHasMul.{u_2} S _inst_1)) (HMul.hMul.{u_2 u_2 u_2} S S S (instHMul.{u_2} S (Semigroup.toHasMul.{u_2} S _inst_1)) a b) c) (HMul.hMul.{u_2 u_2 u_2} S S S (instHMul.{u_2} S (Semigroup.toHasMul.{u_2} S _inst_1)) (HMul.hMul.{u_2 u_2 u_2} S S S (instHMul.{u_2} S (Semigroup.toHasMul.{u_2} S _inst_1)) a c) b))
but is expected to have type
  forall {S : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Commute._hyg.195 : Semigroup.{u_1} S] {b : S} {c : S}, (Commute.{u_1} S (Semigroup.toMul.{u_1} S inst._@.Mathlib.Algebra.Group.Commute._hyg.195) b c) -> (forall (a : S), Eq.{succ u_1} S (HMul.hMul.{u_1 u_1 u_1} S S S (instHMul.{u_1} S (Semigroup.toMul.{u_1} S inst._@.Mathlib.Algebra.Group.Commute._hyg.195)) (HMul.hMul.{u_1 u_1 u_1} S S S (instHMul.{u_1} S (Semigroup.toMul.{u_1} S inst._@.Mathlib.Algebra.Group.Commute._hyg.195)) a b) c) (HMul.hMul.{u_1 u_1 u_1} S S S (instHMul.{u_1} S (Semigroup.toMul.{u_1} S inst._@.Mathlib.Algebra.Group.Commute._hyg.195)) (HMul.hMul.{u_1 u_1 u_1} S S S (instHMul.{u_1} S (Semigroup.toMul.{u_1} S inst._@.Mathlib.Algebra.Group.Commute._hyg.195)) a c) b))
Case conversion may be inaccurate. Consider using '#align commute.right_comm Commute.right_commₓ'. -/
@[to_additive]
protected theorem right_comm (h : Commute b c) (a : S) : a * b * c = a * c * b := by simp only [mul_assoc, h.eq]
#align commute.right_comm Commute.right_comm

/- warning: commute.left_comm -> Commute.left_comm is a dubious translation:
lean 3 declaration is
  forall {S : Type.{u_2}} [_inst_1 : Semigroup.{u_2} S] {a : S} {b : S}, (Commute.{u_2} S (Semigroup.toHasMul.{u_2} S _inst_1) a b) -> (forall (c : S), Eq.{succ u_2} S (HMul.hMul.{u_2 u_2 u_2} S S S (instHMul.{u_2} S (Semigroup.toHasMul.{u_2} S _inst_1)) a (HMul.hMul.{u_2 u_2 u_2} S S S (instHMul.{u_2} S (Semigroup.toHasMul.{u_2} S _inst_1)) b c)) (HMul.hMul.{u_2 u_2 u_2} S S S (instHMul.{u_2} S (Semigroup.toHasMul.{u_2} S _inst_1)) b (HMul.hMul.{u_2 u_2 u_2} S S S (instHMul.{u_2} S (Semigroup.toHasMul.{u_2} S _inst_1)) a c)))
but is expected to have type
  forall {S : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Commute._hyg.226 : Semigroup.{u_1} S] {a : S} {b : S}, (Commute.{u_1} S (Semigroup.toMul.{u_1} S inst._@.Mathlib.Algebra.Group.Commute._hyg.226) a b) -> (forall (c : S), Eq.{succ u_1} S (HMul.hMul.{u_1 u_1 u_1} S S S (instHMul.{u_1} S (Semigroup.toMul.{u_1} S inst._@.Mathlib.Algebra.Group.Commute._hyg.226)) a (HMul.hMul.{u_1 u_1 u_1} S S S (instHMul.{u_1} S (Semigroup.toMul.{u_1} S inst._@.Mathlib.Algebra.Group.Commute._hyg.226)) b c)) (HMul.hMul.{u_1 u_1 u_1} S S S (instHMul.{u_1} S (Semigroup.toMul.{u_1} S inst._@.Mathlib.Algebra.Group.Commute._hyg.226)) b (HMul.hMul.{u_1 u_1 u_1} S S S (instHMul.{u_1} S (Semigroup.toMul.{u_1} S inst._@.Mathlib.Algebra.Group.Commute._hyg.226)) a c)))
Case conversion may be inaccurate. Consider using '#align commute.left_comm Commute.left_commₓ'. -/
@[to_additive]
protected theorem left_comm (h : Commute a b) (c) : a * (b * c) = b * (a * c) := by simp only [← mul_assoc, h.eq]
#align commute.left_comm Commute.left_comm

end Semigroup

/- warning: commute.all -> Commute.all is a dubious translation:
lean 3 declaration is
  forall {S : Type.{u_1}} [_inst_1 : CommSemigroup.{u_1} S] (a : S) (b : S), Commute.{u_1} S (Semigroup.toHasMul.{u_1} S (CommSemigroup.toSemigroup.{u_1} S _inst_1)) a b
but is expected to have type
  forall {S : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Commute._hyg.258 : CommSemigroup.{u_1} S] (a : S) (b : S), Commute.{u_1} S (Semigroup.toMul.{u_1} S (CommSemigroup.toSemigroup.{u_1} S inst._@.Mathlib.Algebra.Group.Commute._hyg.258)) a b
Case conversion may be inaccurate. Consider using '#align commute.all Commute.allₓ'. -/
@[to_additive]
protected theorem all {S : Type _} [CommSemigroup S] (a b : S) : Commute a b :=
  mul_comm a b
#align commute.all Commute.all

section MulOneClass

variable {M : Type _} [MulOneClass M]

/- warning: commute.one_right -> Commute.one_right is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_2}} [_inst_1 : MulOneClass.{u_2} M] (a : M), Commute.{u_2} M (MulOneClass.toHasMul.{u_2} M _inst_1) a (OfNat.ofNat.{u_2} M 1 (OfNat.mk.{u_2} M 1 (One.one.{u_2} M (MulOneClass.toHasOne.{u_2} M _inst_1))))
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Commute._hyg.281 : MulOneClass.{u_1} M] (a : M), Commute.{u_1} M (MulOneClass.toMul.{u_1} M inst._@.Mathlib.Algebra.Group.Commute._hyg.281) a (OfNat.ofNat.{u_1} M 1 (One.toOfNat1.{u_1} M (MulOneClass.toOne.{u_1} M inst._@.Mathlib.Algebra.Group.Commute._hyg.281)))
Case conversion may be inaccurate. Consider using '#align commute.one_right Commute.one_rightₓ'. -/
@[simp, to_additive]
theorem one_right (a : M) : Commute a 1 :=
  SemiconjBy.one_right a
#align commute.one_right Commute.one_right

/- warning: commute.one_left -> Commute.one_left is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_2}} [_inst_1 : MulOneClass.{u_2} M] (a : M), Commute.{u_2} M (MulOneClass.toHasMul.{u_2} M _inst_1) (OfNat.ofNat.{u_2} M 1 (OfNat.mk.{u_2} M 1 (One.one.{u_2} M (MulOneClass.toHasOne.{u_2} M _inst_1)))) a
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Commute._hyg.293 : MulOneClass.{u_1} M] (a : M), Commute.{u_1} M (MulOneClass.toMul.{u_1} M inst._@.Mathlib.Algebra.Group.Commute._hyg.293) (OfNat.ofNat.{u_1} M 1 (One.toOfNat1.{u_1} M (MulOneClass.toOne.{u_1} M inst._@.Mathlib.Algebra.Group.Commute._hyg.293))) a
Case conversion may be inaccurate. Consider using '#align commute.one_left Commute.one_leftₓ'. -/
@[simp, to_additive]
theorem one_left (a : M) : Commute 1 a :=
  SemiconjBy.one_left a
#align commute.one_left Commute.one_left

end MulOneClass

section Monoid

variable {M : Type _} [Monoid M] {a b : M} {u u₁ u₂ : Mˣ}

/- warning: commute.pow_right -> Commute.pow_right is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_2}} [_inst_1 : Monoid.{u_2} M] {a : M} {b : M}, (Commute.{u_2} M (MulOneClass.toHasMul.{u_2} M (Monoid.toMulOneClass.{u_2} M _inst_1)) a b) -> (forall (n : Nat), Commute.{u_2} M (MulOneClass.toHasMul.{u_2} M (Monoid.toMulOneClass.{u_2} M _inst_1)) a (HPow.hPow.{u_2 0 u_2} M Nat M (instHPow.{u_2 0} M Nat (Monoid.hasPow.{u_2} M _inst_1)) b n))
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Commute._hyg.319 : Monoid.{u_1} M] {a : M} {b : M}, (Commute.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Commute._hyg.319)) a b) -> (forall (n : Nat), Commute.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Commute._hyg.319)) a (HPow.hPow.{u_1 0 u_1} M Nat M (instHPow.{u_1 0} M Nat (Monoid.Pow.{u_1} M inst._@.Mathlib.Algebra.Group.Commute._hyg.319)) b n))
Case conversion may be inaccurate. Consider using '#align commute.pow_right Commute.pow_rightₓ'. -/
@[simp, to_additive]
theorem pow_right (h : Commute a b) (n : ℕ) : Commute a (b ^ n) :=
  h.pow_right n
#align commute.pow_right Commute.pow_right

/- warning: commute.pow_left -> Commute.pow_left is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_2}} [_inst_1 : Monoid.{u_2} M] {a : M} {b : M}, (Commute.{u_2} M (MulOneClass.toHasMul.{u_2} M (Monoid.toMulOneClass.{u_2} M _inst_1)) a b) -> (forall (n : Nat), Commute.{u_2} M (MulOneClass.toHasMul.{u_2} M (Monoid.toMulOneClass.{u_2} M _inst_1)) (HPow.hPow.{u_2 0 u_2} M Nat M (instHPow.{u_2 0} M Nat (Monoid.hasPow.{u_2} M _inst_1)) a n) b)
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Commute._hyg.345 : Monoid.{u_1} M] {a : M} {b : M}, (Commute.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Commute._hyg.345)) a b) -> (forall (n : Nat), Commute.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Commute._hyg.345)) (HPow.hPow.{u_1 0 u_1} M Nat M (instHPow.{u_1 0} M Nat (Monoid.Pow.{u_1} M inst._@.Mathlib.Algebra.Group.Commute._hyg.345)) a n) b)
Case conversion may be inaccurate. Consider using '#align commute.pow_left Commute.pow_leftₓ'. -/
@[simp, to_additive]
theorem pow_left (h : Commute a b) (n : ℕ) : Commute (a ^ n) b :=
  (h.symm.pow_right n).symm
#align commute.pow_left Commute.pow_left

/- warning: commute.pow_pow -> Commute.pow_pow is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_2}} [_inst_1 : Monoid.{u_2} M] {a : M} {b : M}, (Commute.{u_2} M (MulOneClass.toHasMul.{u_2} M (Monoid.toMulOneClass.{u_2} M _inst_1)) a b) -> (forall (m : Nat) (n : Nat), Commute.{u_2} M (MulOneClass.toHasMul.{u_2} M (Monoid.toMulOneClass.{u_2} M _inst_1)) (HPow.hPow.{u_2 0 u_2} M Nat M (instHPow.{u_2 0} M Nat (Monoid.hasPow.{u_2} M _inst_1)) a m) (HPow.hPow.{u_2 0 u_2} M Nat M (instHPow.{u_2 0} M Nat (Monoid.hasPow.{u_2} M _inst_1)) b n))
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Commute._hyg.373 : Monoid.{u_1} M] {a : M} {b : M}, (Commute.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Commute._hyg.373)) a b) -> (forall (m : Nat) (n : Nat), Commute.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Commute._hyg.373)) (HPow.hPow.{u_1 0 u_1} M Nat M (instHPow.{u_1 0} M Nat (Monoid.Pow.{u_1} M inst._@.Mathlib.Algebra.Group.Commute._hyg.373)) a m) (HPow.hPow.{u_1 0 u_1} M Nat M (instHPow.{u_1 0} M Nat (Monoid.Pow.{u_1} M inst._@.Mathlib.Algebra.Group.Commute._hyg.373)) b n))
Case conversion may be inaccurate. Consider using '#align commute.pow_pow Commute.pow_powₓ'. -/
@[simp, to_additive]
theorem pow_pow (h : Commute a b) (m n : ℕ) : Commute (a ^ m) (b ^ n) :=
  (h.pow_left m).pow_right n
#align commute.pow_pow Commute.pow_pow

/- warning: commute.self_pow -> Commute.self_pow is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_2}} [_inst_1 : Monoid.{u_2} M] (a : M) (n : Nat), Commute.{u_2} M (MulOneClass.toHasMul.{u_2} M (Monoid.toMulOneClass.{u_2} M _inst_1)) a (HPow.hPow.{u_2 0 u_2} M Nat M (instHPow.{u_2 0} M Nat (Monoid.hasPow.{u_2} M _inst_1)) a n)
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Commute._hyg.411 : Monoid.{u_1} M] (a : M) (n : Nat), Commute.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Commute._hyg.411)) a (HPow.hPow.{u_1 0 u_1} M Nat M (instHPow.{u_1 0} M Nat (Monoid.Pow.{u_1} M inst._@.Mathlib.Algebra.Group.Commute._hyg.411)) a n)
Case conversion may be inaccurate. Consider using '#align commute.self_pow Commute.self_powₓ'. -/
@[simp, to_additive]
theorem self_pow (a : M) (n : ℕ) : Commute a (a ^ n) :=
  (Commute.refl a).pow_right n
#align commute.self_pow Commute.self_pow

/- warning: commute.pow_self -> Commute.pow_self is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_2}} [_inst_1 : Monoid.{u_2} M] (a : M) (n : Nat), Commute.{u_2} M (MulOneClass.toHasMul.{u_2} M (Monoid.toMulOneClass.{u_2} M _inst_1)) (HPow.hPow.{u_2 0 u_2} M Nat M (instHPow.{u_2 0} M Nat (Monoid.hasPow.{u_2} M _inst_1)) a n) a
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Commute._hyg.438 : Monoid.{u_1} M] (a : M) (n : Nat), Commute.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Commute._hyg.438)) (HPow.hPow.{u_1 0 u_1} M Nat M (instHPow.{u_1 0} M Nat (Monoid.Pow.{u_1} M inst._@.Mathlib.Algebra.Group.Commute._hyg.438)) a n) a
Case conversion may be inaccurate. Consider using '#align commute.pow_self Commute.pow_selfₓ'. -/
@[simp, to_additive]
theorem pow_self (a : M) (n : ℕ) : Commute (a ^ n) a :=
  (Commute.refl a).pow_left n
#align commute.pow_self Commute.pow_self

/- warning: commute.pow_pow_self -> Commute.pow_pow_self is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_2}} [_inst_1 : Monoid.{u_2} M] (a : M) (m : Nat) (n : Nat), Commute.{u_2} M (MulOneClass.toHasMul.{u_2} M (Monoid.toMulOneClass.{u_2} M _inst_1)) (HPow.hPow.{u_2 0 u_2} M Nat M (instHPow.{u_2 0} M Nat (Monoid.hasPow.{u_2} M _inst_1)) a m) (HPow.hPow.{u_2 0 u_2} M Nat M (instHPow.{u_2 0} M Nat (Monoid.hasPow.{u_2} M _inst_1)) a n)
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Commute._hyg.465 : Monoid.{u_1} M] (a : M) (m : Nat) (n : Nat), Commute.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Commute._hyg.465)) (HPow.hPow.{u_1 0 u_1} M Nat M (instHPow.{u_1 0} M Nat (Monoid.Pow.{u_1} M inst._@.Mathlib.Algebra.Group.Commute._hyg.465)) a m) (HPow.hPow.{u_1 0 u_1} M Nat M (instHPow.{u_1 0} M Nat (Monoid.Pow.{u_1} M inst._@.Mathlib.Algebra.Group.Commute._hyg.465)) a n)
Case conversion may be inaccurate. Consider using '#align commute.pow_pow_self Commute.pow_pow_selfₓ'. -/
@[simp, to_additive]
theorem pow_pow_self (a : M) (m n : ℕ) : Commute (a ^ m) (a ^ n) :=
  (Commute.refl a).pow_pow m n
#align commute.pow_pow_self Commute.pow_pow_self

@[to_additive succ_nsmul']
theorem _root_.pow_succ' (a : M) (n : ℕ) : a ^ (n + 1) = a ^ n * a :=
  (pow_succ a n).trans (self_pow _ _)
#align commute._root_.pow_succ' commute._root_.pow_succ'

@[to_additive]
theorem units_inv_right : Commute a u → Commute a ↑u⁻¹ :=
  SemiconjBy.units_inv_right
#align commute.units_inv_right Commute.units_inv_right

@[simp, to_additive]
theorem units_inv_right_iff : Commute a ↑u⁻¹ ↔ Commute a u :=
  SemiconjBy.units_inv_right_iff
#align commute.units_inv_right_iff Commute.units_inv_right_iff

@[to_additive]
theorem units_inv_left : Commute (↑u) a → Commute (↑u⁻¹) a :=
  SemiconjBy.units_inv_symm_left
#align commute.units_inv_left Commute.units_inv_left

@[simp, to_additive]
theorem units_inv_left_iff : Commute (↑u⁻¹) a ↔ Commute (↑u) a :=
  SemiconjBy.units_inv_symm_left_iff
#align commute.units_inv_left_iff Commute.units_inv_left_iff

@[to_additive]
theorem units_coe : Commute u₁ u₂ → Commute (u₁ : M) u₂ :=
  SemiconjBy.units_coe
#align commute.units_coe Commute.units_coe

@[to_additive]
theorem units_of_coe : Commute (u₁ : M) u₂ → Commute u₁ u₂ :=
  SemiconjBy.units_of_coe
#align commute.units_of_coe Commute.units_of_coe

@[simp, to_additive]
theorem units_coe_iff : Commute (u₁ : M) u₂ ↔ Commute u₁ u₂ :=
  SemiconjBy.units_coe_iff
#align commute.units_coe_iff Commute.units_coe_iff

/-- If the product of two commuting elements is a unit, then the left multiplier is a unit. -/
@[to_additive "If the sum of two commuting elements is an additive unit, then the left summand is an\nadditive unit."]
def _root_.units.left_of_mul (u : Mˣ) (a b : M) (hu : a * b = u) (hc : Commute a b) : Mˣ where
  val := a
  inv := b * ↑u⁻¹
  val_inv := by rw [← mul_assoc, hu, u.mul_inv]
  inv_val := by
    have : Commute a u := hu ▸ (Commute.refl _).mul_right hc
    rw [← this.units_inv_right.right_comm, ← hc.eq, hu, u.mul_inv]
#align commute._root_.units.left_of_mul commute._root_.units.left_of_mul

/-- If the product of two commuting elements is a unit, then the right multiplier is a unit. -/
@[to_additive "If the sum of two commuting elements is an additive unit, then the right summand is\nan additive unit."]
def _root_.units.right_of_mul (u : Mˣ) (a b : M) (hu : a * b = u) (hc : Commute a b) : Mˣ :=
  u.leftOfMul b a (hc.Eq ▸ hu) hc.symm
#align commute._root_.units.right_of_mul commute._root_.units.right_of_mul

@[to_additive]
theorem is_unit_mul_iff (h : Commute a b) : IsUnit (a * b) ↔ IsUnit a ∧ IsUnit b :=
  ⟨fun ⟨u, hu⟩ => ⟨(u.leftOfMul a b hu.symm h).IsUnit, (u.rightOfMul a b hu.symm h).IsUnit⟩, fun H => H.1.mul H.2⟩
#align commute.is_unit_mul_iff Commute.is_unit_mul_iff

@[simp, to_additive]
theorem _root_.is_unit_mul_self_iff : IsUnit (a * a) ↔ IsUnit a :=
  (Commute.refl a).is_unit_mul_iff.trans (and_self_iff _)
#align commute._root_.is_unit_mul_self_iff commute._root_.is_unit_mul_self_iff

end Monoid

section DivisionMonoid

variable [DivisionMonoid G] {a b : G}

@[to_additive]
theorem inv_inv : Commute a b → Commute a⁻¹ b⁻¹ :=
  SemiconjBy.inv_inv_symm
#align commute.inv_inv Commute.inv_inv

@[simp, to_additive]
theorem inv_inv_iff : Commute a⁻¹ b⁻¹ ↔ Commute a b :=
  SemiconjBy.inv_inv_symm_iff
#align commute.inv_inv_iff Commute.inv_inv_iff

end DivisionMonoid

section Group

variable [Group G] {a b : G}

@[to_additive]
theorem inv_right : Commute a b → Commute a b⁻¹ :=
  SemiconjBy.inv_right
#align commute.inv_right Commute.inv_right

@[simp, to_additive]
theorem inv_right_iff : Commute a b⁻¹ ↔ Commute a b :=
  SemiconjBy.inv_right_iff
#align commute.inv_right_iff Commute.inv_right_iff

@[to_additive]
theorem inv_left : Commute a b → Commute a⁻¹ b :=
  SemiconjBy.inv_symm_left
#align commute.inv_left Commute.inv_left

@[simp, to_additive]
theorem inv_left_iff : Commute a⁻¹ b ↔ Commute a b :=
  SemiconjBy.inv_symm_left_iff
#align commute.inv_left_iff Commute.inv_left_iff

@[to_additive]
protected theorem inv_mul_cancel (h : Commute a b) : a⁻¹ * b * a = b := by rw [h.inv_left.eq, inv_mul_cancel_right]
#align commute.inv_mul_cancel Commute.inv_mul_cancel

@[to_additive]
theorem inv_mul_cancel_assoc (h : Commute a b) : a⁻¹ * (b * a) = b := by rw [← mul_assoc, h.inv_mul_cancel]
#align commute.inv_mul_cancel_assoc Commute.inv_mul_cancel_assoc

@[to_additive]
protected theorem mul_inv_cancel (h : Commute a b) : a * b * a⁻¹ = b := by rw [h.eq, mul_inv_cancel_right]
#align commute.mul_inv_cancel Commute.mul_inv_cancel

@[to_additive]
theorem mul_inv_cancel_assoc (h : Commute a b) : a * (b * a⁻¹) = b := by rw [← mul_assoc, h.mul_inv_cancel]
#align commute.mul_inv_cancel_assoc Commute.mul_inv_cancel_assoc

end Group

end Commute

section CommGroup

variable [CommGroup G] (a b : G)

@[simp, to_additive]
theorem mul_inv_cancel_comm : a * b * a⁻¹ = b :=
  (Commute.all a b).mul_inv_cancel
#align mul_inv_cancel_comm mul_inv_cancel_comm

@[simp, to_additive]
theorem mul_inv_cancel_comm_assoc : a * (b * a⁻¹) = b :=
  (Commute.all a b).mul_inv_cancel_assoc
#align mul_inv_cancel_comm_assoc mul_inv_cancel_comm_assoc

@[simp, to_additive]
theorem inv_mul_cancel_comm : a⁻¹ * b * a = b :=
  (Commute.all a b).inv_mul_cancel
#align inv_mul_cancel_comm inv_mul_cancel_comm

@[simp, to_additive]
theorem inv_mul_cancel_comm_assoc : a⁻¹ * (b * a) = b :=
  (Commute.all a b).inv_mul_cancel_assoc
#align inv_mul_cancel_comm_assoc inv_mul_cancel_comm_assoc

end CommGroup

