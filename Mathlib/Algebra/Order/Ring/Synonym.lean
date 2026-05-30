/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Group.Synonym
public import Mathlib.Algebra.Ring.Defs

/-!
# Ring structure on the order type synonyms

Transfer algebraic instances from `R` to `Rᵒᵈ` and `Lex R`.
-/

public section


variable {R : Type*}

/-! ### Order dual -/

namespace OrderDual

instance [h : Distrib R] : Distrib Rᵒᵈ where
  left_distrib := h.left_distrib
  right_distrib := h.right_distrib

instance [Mul R] [Add R] [h : LeftDistribClass R] : LeftDistribClass Rᵒᵈ where
  left_distrib := h.left_distrib

instance [Mul R] [Add R] [h : RightDistribClass R] : RightDistribClass Rᵒᵈ where
  right_distrib := h.right_distrib

instance [h : NonUnitalNonAssocSemiring R] : NonUnitalNonAssocSemiring Rᵒᵈ where
  zero_mul := h.zero_mul
  mul_zero := h.mul_zero

instance [h : NatCast R] : NatCast Rᵒᵈ := h

instance [h : IntCast R] : IntCast Rᵒᵈ := h

instance [h : AddMonoidWithOne R] : AddMonoidWithOne Rᵒᵈ where
  natCast_zero := h.natCast_zero
  natCast_succ := h.natCast_succ

instance [h : AddCommMonoidWithOne R] : AddCommMonoidWithOne Rᵒᵈ where

instance [h : AddGroupWithOne R] : AddGroupWithOne Rᵒᵈ where
  intCast_ofNat := h.intCast_ofNat
  intCast_negSucc := h.intCast_negSucc

instance [AddCommGroupWithOne R] : AddCommGroupWithOne Rᵒᵈ where

instance [h : NonUnitalSemiring R] : NonUnitalSemiring Rᵒᵈ where

instance [h : NonAssocSemiring R] : NonAssocSemiring Rᵒᵈ where

instance [h : Semiring R] : Semiring Rᵒᵈ where

instance [h : NonUnitalCommSemiring R] : NonUnitalCommSemiring Rᵒᵈ where

instance [h : CommSemiring R] : CommSemiring Rᵒᵈ where

instance [Mul R] [h : HasDistribNeg R] : HasDistribNeg Rᵒᵈ where
  neg_mul := h.neg_mul
  mul_neg := h.mul_neg

instance [h : NonUnitalNonAssocRing R] : NonUnitalNonAssocRing Rᵒᵈ where

instance [h : NonUnitalRing R] : NonUnitalRing Rᵒᵈ where

instance [h : NonAssocRing R] : NonAssocRing Rᵒᵈ where

instance [h : Ring R] : Ring Rᵒᵈ where

instance [h : NonUnitalCommRing R] : NonUnitalCommRing Rᵒᵈ where

instance [h : CommRing R] : CommRing Rᵒᵈ where

instance [Ring R] [h : IsDomain R] : IsDomain Rᵒᵈ where
  mul_left_cancel_of_ne_zero := h.mul_left_cancel_of_ne_zero
  mul_right_cancel_of_ne_zero := h.mul_right_cancel_of_ne_zero

end OrderDual

open OrderDual

@[simp]
theorem toDual_natCast [NatCast R] (n : ℕ) : toDual (n : R) = n :=
  rfl

@[simp]
theorem toDual_ofNat [NatCast R] (n : ℕ) [n.AtLeastTwo] :
    (toDual (ofNat(n) : R)) = ofNat(n) :=
  rfl

@[simp]
theorem ofDual_natCast [NatCast R] (n : ℕ) : (ofDual n : R) = n :=
  rfl

@[simp]
theorem ofDual_ofNat [NatCast R] (n : ℕ) [n.AtLeastTwo] :
    (ofDual (ofNat(n) : Rᵒᵈ)) = ofNat(n) :=
  rfl

@[simp] lemma toDual_intCast [IntCast R] (n : ℤ) : toDual (n : R) = n := rfl

@[simp] lemma ofDual_intCast [IntCast R] (n : ℤ) : (ofDual n : R) = n := rfl

/-! ### Lexicographical order -/

namespace Lex

instance [Distrib R] : Distrib (Lex R) := inferInstanceAs <| Distrib R

instance [Mul R] [Add R] [LeftDistribClass R] : LeftDistribClass (Lex R) :=
  inferInstanceAs <| LeftDistribClass R

instance [Mul R] [Add R] [RightDistribClass R] : RightDistribClass (Lex R) :=
  inferInstanceAs <| RightDistribClass R

instance [NonUnitalNonAssocSemiring R] : NonUnitalNonAssocSemiring (Lex R) :=
  inferInstanceAs <| NonUnitalNonAssocSemiring R

instance [NonUnitalSemiring R] : NonUnitalSemiring (Lex R) := inferInstanceAs <| NonUnitalSemiring R

instance [NatCast R] : NatCast (Lex R) := inferInstanceAs <| NatCast R

instance [IntCast R] : IntCast (Lex R) := inferInstanceAs <| IntCast R

instance [AddMonoidWithOne R] : AddMonoidWithOne (Lex R) := inferInstanceAs <| AddMonoidWithOne R

instance [AddCommMonoidWithOne R] : AddCommMonoidWithOne (Lex R) :=
  inferInstanceAs <| AddCommMonoidWithOne R

instance [AddGroupWithOne R] : AddGroupWithOne (Lex R) := inferInstanceAs <| AddGroupWithOne R

instance [AddCommGroupWithOne R] : AddCommGroupWithOne (Lex R) :=
  inferInstanceAs <| AddCommGroupWithOne R

instance [NonAssocSemiring R] : NonAssocSemiring (Lex R) := inferInstanceAs <| NonAssocSemiring R

instance [Semiring R] : Semiring (Lex R) := inferInstanceAs <| Semiring R

instance [NonUnitalCommSemiring R] : NonUnitalCommSemiring (Lex R) :=
  inferInstanceAs <| NonUnitalCommSemiring R

instance [CommSemiring R] : CommSemiring (Lex R) := inferInstanceAs <| CommSemiring R

instance [Mul R] [HasDistribNeg R] : HasDistribNeg (Lex R) := inferInstanceAs <| HasDistribNeg R

instance [NonUnitalNonAssocRing R] : NonUnitalNonAssocRing (Lex R) :=
  inferInstanceAs <| NonUnitalNonAssocRing R

instance [NonUnitalRing R] : NonUnitalRing (Lex R) := inferInstanceAs <| NonUnitalRing R

instance [NonAssocRing R] : NonAssocRing (Lex R) := inferInstanceAs <| NonAssocRing R

instance [Ring R] : Ring (Lex R) := inferInstanceAs <| Ring R

instance [NonUnitalCommRing R] : NonUnitalCommRing (Lex R) := inferInstanceAs <| NonUnitalCommRing R

instance [CommRing R] : CommRing (Lex R) := inferInstanceAs <| CommRing R

instance [Ring R] [IsDomain R] : IsDomain (Lex R) := inferInstanceAs <| IsDomain R

end Lex

@[simp]
theorem toLex_natCast [NatCast R] (n : ℕ) : toLex (n : R) = n :=
  rfl

@[simp]
theorem toLex_ofNat [NatCast R] (n : ℕ) [n.AtLeastTwo] :
    toLex (ofNat(n) : R) = OfNat.ofNat n :=
  rfl

@[simp]
theorem ofLex_natCast [NatCast R] (n : ℕ) : (ofLex n : R) = n :=
  rfl

@[simp]
theorem ofLex_ofNat [NatCast R] (n : ℕ) [n.AtLeastTwo] :
    ofLex (ofNat(n) : Lex R) = OfNat.ofNat n :=
  rfl
@[simp] lemma toLex_intCast [IntCast R] (n : ℤ) : toLex (n : R) = n := rfl

@[simp] lemma ofLex_intCast [IntCast R] (n : ℤ) : (ofLex n : R) = n := rfl
