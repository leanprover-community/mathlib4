/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Synonym
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Nat.Cast.Synonym

/-!
# Ring structure on the order type synonyms

Transfer algebraic instances from `R` to `Rᵒᵈ` and `Lex R`.
-/

@[expose] public section


variable {R : Type*}

/-! ### Order dual -/


instance [h : Distrib R] : Distrib Rᵒᵈ where
  left_distrib := h.left_distrib
  right_distrib := h.right_distrib

instance [Mul R] [Add R] [h : LeftDistribClass R] : LeftDistribClass Rᵒᵈ := h

instance [Mul R] [Add R] [h : RightDistribClass R] : RightDistribClass Rᵒᵈ := h

instance [h : NonUnitalNonAssocSemiring R] : NonUnitalNonAssocSemiring Rᵒᵈ where
  zero_mul := h.zero_mul
  mul_zero := h.mul_zero

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
  intCast n := .toDual n
  intCast_ofNat := h.intCast_ofNat
  intCast_negSucc := h.intCast_negSucc

instance [h : Ring R] : Ring Rᵒᵈ where

instance [h : NonUnitalCommRing R] : NonUnitalCommRing Rᵒᵈ where

instance [h : CommRing R] : CommRing Rᵒᵈ where

instance [Ring R] [h : IsDomain R] : IsDomain Rᵒᵈ where
  mul_left_cancel_of_ne_zero := h.mul_left_cancel_of_ne_zero
  mul_right_cancel_of_ne_zero := h.mul_right_cancel_of_ne_zero

/-! ### Lexicographical order -/


instance [h : Distrib R] : Distrib (Lex R) := h

instance [Mul R] [Add R] [h : LeftDistribClass R] : LeftDistribClass (Lex R) := h

instance [Mul R] [Add R] [h : RightDistribClass R] : RightDistribClass (Lex R) := h

instance [h : NonUnitalNonAssocSemiring R] : NonUnitalNonAssocSemiring (Lex R) := h

instance [h : NonUnitalSemiring R] : NonUnitalSemiring (Lex R) := h

instance [h : NonAssocSemiring R] : NonAssocSemiring (Lex R) := h

instance [h : Semiring R] : Semiring (Lex R) := h

instance [h : NonUnitalCommSemiring R] : NonUnitalCommSemiring (Lex R) := h

instance [h : CommSemiring R] : CommSemiring (Lex R) := h

instance [Mul R] [h : HasDistribNeg R] : HasDistribNeg (Lex R) := h

instance [h : NonUnitalNonAssocRing R] : NonUnitalNonAssocRing (Lex R) := h

instance [h : NonUnitalRing R] : NonUnitalRing (Lex R) := h

instance [h : NonAssocRing R] : NonAssocRing (Lex R) := h

instance [h : Ring R] : Ring (Lex R) := h

instance [h : NonUnitalCommRing R] : NonUnitalCommRing (Lex R) := h

instance [h : CommRing R] : CommRing (Lex R) := h

instance [Ring R] [h : IsDomain R] : IsDomain (Lex R) := h
