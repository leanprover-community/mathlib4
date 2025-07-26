/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies
-/
import Mathlib.Algebra.Order.Group.Synonym
import Mathlib.Algebra.Ring.Defs

/-!
# Ring structure on the order type synonyms

Transfer algebraic instances from `R` to `Rᵒᵈ` and `Lex R`.
-/


variable {R : Type*}

/-! ### Order dual -/


instance [Distrib R] : Distrib Rᵒᵈ where
  left_distrib _ _ _ := congrArg OrderDual.toDual (left_distrib _ _ _)
  right_distrib _ _ _ := congrArg OrderDual.toDual (right_distrib _ _ _)

instance [Mul R] [Add R] [LeftDistribClass R] : LeftDistribClass Rᵒᵈ where
  left_distrib _ _ _ := congrArg OrderDual.toDual (left_distrib _ _ _)

instance [Mul R] [Add R] [RightDistribClass R] : RightDistribClass Rᵒᵈ where
  right_distrib _ _ _ := congrArg OrderDual.toDual (right_distrib _ _ _)

instance [NonUnitalNonAssocSemiring R] : NonUnitalNonAssocSemiring Rᵒᵈ where
  zero_add _ := congrArg OrderDual.toDual (zero_add _)
  add_zero _ := congrArg OrderDual.toDual (add_zero _)
  nsmul n r := .toDual (n • r.ofDual)
  nsmul_zero _ := congrArg OrderDual.toDual (zero_nsmul _)
  nsmul_succ _ _ := congrArg OrderDual.toDual (AddMonoid.nsmul_succ _ _)
  zero_mul _ := congrArg OrderDual.toDual (zero_mul _)
  mul_zero _ := congrArg OrderDual.toDual (mul_zero _)

instance [NonUnitalSemiring R] : NonUnitalSemiring Rᵒᵈ where

instance [NonAssocSemiring R] : NonAssocSemiring Rᵒᵈ where

instance [Semiring R] : Semiring Rᵒᵈ where

instance [NonUnitalCommSemiring R] : NonUnitalCommSemiring Rᵒᵈ where

instance [CommSemiring R] : CommSemiring Rᵒᵈ where

instance [Mul R] [HasDistribNeg R] : HasDistribNeg Rᵒᵈ where
  neg_mul _ _ := congrArg OrderDual.toDual (neg_mul _ _)
  mul_neg _ _ := congrArg OrderDual.toDual (mul_neg _ _)

instance [NonUnitalNonAssocRing R] : NonUnitalNonAssocRing Rᵒᵈ where

instance [NonUnitalRing R] : NonUnitalRing Rᵒᵈ where

instance [NonAssocRing R] : NonAssocRing Rᵒᵈ where

instance [Ring R] : Ring Rᵒᵈ where
  __ : Semiring (Rᵒᵈ) := inferInstance
  __ : AddGroup (Rᵒᵈ) := inferInstance

instance [NonUnitalCommRing R] : NonUnitalCommRing Rᵒᵈ where

instance [CommRing R] : CommRing Rᵒᵈ where

instance [Ring R] [IsDomain R] : IsDomain Rᵒᵈ where
  mul_left_cancel_of_ne_zero hzero h :=
    congrArg OrderDual.toDual (mul_left_cancel₀ (hzero ∘ congrArg OrderDual.toDual)
      (congrArg OrderDual.ofDual h))
  mul_right_cancel_of_ne_zero hzero h :=
    congrArg OrderDual.toDual (mul_right_cancel₀ (hzero ∘ congrArg OrderDual.toDual)
      (congrArg OrderDual.ofDual h))


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
