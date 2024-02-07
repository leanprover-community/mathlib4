/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.OrderSynonym

#align_import algebra.ring.order_synonym from "leanprover-community/mathlib"@"d6aae1bcbd04b8de2022b9b83a5b5b10e10c777d"

/-!
# Ring structure on the order type synonyms

Transfer algebraic instances from `α` to `αᵒᵈ` and `Lex α`.
-/


variable {α : Type*}

/-! ### Order dual -/


instance (priority := 10000) [h : Distrib α] : Distrib αᵒᵈ := h

instance (priority := 10000) [Mul α] [Add α] [h : LeftDistribClass α] : LeftDistribClass αᵒᵈ := h

instance (priority := 10000) [Mul α] [Add α] [h : RightDistribClass α] : RightDistribClass αᵒᵈ := h

instance (priority := 10000) [h : NonUnitalNonAssocSemiring α] : NonUnitalNonAssocSemiring αᵒᵈ := h

instance (priority := 10000) [h : NonUnitalSemiring α] : NonUnitalSemiring αᵒᵈ := h

instance (priority := 10000) [h : NonAssocSemiring α] : NonAssocSemiring αᵒᵈ := h

instance (priority := 10000) [h : Semiring α] : Semiring αᵒᵈ := h

instance (priority := 10000) [h : NonUnitalCommSemiring α] : NonUnitalCommSemiring αᵒᵈ := h

instance (priority := 10000) [h : CommSemiring α] : CommSemiring αᵒᵈ := h

instance (priority := 10000) [Mul α] [h : HasDistribNeg α] : HasDistribNeg αᵒᵈ := h

instance (priority := 10000) [h : NonUnitalNonAssocRing α] : NonUnitalNonAssocRing αᵒᵈ := h

instance (priority := 10000) [h : NonUnitalRing α] : NonUnitalRing αᵒᵈ := h

instance (priority := 10000) [h : NonAssocRing α] : NonAssocRing αᵒᵈ := h

instance (priority := 10000) [h : Ring α] : Ring αᵒᵈ := h

instance (priority := 10000) [h : NonUnitalCommRing α] : NonUnitalCommRing αᵒᵈ := h

instance (priority := 10000) [h : CommRing α] : CommRing αᵒᵈ := h

instance (priority := 10000) [Ring α] [h : IsDomain α] : IsDomain αᵒᵈ := h

/-! ### Lexicographical order -/


instance (priority := 10000) [h : Distrib α] : Distrib (Lex α) := h

instance (priority := 10000) [Mul α] [Add α] [h : LeftDistribClass α] : LeftDistribClass (Lex α) := h

instance (priority := 10000) [Mul α] [Add α] [h : RightDistribClass α] : RightDistribClass (Lex α) := h

instance (priority := 10000) [h : NonUnitalNonAssocSemiring α] : NonUnitalNonAssocSemiring (Lex α) := h

instance (priority := 10000) [h : NonUnitalSemiring α] : NonUnitalSemiring (Lex α) := h

instance (priority := 10000) [h : NonAssocSemiring α] : NonAssocSemiring (Lex α) := h

instance (priority := 10000) [h : Semiring α] : Semiring (Lex α) := h

instance (priority := 10000) [h : NonUnitalCommSemiring α] : NonUnitalCommSemiring (Lex α) := h

instance (priority := 10000) [h : CommSemiring α] : CommSemiring (Lex α) := h

instance (priority := 10000) [Mul α] [h : HasDistribNeg α] : HasDistribNeg (Lex α) := h

instance (priority := 10000) [h : NonUnitalNonAssocRing α] : NonUnitalNonAssocRing (Lex α) := h

instance (priority := 10000) [h : NonUnitalRing α] : NonUnitalRing (Lex α) := h

instance (priority := 10000) [h : NonAssocRing α] : NonAssocRing (Lex α) := h

instance (priority := 10000) [h : Ring α] : Ring (Lex α) := h

instance (priority := 10000) [h : NonUnitalCommRing α] : NonUnitalCommRing (Lex α) := h

instance (priority := 10000) [h : CommRing α] : CommRing (Lex α) := h

instance (priority := 10000) [Ring α] [h : IsDomain α] : IsDomain (Lex α) := h
