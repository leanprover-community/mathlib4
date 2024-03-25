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


instance [h : Distrib α] : Distrib αᵒᵈ := fast_instance% h

instance [Mul α] [Add α] [h : LeftDistribClass α] : LeftDistribClass αᵒᵈ := fast_instance% h

instance [Mul α] [Add α] [h : RightDistribClass α] : RightDistribClass αᵒᵈ := fast_instance% h

instance [h : NonUnitalNonAssocSemiring α] : NonUnitalNonAssocSemiring αᵒᵈ := fast_instance% h

instance [h : NonUnitalSemiring α] : NonUnitalSemiring αᵒᵈ := fast_instance% h

instance [h : NonAssocSemiring α] : NonAssocSemiring αᵒᵈ := fast_instance% h

instance [h : Semiring α] : Semiring αᵒᵈ := fast_instance% h

instance [h : NonUnitalCommSemiring α] : NonUnitalCommSemiring αᵒᵈ := fast_instance% h

instance [h : CommSemiring α] : CommSemiring αᵒᵈ := fast_instance% h

instance [Mul α] [h : HasDistribNeg α] : HasDistribNeg αᵒᵈ := fast_instance% h

instance [h : NonUnitalNonAssocRing α] : NonUnitalNonAssocRing αᵒᵈ := fast_instance% h

instance [h : NonUnitalRing α] : NonUnitalRing αᵒᵈ := fast_instance% h

instance [h : NonAssocRing α] : NonAssocRing αᵒᵈ := fast_instance% h

instance [h : Ring α] : Ring αᵒᵈ := fast_instance% h

instance [h : NonUnitalCommRing α] : NonUnitalCommRing αᵒᵈ := fast_instance% h

instance [h : CommRing α] : CommRing αᵒᵈ := fast_instance% h

instance [Ring α] [h : IsDomain α] : IsDomain αᵒᵈ := fast_instance% h

/-! ### Lexicographical order -/


instance [h : Distrib α] : Distrib (Lex α) := fast_instance% h

instance [Mul α] [Add α] [h : LeftDistribClass α] : LeftDistribClass (Lex α) := fast_instance% h

instance [Mul α] [Add α] [h : RightDistribClass α] : RightDistribClass (Lex α) := fast_instance% h

instance [h : NonUnitalNonAssocSemiring α] : NonUnitalNonAssocSemiring (Lex α) := fast_instance% h

instance [h : NonUnitalSemiring α] : NonUnitalSemiring (Lex α) := fast_instance% h

instance [h : NonAssocSemiring α] : NonAssocSemiring (Lex α) := fast_instance% h

instance [h : Semiring α] : Semiring (Lex α) := fast_instance% h

instance [h : NonUnitalCommSemiring α] : NonUnitalCommSemiring (Lex α) := fast_instance% h

instance [h : CommSemiring α] : CommSemiring (Lex α) := fast_instance% h

instance [Mul α] [h : HasDistribNeg α] : HasDistribNeg (Lex α) := fast_instance% h

instance [h : NonUnitalNonAssocRing α] : NonUnitalNonAssocRing (Lex α) := fast_instance% h

instance [h : NonUnitalRing α] : NonUnitalRing (Lex α) := fast_instance% h

instance [h : NonAssocRing α] : NonAssocRing (Lex α) := fast_instance% h

instance [h : Ring α] : Ring (Lex α) := fast_instance% h

instance [h : NonUnitalCommRing α] : NonUnitalCommRing (Lex α) := fast_instance% h

instance [h : CommRing α] : CommRing (Lex α) := fast_instance% h

instance [Ring α] [h : IsDomain α] : IsDomain (Lex α) := fast_instance% h
