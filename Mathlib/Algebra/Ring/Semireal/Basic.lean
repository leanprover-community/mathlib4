/-
Copyright (c) 2026 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
module

public import Mathlib.Algebra.Order.Ring.Ordering.Defs
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Algebra.Ring.Semireal.Defs

import Mathlib.Algebra.Field.Basic

/-!
# Properties of semireal rings

We prove basic properties of semireal rings, including their relationship to formally real rings
and to ring preorderings.

## References

- *An introduction to real algebra*, by T.Y. Lam. Rocky Mountain J. Math. 14(4): 767-814 (1984).
  [lam_1984](https://doi.org/10.1216/RMJ-1984-14-4-767)
-/

public section

variable (R : Type*)

instance [NonAssocSemiring R] [Nontrivial R] [IsFormallyReal R] : IsSemireal R where
  one_add_ne_zero := (one_ne_zero <| IsFormallyReal.eq_zero_of_add_right IsSumSq.one · ·)

section CommRing

variable [CommRing R]

theorem Subsemiring.IsPreordering.sumSq [IsSemireal R] : (Subsemiring.sumSq R).IsPreordering where
  mem_of_isSquare h := by grind [membership, Subsemiring.mem_sumSq, IsSquare.isSumSq]
  neg_one_notMem := by grind [membership, Subsemiring.mem_sumSq, IsSemireal.not_isSumSq_neg_one]

variable {R} in
theorem Subsemiring.IsPreordering.isSemireal {P : Subsemiring R} (hP : P.IsPreordering) :
    IsSemireal R := .of_not_isSumSq_neg_one (by membership)

variable {R} in
theorem exists_isPreordering_iff_isSemireal :
    (∃ P : Subsemiring R, P.IsPreordering) ↔ IsSemireal R where
  mp | ⟨_, hP⟩ => hP.isSemireal
  mpr _ := ⟨_, .sumSq R⟩

end CommRing

instance [Field R] [IsSemireal R] : IsFormallyReal R :=
  .of_eq_zero_of_eq_zero_of_mul_self_add <| fun {s} {a} _ h ↦ by
    by_contra
    apply IsSemireal.one_add_ne_zero (s := s * a⁻¹ ^ 2) <;>
      grind [inv_pow, IsSumSq.mul, IsSquare.isSumSq, isSquare_inv, IsSquare.sq]
