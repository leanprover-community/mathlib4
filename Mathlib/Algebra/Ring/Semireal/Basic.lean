/-
Copyright (c) 2026 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Ring.Semireal.Defs
public import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# Properties of semireal rings

We prove basic properties of semireal rings, such as their relationship to formally real rings.

## References

- *An introduction to real algebra*, by T.Y. Lam. Rocky Mountain J. Math. 14(4): 767-814 (1984).
  [lam_1984](https://doi.org/10.1216/RMJ-1984-14-4-767)
-/

public section

instance {R : Type*} [NonAssocSemiring R] [Nontrivial R] [IsFormallyReal R] : IsSemireal R where
  one_add_ne_zero := (one_ne_zero <| IsFormallyReal.eq_zero_of_add_right IsSumSq.one · ·)

instance {F : Type*} [Field F] [IsSemireal F] : IsFormallyReal F :=
  .of_eq_zero_of_eq_zero_of_mul_self_add <| fun {s} {a} _ h ↦ by
    by_contra
    exact IsSemireal.one_add_ne_zero (s := s * a⁻¹ ^ 2)
      (by grind [inv_pow, IsSumSq.mul, IsSquare.isSumSq, isSquare_inv, IsSquare.sq])
      (by grind)
