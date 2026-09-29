/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Torsion

/-!
# Torsion of products

This file proves that products of torsion-free monoids are torsion-free.
-/

public section

assert_not_exists AddMonoidWithOne MonoidWithZero

variable {ι : Type*} {M : ι → Type*}

namespace Pi

@[to_additive]
instance [∀ i, Monoid (M i)] [∀ i, IsMulTorsionFree (M i)] : IsMulTorsionFree (∀ i, M i) where
  eq_of_pow_eq_pow_of_commute n hn a b hab h := by
    ext i
    exact IsMulTorsionFree.eq_of_pow_eq_pow_of_commute hn (congr_fun hab i) (congrFun h i)

@[to_additive]
instance [∀ i, Monoid (M i)] [∀ i, HasUniqueRoots (M i)] : HasUniqueRoots (∀ i, M i) where
  pow_left_injective n hn a b hab := by ext i; exact pow_left_injective hn <| congr_fun hab i

end Pi
