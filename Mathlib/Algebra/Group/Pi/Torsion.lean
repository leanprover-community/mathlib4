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
instance instIsMulTorsionFree [∀ i, Monoid (M i)] [∀ i, IsMulTorsionFree (M i)] :
    IsMulTorsionFree (∀ i, M i) where
  eq_of_pow_eq_pow_of_commute _n hn _a _b hab habn := funext fun i ↦
    eq_of_pow_eq_pow_of_commute hn (congr_fun hab i) (congr_fun habn i)

end Pi
