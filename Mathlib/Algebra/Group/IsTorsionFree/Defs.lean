/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.MkIffOfInductiveProp

/-!
# Definitions about torsion free monoids

In this file we define typeclasses for torsion free additive and multiplicative monoids.
-/

/-- An additive monoid is called *torsion free*,
if `n • x = 0`, `n : ℕ`, is possibly only if `n = 0` or `x = 0`. -/
class IsAddTorsionFree (M : Type*) [AddMonoid M] : Prop where
  eq_zero_of_nsmul_eq_zero (x : M) (n : ℕ) : n • x = 0 → n ≠ 0 → x = 0

/-- A multiplicative monoid is called *torsion free*,
if `x ^ n = 1`, `n : ℕ`, is possibly only if `n = 0` or `x = 1`. -/
@[to_additive, mk_iff]
class IsMulTorsionFree (M : Type*) [Monoid M] : Prop where
  eq_one_of_pow_eq_one (x : M) (n : ℕ) : x ^ n = 1 → n ≠ 0 → x = 1

attribute [to_additive] isMulTorsionFree_iff

@[to_additive]
instance (priority := 100) IsMulTorsionFree.of_subsingleton
    (M : Type*) [Monoid M] [Subsingleton M] : IsMulTorsionFree M where
  eq_one_of_pow_eq_one _ _ _ _ := Subsingleton.elim _ _

variable {M : Type*} [Monoid M] [IsMulTorsionFree M] {x : M} {n : ℕ}

@[to_additive]
theorem eq_one_of_pow_eq_one (hxn : x ^ n = 1) (hn : n ≠ 0) : x = 1 :=
  IsMulTorsionFree.eq_one_of_pow_eq_one x n hxn hn

@[to_additive, simp]
theorem pow_eq_one_iff : x ^ n = 1 ↔ x = 1 ∨ n = 0 := by
  if hn : n = 0 then simp [hn]
  else if hx : x = 1 then simp [*]
  else simp [*, mt (eq_one_of_pow_eq_one · hn)]

@[to_additive nsmul_eq_zero_iff_right]
theorem pow_eq_one_iff_left (hn : n ≠ 0) : x ^ n = 1 ↔ x = 1 := by simp [hn]
