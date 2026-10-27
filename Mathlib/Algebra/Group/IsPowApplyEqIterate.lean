/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.IsApply

/-!

# Lemmas about monoid of functions

If `F` is a type of functions from `α` onto itself equipped with a monoid structure such that
`1` is the identity and the multiplication is given by the composition, then natural exponentiation
corresponds to iteration of composition.

This is separated from the `IsApply` file to avoid importing `Monoid` there.

-/

public section

variable {F α : Type*} [FunLike F α α] [Monoid F] [IsOneApplyEqSelf F] [IsMulApplyEqComp F]

@[simp, grind =]
lemma pow_apply_eq_iterate (f : F) (n : ℕ) (x : α) :
    (f ^ n) x = f^[n] x := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ', ih, ← Function.iterate_succ_apply']

@[simp, norm_cast]
lemma coe_pow_eq_iterate (f : F) (n : ℕ) : ⇑(f ^ n) = f^[n] :=
  funext <| pow_apply_eq_iterate f n
