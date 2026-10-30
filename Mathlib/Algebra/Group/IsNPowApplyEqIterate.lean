/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid

/-!

# Lemmas about monoid of functions

If `F` is a type of functions from `α` onto itself equipped with a monoid structure such that
`1` is the identity and the multiplication is given by the composition, then natural exponentiation
corresponds to iteration of composition.

This is separated from the `IsApply` file to avoid importing `Monoid` there.

-/

public section

/-- `IsNPowApplyEqIterate F` states for all `x : α`, `(f ^ n) x = f^[n] x`. -/
class IsNPowApplyEqIterate (F : Type*) {α : outParam Type*} [FunLike F α α] [NPow F] where
  pow_apply_eq_iterate (f : F) (n : ℕ) (x : α) : (f ^ n) x = f^[n] x := by intros; rfl

@[grind =]
alias pow_apply_eq_iterate := IsNPowApplyEqIterate.pow_apply_eq_iterate

variable {F α : Type*} [FunLike F α α]

instance [Monoid F] [IsOneApplyEqSelf F] [IsMulApplyEqComp F] : IsNPowApplyEqIterate F where
  pow_apply_eq_iterate f n x := by
    induction n with
    | zero => simp
    | succ n ih => simp [pow_succ', ih, ← Function.iterate_succ_apply']

lemma FunLike.coe_pow_eq_iterate [NPow F] [IsNPowApplyEqIterate F] (f : F) (n : ℕ) :
    ⇑(f ^ n) = f^[n] :=
  funext <| pow_apply_eq_iterate f n
