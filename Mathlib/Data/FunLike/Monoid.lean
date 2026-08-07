/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.FunLike.IsApply

/-! # Additional lemmas for `Monoid` -/

public section

variable {F α : Type*} [FunLike F α α] [Monoid F] [IsMulApplyEqComp F α] [IsOneApplyEqSelf F α]

@[simp, grind =]
lemma pow_apply_eq_iterate (f : F) (n : ℕ) (x : α) : (f ^ n) x = f^[n] x := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ', ih, ← Function.iterate_succ_apply']

@[simp, norm_cast]
lemma FunLike.coe_pow_eq_iterate (f : F) (n : ℕ) : ⇑(f ^ n) = f^[n] :=
  funext <| pow_apply_eq_iterate f n
