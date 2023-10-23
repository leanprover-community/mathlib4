/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

import Mathlib.Init.Data.Nat.Notation
import Mathlib.Mathport.Rename

/-! # Function types of a given arity

This provides `FunctionOfArity`, such that `OfArity α 2 = α → α → α`.
Note that it is often preferrable to use `(Fin n → α) → α` in place of `OfArity n α`.

## Main definitions

* `Function.OfArity α n`: `n`-ary function `α → α → ... → α`. Defined inductively.
* `Function.OfArity.const a n`: `n`-ary constant function equal to `a`.
-/

universe u

namespace Function

/-- The type of `n`-ary functions `α → α → ... → α`. -/
def OfArity (α : Type u) : ℕ → Type u
  | 0 => α
  | n + 1 => α → OfArity α n
#align arity Function.OfArity

@[simp]
theorem ofArity_zero (α : Type u) : OfArity α 0 = α :=
  rfl
#align arity_zero Function.ofArity_zero

@[simp]
theorem ofArity_succ (α : Type u) (n : ℕ) : OfArity α n.succ = (α → OfArity α n) :=
  rfl
#align arity_succ Function.ofArity_succ

namespace OfArity

/-- Constant `n`-ary function with value `a`. -/
def const {α : Type u} (a : α) : ∀ n, OfArity α n
  | 0 => a
  | n + 1 => fun _ => const a n
#align arity.const Function.OfArity.const

@[simp]
theorem const_zero {α : Type u} (a : α) : const a 0 = a :=
  rfl
#align arity.const_zero Function.OfArity.const_zero

@[simp]
theorem const_succ {α : Type u} (a : α) (n : ℕ) : const a n.succ = fun _ => const a n :=
  rfl
#align arity.const_succ Function.OfArity.const_succ

theorem const_succ_apply {α : Type u} (a : α) (n : ℕ) (x : α) : const a n.succ x = const a n :=
  rfl
#align arity.const_succ_apply Function.OfArity.const_succ_apply

instance OfArity.inhabited {α n} [Inhabited α] : Inhabited (OfArity α n) :=
  ⟨const default _⟩
#align arity.arity.inhabited Function.OfArity.OfArity.inhabited

end OfArity

end Function
