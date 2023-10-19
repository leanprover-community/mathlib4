/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

import Mathlib.Init.Data.Nat.Notation
import Mathlib.Mathport.Rename
import Mathlib.Data.Fin.Tuple.Basic

/-! # Function types of a given arity

This provides `FunctionOfArity`, such that `OfArity α 2 = α → α → α`.
Note that it is often preferrable to use `(Fin n → α) → α` in place of `OfArity n α`.

## Main definitions

* `Function.OfArity α n`: `n`-ary function `α → α → ... → α`. Defined inductively.
* `Function.OfArity.const a n`: `n`-ary constant function equal to `a`.
* `Function.OfArity.uncurry`: convert an `n`-ary function to a function from `Fin n → α`.
* `Function.OfArity.curry`: convert a function from `Fin n → α` to an `n`-ary function.
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

section currying

variable {α : Type u}

/-- Uncurry all the arguments of `Function.OfArity α n` to get a function from a tuple.

Note this can be used on raw functions if used-/
def uncurry {n} (f : Function.OfArity α n) : (Fin n → α) → α :=
  match n with
  | 0 => fun _ => f
  | _ + 1 => fun args => (f (args 0)).uncurry (args ∘ Fin.succ)

/-- Uncurry all the arguments of `Function.OfArity α n` to get a function from a tuple. -/
def curry {n} (f : (Fin n → α) → α) : Function.OfArity α n :=
  match n with
  | 0 => f Fin.elim0
  | _ + 1 => fun a => curry (fun args => f (Fin.cons a args))

@[simp]
theorem curry_uncurry {n} (f : Function.OfArity α n) :
    curry (uncurry f) = f :=
  match n with
  | 0 => rfl
  | n + 1 => funext fun a => by
    dsimp [curry, uncurry, Function.comp]
    simp only [Fin.cons_zero, Fin.cons_succ]
    eta_reduce
    eta_reduce
    rw [curry_uncurry]

@[simp]
theorem uncurry_curry {n} (f : (Fin n → α) → α) :
    uncurry (curry f) = f := by
  ext args
  induction args using Fin.consInduction with
  | h0 => rfl
  | h a as ih =>
    dsimp [curry, uncurry, Function.comp]
    simp only [Fin.cons_zero, Fin.cons_succ, ih (f <| Fin.cons a ·)]

end currying

end OfArity

end Function
