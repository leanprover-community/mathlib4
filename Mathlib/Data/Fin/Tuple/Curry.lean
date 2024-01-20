/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Function.OfArity

/-!
# Currying and uncurrying of n-ary functions

A function of `n` arguments can either be written as `f a₁ a₂ ⋯ aₙ` or `f' ![a₁, a₂, ⋯, aₙ]`.
This file provides the currying and uncurrying operations that convert between the two, as
n-ary generalizations of the binary `curry` and `uncurry`.

## Main definitions

* `Function.OfArity.uncurry`: convert an `n`-ary function to a function from `Fin n → α`.
* `Function.OfArity.curry`: convert a function from `Fin n → α` to an `n`-ary function.

-/

universe u

variable {α β : Type u}

namespace Function.OfArity

/-- Uncurry all the arguments of `Function.OfArity α n` to get a function from a tuple.

Note this can be used on raw functions if used-/
def uncurry {n} (f : Function.OfArity α β n) : (Fin n → α) → β :=
  match n with
  | 0 => fun _ => f
  | _ + 1 => fun args => (f (args 0)).uncurry (args ∘ Fin.succ)

/-- Uncurry all the arguments of `Function.OfArity α β n` to get a function from a tuple. -/
def curry {n} (f : (Fin n → α) → β) : Function.OfArity α β n :=
  match n with
  | 0 => f Fin.elim0
  | _ + 1 => fun a => curry (fun args => f (Fin.cons a args))

@[simp]
theorem curry_uncurry {n} (f : Function.OfArity α β n) :
    curry (uncurry f) = f :=
  match n with
  | 0 => rfl
  | n + 1 => funext fun a => by
    dsimp [curry, uncurry, Function.comp_def]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [curry_uncurry]

@[simp]
theorem uncurry_curry {n} (f : (Fin n → α) → β) :
    uncurry (curry f) = f := by
  ext args
  induction args using Fin.consInduction with
  | h0 => rfl
  | h a as ih =>
    dsimp [curry, uncurry, Function.comp_def]
    simp only [Fin.cons_zero, Fin.cons_succ, ih (f <| Fin.cons a ·)]

/-- `Equiv.curry` for n-ary functions. -/
@[simps]
def curryEquiv (n : ℕ) : ((Fin n → α) → β) ≃ OfArity α β n where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

end Function.OfArity
