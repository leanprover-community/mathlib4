/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Brendan Murphy
-/
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.OfArity

/-!
# Currying and uncurrying of n-ary functions

A function of `n` arguments can either be written as `f a₁ a₂ ⋯ aₙ` or `f' ![a₁, a₂, ⋯, aₙ]`.
This file provides the currying and uncurrying operations that convert between the two, as
n-ary generalizations of the binary `curry` and `uncurry`.

## Main definitions

* `Function.OfArity.uncurry`: convert an `n`-ary function to a function from `Fin n → α`.
* `Function.OfArity.curry`: convert a function from `Fin n → α` to an `n`-ary function.
* `Function.FromTypes.uncurry`: convert an `p`-ary heterogeneous function to a
  function from `(i : Fin n) → p i`.
* `Function.FromTypes.curry`: convert a function from `(i : Fin n) → p i` to a
  `p`-ary heterogeneous function.

-/

universe u v w w'

namespace Function.FromTypes

open Matrix (vecCons vecHead vecTail vecEmpty)

/-- Uncurry all the arguments of `Function.FromTypes p τ` to get
a function from a tuple.

Note this can be used on raw functions if used. -/
def uncurry : {n : ℕ} → {p : Fin n → Type u} → {τ : Type u} →
    (f : Function.FromTypes p τ) → ((i : Fin n) → p i) → τ
  | 0    , _, _, f => fun _    => f
  | _ + 1, _, _, f => fun args => (f (args 0)).uncurry (args ∘' Fin.succ)

/-- Curry all the arguments of `Function.FromTypes p τ` to get a function from a tuple. -/
def curry : {n : ℕ} → {p : Fin n → Type u} → {τ : Type u} →
    (((i : Fin n) → p i) → τ) → Function.FromTypes p τ
  | 0    , _, _, f => f isEmptyElim
  | _ + 1, _, _, f => fun a => curry (fun args => f (Fin.cons a args))

@[simp]
theorem uncurry_apply_cons {n : ℕ} {α} {p : Fin n → Type u} {τ : Type u}
    (f : Function.FromTypes (vecCons α p) τ) (a : α) (args : (i : Fin n) → p i) :
    uncurry f (Fin.cons a args) = @uncurry _ p _ (f a) args := rfl

@[simp low]
theorem uncurry_apply_succ {n : ℕ} {p : Fin (n + 1) → Type u} {τ : Type u}
    (f : Function.FromTypes p τ) (args : (i : Fin (n + 1)) → p i) :
    uncurry f args = uncurry (f (args 0)) (Fin.tail args) := rfl

@[simp]
theorem curry_apply_cons {n : ℕ} {α} {p : Fin n → Type u} {τ : Type u}
    (f : ((i : Fin (n + 1)) → (vecCons α p) i) → τ) (a : α) :
    curry f a = @curry _ p _ (f ∘' Fin.cons a) := rfl

@[simp low]
theorem curry_apply_succ {n : ℕ} {p : Fin (n + 1) → Type u} {τ : Type u}
    (f : ((i : Fin (n + 1)) → p i) → τ) (a : p 0) :
    curry f a = curry (f ∘ Fin.cons a) := rfl

variable {n : ℕ} {p : Fin n → Type u} {τ : Type u}

@[simp]
theorem curry_uncurry (f : Function.FromTypes p τ) : curry (uncurry f) = f := by
  induction n with
  | zero => rfl
  | succ n ih => exact funext (ih <| f ·)

@[simp]
theorem uncurry_curry (f : ((i : Fin n) → p i) → τ) :
    uncurry (curry f) = f := by
  ext args
  induction n with
  | zero => exact congrArg f (Subsingleton.allEq _ _)
  | succ n ih => exact Eq.trans (ih _ _) (congrArg f (Fin.cons_self_tail args))

/-- `Equiv.curry` for `p`-ary heterogeneous functions. -/
@[simps]
def curryEquiv (p : Fin n → Type u) : (((i : Fin n) → p i) → τ) ≃ FromTypes p τ where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

lemma curry_two_eq_curry {p : Fin 2 → Type u} {τ : Type u}
    (f : ((i : Fin 2) → p i) → τ) :
    curry f = Function.curry (f ∘ (piFinTwoEquiv p).symm) := rfl

lemma uncurry_two_eq_uncurry (p : Fin 2 → Type u) (τ : Type u)
    (f : Function.FromTypes p τ) :
    uncurry f = Function.uncurry f ∘ piFinTwoEquiv p := rfl

end Function.FromTypes

namespace Function.OfArity

variable {α β : Type u}

/-- Uncurry all the arguments of `Function.OfArity α n` to get a function from a tuple.

Note this can be used on raw functions if used. -/
def uncurry {n} (f : Function.OfArity α β n) : (Fin n → α) → β := FromTypes.uncurry f

/-- Curry all the arguments of `Function.OfArity α β n` to get a function from a tuple. -/
def curry {n} (f : (Fin n → α) → β) : Function.OfArity α β n := FromTypes.curry f

@[simp]
theorem curry_uncurry {n} (f : Function.OfArity α β n) :
    curry (uncurry f) = f := FromTypes.curry_uncurry f

@[simp]
theorem uncurry_curry {n} (f : (Fin n → α) → β) :
    uncurry (curry f) = f := FromTypes.uncurry_curry f

/-- `Equiv.curry` for n-ary functions. -/
@[simps!]
def curryEquiv (n : ℕ) : ((Fin n → α) → β) ≃ OfArity α β n :=
  FromTypes.curryEquiv _

lemma curry_two_eq_curry {α β : Type u} (f : ((i : Fin 2) → α) → β) :
    curry f = Function.curry (f ∘ (finTwoArrowEquiv α).symm) :=
  FromTypes.curry_two_eq_curry f

lemma uncurry_two_eq_uncurry {α β : Type u} (f : OfArity α β 2) :
    uncurry f = Function.uncurry f ∘ (finTwoArrowEquiv α) :=
  FromTypes.uncurry_two_eq_uncurry _ _ f

end Function.OfArity
