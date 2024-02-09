/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Brendan Murphy
-/
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fin
import Mathlib.Logic.Function.OfHArity

/-!
# Currying and uncurrying of n-ary functions

A function of `n` arguments can either be written as `f a₁ a₂ ⋯ aₙ` or `f' ![a₁, a₂, ⋯, aₙ]`.
This file provides the currying and uncurrying operations that convert between the two, as
n-ary generalizations of the binary `curry` and `uncurry`.

## Main definitions

* `Function.OfArity.uncurry`: convert an `n`-ary function to a function from `Fin n → α`.
* `Function.OfArity.curry`: convert a function from `Fin n → α` to an `n`-ary function.
* `Function.OfHArity.uncurry`: convert an `p`-ary heterogeneous function to a
  function from `(i : Fin n) → p i`.
* `Function.OfHArity.curry`: convert a function from `(i : Fin n) → p i` to a
  `p`-ary heterogeneous function.

-/

universe u v w w'

namespace Function

/-- Currying for 3-ary functions. -/
@[inline] def curry₃ {α : Type u} {β : Type v} {γ : Type w} {δ : Type w'} :
    (α × β × γ → δ) → α → β → γ → δ := fun f a b c => f (a, b, c)
/-- Uncurrying for 3-ary functions. -/
@[inline] def uncurry₃ {α : Type u} {β : Type v} {γ : Type w} {δ : Type w'} :
    (α → β → γ → δ) → (α × β × γ) → δ := fun f x => f x.1 x.2.1 x.2.2

end Function

namespace Function.OfArity

variable {α β : Type u}

/-- Uncurry all the arguments of `Function.OfArity α n` to get a function from a tuple.

Note this can be used on raw functions if used. -/
def uncurry {n} (f : Function.OfArity α β n) : (Fin n → α) → β :=
  match n with
  | 0 => fun _ => f
  | _ + 1 => fun args => (f (args 0)).uncurry (args ∘ Fin.succ)

/-- Curry all the arguments of `Function.OfArity α β n` to get a function from a tuple. -/
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

lemma curry_2_eq_curry {α β : Type u} (f : ((i : Fin 2) → α) → β) :
    curry f = Function.curry (f ∘ (finTwoArrowEquiv α).symm) := rfl

lemma uncurry_2_eq_uncurry₂ {α β : Type u} (f : OfArity α β 2) :
    uncurry f = Function.uncurry f ∘ (finTwoArrowEquiv α) := rfl

lemma curry_3_eq_curry₃ {α β : Type u} (f : ((i : Fin 3) → α) → β) :
    curry f = curry₃ (f ∘ (finThreeArrowEquiv α).symm) := rfl

lemma uncurry_3_eq_uncurry₃ {α β : Type u} (f : OfArity α β 3) :
    uncurry f = uncurry₃ f ∘ (finThreeArrowEquiv α) := rfl

end Function.OfArity

namespace Function.OfHArity

open Matrix (vecCons vecHead vecTail vecEmpty)

/-- Uncurry all the arguments of `Function.OfHArity p τ` to get
a function from a tuple.

Note this can be used on raw functions if used. -/
def uncurry : {n : ℕ} → {p : Fin n → Type u} → {τ : Type u} →
    (f : Function.OfHArity p τ) → ((i : Fin n) → p i) → τ
  | 0    , _, _, f => fun _    => f
  | _ + 1, _, _, f => fun args => (f (args 0)).uncurry (args ∘' Fin.succ)

/-- Curry all the arguments of `Function.OfHArity p τ` to get a function from a tuple. -/
def curry : {n : ℕ} → {p : Fin n → Type u} → {τ : Type u} →
    (((i : Fin n) → p i) → τ) → Function.OfHArity p τ
  | 0    , _, _, f => f isEmptyElim
  | _ + 1, _, _, f => fun a => curry (fun args => f (Fin.cons a args))

@[simp]
theorem uncurry_apply_cons {n : ℕ} {α} {p : Fin n → Type u} {τ : Type u}
    (f : Function.OfHArity (vecCons α p) τ) (a : α) (args : (i : Fin n) → p i) :
    uncurry f (Fin.cons a args) = @uncurry _ p _ (f a) args := rfl

@[simp low]
theorem uncurry_apply_succ {n : ℕ} {p : Fin (n + 1) → Type u} {τ : Type u}
    (f : Function.OfHArity p τ) (args : (i : Fin (n + 1)) → p i) :
    uncurry f args = uncurry (f (args 0)) (Fin.tail args) :=
  @uncurry_apply_cons n (p 0) (vecTail p) τ f (args 0) (Fin.tail args)

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
theorem curry_uncurry (f : Function.OfHArity p τ) : curry (uncurry f) = f := by
  induction n with
  | zero => rfl
  | succ n ih => exact funext (ih $ f .)

@[simp]
theorem uncurry_curry (f : ((i : Fin n) → p i) → τ) :
    uncurry (curry f) = f := by
  ext args
  induction n with
  | zero => exact congrArg f (Subsingleton.allEq _ _)
  | succ n ih => exact Eq.trans (ih _ _) (congrArg f (Fin.cons_self_tail args))

/-- `Equiv.curry` for `p`-ary heterogeneous functions. -/
@[simps]
def curryEquiv (p : Fin n → Type u) : (((i : Fin n) → p i) → τ) ≃ OfHArity p τ where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

lemma curry_2_eq_curry₂ {p : Fin 2 → Type u} {τ : Type u}
    (f : ((i : Fin 2) → p i) → τ) :
    curry f = Function.curry (f ∘ (piFinTwoEquiv p).symm) := rfl

lemma uncurry_2_eq_uncurry₂ (p : Fin 2 → Type u) (τ : Type u)
    (f : Function.OfHArity p τ) :
    uncurry f = Function.uncurry f ∘ piFinTwoEquiv p := rfl

lemma curry_3_eq_curry₃ {p : Fin 3 → Type u} {τ : Type u}
    (f : ((i : Fin 3) → p i) → τ) :
    curry f = curry₃ (f ∘ (piFinThreeEquiv p).symm) := rfl

lemma uncurry_3_eq_uncurry₃ (p : Fin 3 → Type u) (τ : Type u)
    (f : Function.OfHArity p τ) :
    uncurry f = uncurry₃ f ∘ piFinThreeEquiv p := rfl

end Function.OfHArity
