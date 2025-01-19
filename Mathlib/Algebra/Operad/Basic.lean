/-
Copyright (c) 2024 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mathlib.Algebra.Group.Action.Defs

/-!
# Operads: basic typeclasses and notations

This file defines the typeclasses and notations used for working with `Operad`, `SymmOperad`,
  and `Clone`. These all, in some form another, work with graded - or Sigma - types. Below,
  `A : ℕ → Type*` is always the carrier.

  Classes:
  - `MultiComposable`: A `compose` operation `A n → Fin n → A m → A (n+m-1)`, for composing an
    element of grade `m` into one of grade `n` at a location `Fin n`. This is the type of operation
    used in Operads.
  - `Superposable`: A `superpose` operation `A n → (Fin n → A m) → A m`. This is the type of
    operation used in Clones.
  - `OneGradedOne`: There is a distinguished `1` element at grade 1, a notion of identity.
  - `SigmaMulAction`: A graded `MulAction M A`, where elements `M i` can act on `A i` at each i.

  Definitions:
  - `composeAt` bundles the action of `MultiComposable.compose` into `Sigma A`.
  - `superpose` bundles the action of `Superposable.superpose` into `Sigma A`.

  Notations:
  - `x ∘⟨p⟩ y` for `MultiComposable.compose` to compose `x ∘ y` at index `p`.
  - `x ∘[p] y` for the `composeAt` Sigma variant.
  - `x ∘⚟ y` for `Superposable.superpose x y`. The typography is meant to suggest
    "many arguments into one".

  References:
  - [Wikipedia, "Operad"](https://en.wikipedia.org/wiki/Operad#Definition)
  - Clifford Bergman, "Bergman, Clifford (2011). Universal Algebra: Fundamentals and Selected
  Topics." [Google Books](https://books.google.ca/books?id=QXi3BZWoMRwC&pg=PA79)
  - "Operad", nCatlab. [Link](https://ncatlab.org/nlab/show/operad)
-/

/-- A MultiComposable is a structure that allows composition from an m-arity object
 into a n-arity object at location p (in the range 0 to n-1) to produce an (n+m-1)
 arity object. `Operad` is the canonical example. -/
class MultiComposable  (A : ℕ → Type*) where
  /-- Compose the (n+1)-arity object at location p on the m-arity object. -/
  compose {n m} : A n → Fin n → A m → A (n+m-1)

/-- A Superposable is a structure that allows "superposition": given an n-arity object
 and n many m-arity objects, they can all enter and share arguments to make a new m-arity
object. `Clone` is the canonical example. -/
class Superposable (A : ℕ → Type*) where
  /-- Compose the (n+1)-arity object at location p on the m-arity object. -/
  superpose {n m} : A n → (Fin n → A m) → A m

/-- Families that have a "one" at grading 1. -/
class OneGradedOne (A : ℕ → Type*) extends One (A 1) where

variable {A} {m n k : ℕ}

/-- Upgrade `MultiComposable.compose` to an operation on Sigma types. -/
def composeAt [MultiComposable A] (x : Sigma A) (y : Sigma A) (p : Fin x.fst) : Sigma A :=
  ⟨_, MultiComposable.compose x.snd p y.snd⟩

/-- Upgrade `Superposable.superpose` to an operation on Sigma types. -/
def superpose [Superposable A] (x : Sigma A) (y : Fin x.fst → A m) : Sigma A :=
  ⟨m, Superposable.superpose x.snd y⟩

namespace MultiComposable

/-- Alternative to `MultiComposable.compose`, with proof that the output arity `k` is correct. -/
def composeEq [MultiComposable A] (x : A n) (p : Fin n) (y : A m) (hk : n + m = k + 1) : A k :=
  (show k = n + m - 1 by omega) ▸ compose x p y

theorem compose_eq_composeEq [MultiComposable A] (x : A n) (p : Fin n) (y : A m)
    : compose x p y = composeEq x p y (Nat.sub_add_cancel (p.addNat m).pos).symm := by
  rfl

/-- Notation for `MultiComposable.compose`, for working with `A n` graded types. -/
scoped notation:70 x:71 " ∘⟨" p:70 "⟩ " y:70  => MultiComposable.compose x p y
/-- Notation for `composeAt`, for working with Sigma types. -/
scoped notation:70 x:71 " ∘[" p:70 "] " y:70  => composeAt x y p

end MultiComposable

namespace Superposable

/-- Notation for `Superposable.superpose`, for working with `A n` graded types. -/
scoped infixr:70 " ∘⚟ " => Superposable.superpose

/-- Notation for `superpose`, for working with Sigma types. -/
scoped infixr:70 " ∘∈ " => superpose

end Superposable

/-- `OneGradedOne` yields a `One (Sigma A)` -/
instance OneGradedOne_toOne [OneGradedOne A] : One (Sigma A) :=
  ⟨⟨1, 1⟩⟩

@[simp]
theorem OneGradedOne.id_fst_eq_id [OneGradedOne A] : (1 : Sigma A).fst = 1 :=
  rfl

@[simp]
theorem OneGradedOne.id_snd_eq_id [OneGradedOne A] : (1 : Sigma A).snd = 1 :=
  rfl

section SigmaMul

variable {ι : Type*}

universe s t

/-- A SigmaMulAction exists on two sigma types with the same domain, and gives a MulAction
  at each matched level. -/
class SigmaMulAction (M : (ι → Type s)) (A : ι → Type t) [m : ∀ i, Monoid (M i)] where
  /-- At each ι, there's a MulAction from M i on the type A i -/
  act_at (i : ι) : @MulAction (M i) (A i) (m i)

variable {M : (ι → Type s)} {A : ι → Type t} [m : ∀ i, Monoid (M i)] [SigmaMulAction M A]

instance sigmaMul_to_MulAction : ∀ (i : ι), MulAction (M i) (A i) :=
  SigmaMulAction.act_at

end SigmaMul
