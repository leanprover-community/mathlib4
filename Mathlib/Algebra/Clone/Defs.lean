/-
Copyright (c) 2024 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mathlib.Data.One.Defs
import Mathlib.Tactic.TypeStar

/-!
# Clones

This file defines the notation typeclasse `Superposable` used for working with `Clone`.
  There is a version with bare types `{n m : ℕ} : A n → (T n → A m) → A m`, and a version
  for Sigma types `(x : Sigma A) (y : T x.fst → A m) : Sigma A`. In both of these,
  `A : ι → Type*` is the carrier. A prototypical could have `ι := ℕ`, `T := Fin`, and `A i`
  as some `i`-arity functions.

  This also defines the `OneGradedOne` type class, which gives a graded `One (A 1)`.

  Classes:
  - `Superposable`: A `superpose` operation `A n → (T n → A m) → A m`. This is the type of
    operation used in Clones.
  - `OneGradedOne`: There is a distinguished `1` element at grade 1, a notion of identity.

  Definitions:.
  - `superpose` bundles the action of `Superposable.superpose` into `Sigma A`.

  Notations:
  - `x ∘⚟ y` for `Superposable.superpose x y`. The typography is meant to suggest
    "many arguments into one".
  - `x ∘∈ y` for `superpose x y`, the variant for Sigma types.
-/

/-- A Superposable is a structure that allows "superposition": given an n-arity object
 and n many m-arity objects, they can all enter and share arguments to make a new m-arity
object. `Clone` is the canonical example. -/
class Superposable {ι : Type*} (T : ι → Type*) (A : ι → Type*) where
  /-- Compose the (n+1)-arity object at location p on the m-arity object. -/
  superpose {n m} : A n → (T n → A m) → A m

variable {ι : Type*} {T A : ι → Type*} {i : ι}

/-- Upgrade `Superposable.superpose` to an operation on Sigma types. -/
def superpose [Superposable T A] (x : Sigma A) (y : T x.fst → A i) : Sigma A :=
  ⟨i, Superposable.superpose x.snd y⟩

namespace Superposable

/-- Notation for `Superposable.superpose`, for working with `A n` graded types. -/
scoped infixr:70 " ∘⚟ " => Superposable.superpose

/-- Notation for `superpose`, for working with Sigma types. -/
scoped infixr:70 " ∘∈ " => _root_.superpose

variable [Superposable T A]

@[simp]
theorem superpose_fst {i : ι} (x : Sigma A) (y : T x.fst → A i) : (x ∘∈ y).fst = i :=
  rfl

@[simp]
theorem superpose_snd {i : ι} (x : Sigma A) (y : T x.fst → A i) : (x ∘∈ y).snd = x.snd ∘⚟ y :=
  rfl

end Superposable

/-- Families that have a "one" at grading 1. -/
class OneGradedOne {ι : Type*} [One ι] (A : ι → Type*) extends One (A 1) where

namespace OneGradedOne

variable [One ι] [OneGradedOne A]

/-- `OneGradedOne` yields a `One (Sigma A)` -/
instance OneGradedOne_toOne : One (Sigma A) :=
  ⟨⟨1, 1⟩⟩

@[simp]
theorem sigma_snd : (1 : Sigma A).snd = 1 :=
  rfl

@[simp]
theorem sigma_fst : (1 : Sigma A).fst = 1 :=
  rfl

end OneGradedOne
