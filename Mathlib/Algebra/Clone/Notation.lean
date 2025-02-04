/-
Copyright (c) 2024 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mathlib.Data.One.Defs
import Mathlib.Tactic.TypeStar

/-! This file defines the notation typeclasse `Superposable` used for working with `Clone`.
  There is a version with bare types `{n m : ℕ} : A n → (Fin n → A m) → A m`, and a version
  for Sigma types `(x : Sigma A) (y : Fin x.fst → A m) : Sigma A`. In both of these,
  `A : ℕ → Type*` is the carrier.

  This also defines the `OneGradedOne` type class, which gives a graded `One (A 1)`.

  Classes:
  - `Superposable`: A `superpose` operation `A n → (Fin n → A m) → A m`. This is the type of
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
class Superposable (A : ℕ → Type*) where
  /-- Compose the (n+1)-arity object at location p on the m-arity object. -/
  superpose {n m} : A n → (Fin n → A m) → A m

/-- Families that have a "one" at grading 1. -/
class OneGradedOne (A : ℕ → Type*) extends One (A 1) where

variable {A} {m : ℕ}

/-- Upgrade `Superposable.superpose` to an operation on Sigma types. -/
def superpose [Superposable A] (x : Sigma A) (y : Fin x.fst → A m) : Sigma A :=
  ⟨m, Superposable.superpose x.snd y⟩

namespace Superposable

/-- Notation for `Superposable.superpose`, for working with `A n` graded types. -/
scoped infixr:70 " ∘⚟ " => Superposable.superpose

/-- Notation for `superpose`, for working with Sigma types. -/
scoped infixr:70 " ∘∈ " => superpose

end Superposable

/-- `OneGradedOne` yields a `One (Sigma A)` -/
instance ComposableOne_toOne [OneGradedOne A] : One (Sigma A) :=
  ⟨⟨1, 1⟩⟩

@[simp]
theorem eq_id_sigma_id [OneGradedOne A] : (1 : Sigma A).snd = 1 :=
  rfl

@[simp]
theorem eq_id_sigma_one [OneGradedOne A] : (1 : Sigma A).fst = 1 :=
  rfl
