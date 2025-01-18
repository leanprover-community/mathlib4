/-
Copyright (c) 2025 Tomaz Mascarenhas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving, Tomaz Mascarenhas
-/
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Set.Basic

/-!
# Definition of a model of computation based on oracles.

This module defines an abstraction of computation with oracles, enabling the analysis of upper
bounds on the query complexity of algorithms. It also provides a Monad instance for it.

Note that this is the deterministic version. In the future, the stochastic version will
also be ported, which enables the possibility of proving lower bounds on the query complexity
of algorithms. In order to facilitate this future integration, the design of the types
in this module is based on the original stochastic version. Source:
  https://github.com/girving/debate/blob/862fdb1cf55df0d541b802bdb1e672d724df6398/Comp/Oracle.lean

## Main Definitions

* Comp (ι : Type) {I : Type} (s : Set I) (α : Type) : Type
* Comp.run : Comp ι s α → (I → Oracle ι) → α × (I → ℕ)
-/

open Classical
open Set
noncomputable section

variable {ι I : Type}
variable {s t : Set I}
variable {α β γ : Type}

namespace QueryComplexity

/-- A deterministic oracle is a map from `α` to `Bool` -/
def Oracle (α : Type) := α → Bool

/- A deterministic computation that make decisions by querying oracles. A computation is either a
pure value or the identifier of an oracle (`o`) drawn from a predefined set (`s`), a value to
be queried by the oracle (`i`) and two other computations, to be run depending on the answer
of the oracle. -/
inductive Comp (ι : Type) {I : Type} (s : Set I) (α : Type) : Type where
  | pure' : α → Comp ι s α
  | query' : (o : I) → o ∈ s → (i : ι) → Comp ι s α → Comp ι s α → Comp ι s α

namespace Comp

/-- The standard bind operation for `Comp` -/
def bind' (f : Comp ι s α) (g : α → Comp ι s β) : Comp ι s β := match f with
  | .pure' x => g x
  | .query' o m y f0 f1 => .query' o m y (f0.bind' g) (f1.bind' g)

/-- `Comp` is a monad -/
instance : Monad (Comp ι s) where
  pure := Comp.pure'
  bind := Comp.bind'

/-- Produce a `Comp` given the identifier of an oracle and a value to be queried. The `Comp`
just returns `true` or `false` according to the answer of the oracle. -/
def query (o : I) (y : ι) : Comp ι {o} Bool :=
  Comp.query' o (mem_singleton _) y (pure true) (pure false)

/-- Execute `f` with the oracles `os`. Returns the final value and the number of queries to
each one of the oracles. -/
def run (f : Comp ι s α) (os : I → Oracle ι) : α × (I → ℕ) := match f with
  | .pure' x => (x, fun _ => 0)
  | .query' i _ y f0 f1 =>
    let x := (os i) y
    let (z,c) := if x then f0.run os else f1.run os
    (z, c + fun j => if j = i then 1 else 0)

/-- The value of a `Comp ι s` after it's execution -/
def value (f : Comp ι s α) (o : I → Oracle ι) : α :=
  Prod.fst (f.run o)

/-- The value of a `Comp ι s` after it's execution with a single oracle -/
@[simp]
def value' (f : Comp ι s α) (o : Oracle ι) : α :=
  f.value fun _ ↦ o

/-- The query count for a specific oracle of a `Comp ι s` -/
def cost (f : Comp ι s α) (o : I → Oracle ι) (i : I) : ℕ :=
  Prod.snd (f.run o) i

/-- The cost of a `Comp ι s`, when run with a single oracle -/
def cost' (f : Comp ι s α) (o : Oracle ι) : I → ℕ :=
  f.cost fun _ ↦ o

/-- Extend the set of allowed oracles in a computation -/
def allow (f : Comp ι s α) (st : s ⊆ t) : Comp ι t α := match f with
  | .pure' x => pure x
  | .query' i m y f0 f1 => .query' i (st m) y (f0.allow st) (f1.allow st)

/-- Extend the set of allowed oracles in a computation to the universe set -/
def allow_all (f : Comp ι s α) : Comp ι (@univ I) α :=
  f.allow (subset_univ s)

end Comp

end QueryComplexity
