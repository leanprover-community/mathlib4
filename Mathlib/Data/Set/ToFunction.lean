/-
Copyright (c) 2024 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.Data.Rel
import Mathlib.Logic.ExistsUnique

/-!
# Set to function

This file provides API for sets that define functions.

## Main definitions

- `Set.asPartialFun` converts `Set (α × β)` to `α → Option β` if possible.
- `Set.asFun` converts `Set (α × β)` to `α → β` if possible.

These definitions mimic the standard definition of functions in set theory.

## Main theorems

- `Function.graph_toSet_asFun` says that if you convert a function to a graph, the graph to a set,
and the set to a function, you will obtain the same function.
-/

variable {α β : Type*}

namespace Set

section set_as_partial_function

/-- A set `s : Set (α × α)` represents a partial function if for every `x : α` there is at most one
`y : β` such that `(x, y) ∈ s`. -/
def IsPartialFun (s : Set (α × β)) : Prop :=
  ∀ x : α, { y : β | (x, y) ∈ s }.Subsingleton

open Classical in
/-- Use given set on `α × α` as a partial function. Each `x : α` is mapped to the unique `y : β`
such that `(x, y) ∈ s`, or to `none` if none exists.  -/
noncomputable def asPartialFun (s : Set (α × β)) : α → Option β :=
  fun a : α => if hb : ∃ b, (a, b) ∈ s then hb.choose else none

theorem asPartialFun_eq {s : Set (α × β)} (hs : IsPartialFun s) {a : α} {b : β} (hab : (a, b) ∈ s) :
    asPartialFun s a = b := by
  have hba : ∃ b, (a, b) ∈ s := ⟨b, hab⟩
  simpa [asPartialFun, hba] using hs _ hba.choose_spec hab

end set_as_partial_function

section set_as_total_function

/-- A set `s : Set (α × α)` represents a total function when for every `x : α` there's exactly one
`y : β` such that `(x, y) ∈ s`. -/
def IsFun (s : Set (α × β)) : Prop :=
  ∀ x : α, ∃! y : β, (x, y) ∈ s

theorem isFun.isPartialFun {s : Set (α × β)} (hs : IsFun s) : IsPartialFun s :=
  fun x y hxy z hxz => ((hs x).choose_spec.2 y hxy).trans ((hs x).choose_spec.2 z hxz).symm

/-- Turns `s : Set (α × α)` into a total function. Each `x : α` is mapped to the unique `y : β`
such that `(x, y) ∈ s`. -/
noncomputable def asFun {s : Set (α × β)} (hs : IsFun s) : α → β :=
  fun a : α => (hs a).choose

theorem asFun_eq {s : Set (α × β)} (hs : IsFun s) {a : α} {b : β} (hab : (a, b) ∈ s) :
    asFun hs a = b :=
  ((hs a).choose_spec.2 b hab).symm

end set_as_total_function

end Set

/-- Convert `Rel` to a `Set` (like uncurry). -/
def Rel.toSet (R : Rel α β) : Set (α × β) := fun ⟨a, b⟩ => R a b

theorem Function.graph_is_fun (f : α → β) : f.graph.toSet.IsFun :=
  fun x => ⟨f x, rfl, fun _ => Eq.symm⟩

theorem Function.graph_toSet_asFun (f : α → β) : Set.asFun f.graph_is_fun = f :=
  funext (fun _ => Set.asFun_eq f.graph_is_fun rfl)
