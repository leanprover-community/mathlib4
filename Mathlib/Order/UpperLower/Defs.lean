/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sara Rousta
-/
import Aesop
import Mathlib.Data.Set.Defs
import Mathlib.Tactic.ExtendDoc

/-!
# Up-sets and down-sets

This file defines upper and lower sets in an order.

## Main declarations

* `IsUpperSet`: Predicate for a set to be an upper set. This means every element greater than a
  member of the set is in the set itself.
* `IsLowerSet`: Predicate for a set to be a lower set. This means every element less than a member
  of the set is in the set itself.
* `UpperSet`: The type of upper sets.
* `LowerSet`: The type of lower sets.
-/

universe u

/-- An upper set in an order `α` is a set such that any element greater than one of its members is
also a member. Also called up-set, upward-closed set. -/
@[aesop norm unfold]
def IsUpperSet {α : Type u} [LE α] (s : Set α) : Prop :=
  ∀ ⦃a b : α⦄, a ≤ b → a ∈ s → b ∈ s

/-- A lower set in an order `α` is a set such that any element less than one of its members is also
a member. Also called down-set, downward-closed set. -/
@[aesop norm unfold]
def IsLowerSet {α : Type u} [LE α] (s : Set α) : Prop :=
  ∀ ⦃a b : α⦄, b ≤ a → a ∈ s → b ∈ s

@[inherit_doc IsUpperSet]
structure UpperSet (α : Type u) [LE α] where
  /-- The carrier of an `UpperSet`. -/
  carrier : Set α
  /-- The carrier of an `UpperSet` is an upper set. -/
  upper' : IsUpperSet carrier

extend_docs UpperSet before "The type of upper sets of an order."

@[inherit_doc IsLowerSet]
structure LowerSet (α : Type u) [LE α] where
  /-- The carrier of a `LowerSet`. -/
  carrier : Set α
  /-- The carrier of a `LowerSet` is a lower set. -/
  lower' : IsLowerSet carrier

extend_docs LowerSet before "The type of lower sets of an order."
