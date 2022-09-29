/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
import Mathlib.Data.Multiset.Nodup

/-!
# Finite sets

Terms of type `Finset α` are one way of talking about finite subsets of `α` in mathlib.
Below, `Finset α` is defined as a structure with 2 fields:

  1. `val` is a `Multiset α` of elements;
  2. `nodup` is a proof that `val` has no duplicates.

Finsets in Lean are constructive in that they have an underlying `List` that enumerates their
elements. In particular, any function that uses the data of the underlying list cannot depend on its
ordering. This is handled on the `Multiset` level by multiset API, so in most cases one needn't
worry about it explicitly.

## Main declarations

### Main definitions

* `Finset`: Defines a type for the finite subsets of `α`.
  Constructing a `Finset` requires two pieces of data: `val`, a `Multiset α` of elements,
  and `nodup`, a proof that `val` has no duplicates.
* `Finset.Membership`: Defines membership `a ∈ (s : Finset α)`.

-/


open Multiset Subtype Nat Function

universe u

variable {α : Type _} {β : Type _} {γ : Type _}

/-- `finset α` is the type of finite sets of elements of `α`. It is implemented
  as a multiset (a list up to permutation) which has no duplicate elements. -/
structure Finset (α : Type _) where
  /-- The underlying `Multiset` of a `Finset`. -/
  val : Multiset α
  /-- The proof that the underlying `Multiset` of a `Finset` has no duplicates. -/
  nodup : Nodup val

namespace Finset

/-! ### membership -/

instance : Membership α (Finset α) := ⟨fun a s => a ∈ s.1⟩

theorem mem_def {a : α} {s : Finset α} : a ∈ s ↔ a ∈ s.1 := Iff.rfl
