/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Init
public import Batteries.Tactic.Alias

/-!
### The predicate `List.Sorted` (now deprecated).
-/

@[expose] public section

namespace List

universe u v

section Sorted

variable {α : Type u} {r : α → α → Prop} {a : α} {l : List α}

/-- `Sorted r l` is the same as `List.Pairwise r l` and has been deprecated.
Consider using any of `SortedLE`, `SortedLT`, `SortedGE`, or `SortedGT` if the relation you're
  using is a preorder. -/
@[deprecated (since := "2025-10-11")]
alias Sorted := Pairwise

set_option linter.deprecated false

/-- Deprecated decidable instance for `Sorted`. -/
@[deprecated List.instDecidablePairwise (since := "2025-10-11")]
def decidableSorted [DecidableRel r] (l : List α) : Decidable (Sorted r l) :=
  List.instDecidablePairwise l

@[deprecated Pairwise.nil (since := "2025-10-11")]
theorem sorted_nil : Sorted r [] := Pairwise.nil

@[deprecated Pairwise.of_cons (since := "2025-10-11")]
theorem Sorted.of_cons (p : Sorted r (a :: l)) :
  Sorted r l := Pairwise.of_cons p

@[deprecated Pairwise.tail (since := "2025-10-11")]
theorem Sorted.tail (h : Sorted r l) : Sorted r l.tail := Pairwise.tail h

@[deprecated rel_of_pairwise_cons (since := "2025-10-11")]
theorem rel_of_sorted_cons (p : Sorted r (a :: l))
  {a' : α} : a' ∈ l → r a a' := rel_of_pairwise_cons p

@[deprecated pairwise_cons (since := "2025-10-11")]
theorem sorted_cons : Sorted r (a :: l) ↔ (∀ a' ∈ l, r a a') ∧ Sorted r l := pairwise_cons

@[deprecated Pairwise.filter (since := "2025-10-11")]
theorem Sorted.filter (p : α → Bool) : Sorted r l → Sorted r (filter p l) := Pairwise.filter p

@[deprecated pairwise_singleton (since := "2025-10-11")]
theorem sorted_singleton (r) (a : α) : Sorted r [a] := pairwise_singleton r a

@[deprecated Pairwise.rel_of_mem_take_of_mem_drop (since := "2025-10-11")]
theorem Sorted.rel_of_mem_take_of_mem_drop {x y i} (h : Sorted r l)
    (hx : x ∈ take i l) (hy : y ∈ drop i l) : r x y := Pairwise.rel_of_mem_take_of_mem_drop h hx hy

@[deprecated Pairwise.filterMap (since := "2025-10-11")]
theorem Sorted.filterMap (f) {s : α → α → Prop}
    (H : ∀ (a a' : α), r a a' → ∀ (b : α), f a = some b → ∀ (b' : α), f a' = some b' → s b b') :
  Sorted r l → Sorted s (filterMap f l) := Pairwise.filterMap f H

end Sorted

end List
