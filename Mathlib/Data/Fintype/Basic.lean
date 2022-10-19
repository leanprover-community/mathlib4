/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Range

/-!
# Finite types

This file defines a typeclass to state that a type is finite.

## Main declarations

* `Fintype α`: Typeclass saying that a type is finite. It takes as fields a `Finset` and a proof
  that all terms of type `α` are in it.
* `Finset.univ`: The finset of all elements of a fintype.

-/

/-- `fintype α` means that `α` is finite, i.e. there are only
  finitely many distinct elements of type `α`. The evidence of this
  is a finset `elems` (a list up to permutation without duplicates),
  together with a proof that everything of type `α` is in the list. -/
class Fintype (α : Type _) where
  /-- The `Finset` of elements of a `Fintype`. -/
  elems : Finset α
  /-- The proof that every term of the type is contained in the `Finset` of elements. -/
  complete : ∀ x : α, x ∈ elems

namespace Finset

variable [Fintype α]

/-- `univ` is the universal finite set of type `finset α` implied from
  the assumption `fintype α`. -/
def univ : Finset α := Fintype.elems

@[simp] theorem mem_univ (x : α) : x ∈ (univ : Finset α) := Fintype.complete x

end Finset

namespace Fintype

instance (n : ℕ) : Fintype (Fin n) :=
  ⟨⟨List.finRange n, List.nodup_fin_range n⟩, List.mem_fin_range⟩

end Fintype
