/-
Copyright (c) 2024 Hannah Fechtner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hannah Fechtner
-/
module

public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Translate.ToAdditive

/-!
# The finite set of symbols in a FreeMonoid element

This is separated from the main FreeMonoid file, as it imports the finiteness hierarchy
-/

@[expose] public section

variable {α : Type*} [DecidableEq α]

namespace FreeMonoid

/-- the set of unique symbols in a free monoid element -/
@[to_additive /-- The set of unique symbols in an additive free monoid element -/]
def symbols (a : FreeMonoid α) : Finset α := List.toFinset a

@[to_additive (attr := simp)]
theorem symbols_one : symbols (1 : FreeMonoid α) = ∅ := rfl

@[to_additive (attr := simp)]
theorem symbols_of {m : α} : symbols (of m) = {m} := rfl

@[to_additive (attr := simp)]
theorem symbols_mul {a b : FreeMonoid α} : symbols (a * b) = symbols a ∪ symbols b :=
  List.toFinset_append

@[to_additive (attr := simp)]
theorem mem_symbols {m : α} {a : FreeMonoid α} : m ∈ symbols a ↔ m ∈ a :=
  List.mem_toFinset

end FreeMonoid
