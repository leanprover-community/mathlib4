/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.List.Perm

/-!
# Multisets
These are implemented as the quotient of a list by permutations.

TODO: This is currently extremely minimal,
containing only the definitions required to implement the `fin_cases` tactic.
Please update this module doc as changes are made,
eventually restoring the original mathlib3 module doc.
-/


open List Subtype Nat

variable {α : Type _} {β : Type _} {γ : Type _}

/-- `Multiset α` is the quotient of `List α` by list permutation. The result
  is a type of finite sets with duplicates allowed.  -/
def Multiset.{u} (α : Type u) : Type u :=
  Quotient (List.instSetoidList α)

section Mem

/-- `a ∈ s` means that `a` has nonzero multiplicity in `s`. -/
def Mem (a : α) (s : Multiset α) : Prop :=
  Quot.liftOn s (fun l => a ∈ l) fun l₁ l₂ (e : l₁ ~ l₂) => propext <| e.mem_iff

instance : Membership α (Multiset α) :=
  ⟨Mem⟩
