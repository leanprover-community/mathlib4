/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau, Yury Kudryashov
-/
import Mathlib.Data.List.Pairwise

/-!
# Relation Chain
This file provides basic results about `List.Chain` (definition in `data.List.defs`).
A List `[a₂, ..., aₙ]` is a `Chain` starting at `a₁` with respect to the relation `r` if `r a₁ a₂`
and `r a₂ a₃` and ... and `r aₙ₋₁ aₙ`. We write it `Chain r a₁ [a₂, ..., aₙ]`.
A graph-specialized version is in development and will hopefully be added under `combinatorics.`
sometime soon.
-/

open Nat

namespace List

variable {α : Type u} {β : Type v} {R r : α → α → Prop} {l l₁ l₂ : List α} {a b : α}


protected lemma Pairwise.Chain (p : Pairwise R (a :: l)) : Chain R a l := by
  have ⟨r, p'⟩ := Pairwise_cons.1 p; clear p
  induction p' generalizing a with
  | nil => exact Chain.nil
  | cons r' _ ih =>
    simp only [Chain_cons, forall_mem_cons] at r
    exact Chain_cons.2 ⟨r.1, ih r'⟩

protected lemma Chain.Pairwise [Trans R R R] :
  ∀ {a : α} {l : List α}, Chain R a l → Pairwise R (a :: l)
| a, [], Chain.nil => Pairwise_singleton _ _
| a, _, (@Chain.cons _ _ _ b l h hb) => by
    refine Pairwise.cons ?_ ?_
    · sorry
    · sorry
    -- hb.Pairwise.cons begin
    -- simp only [mem_cons_iff, forall_eq_or_imp, h, true_and]
    -- exact λ c hc => trans h (rel_of_Pairwise_cons hb.Pairwise hc)

theorem Chain_iff_Pairwise [Trans R R R] {a : α} {l : List α} :
  Chain R a l ↔ Pairwise R (a :: l) :=
⟨Chain.Pairwise, Pairwise.Chain⟩
