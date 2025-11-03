/-
Copyright (c) 2025 Bernhard Reinke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amir Livne Bar-on, Bernhard Reinke
-/
import Mathlib.Data.List.Induction
import Mathlib.GroupTheory.FreeGroup.Basic

/-!
This file defines some extra lemmas for free groups, in particular about cyclically reduced words.

## Main declarations

* `FreeGroup.IsCyclicallyReduced`: the predicate for cyclically reduced words

-/
open List

universe u

variable {α : Type u}
namespace FreeGroup

variable {L L₁ L₂ : List (α × Bool)}

/-- Predicate asserting that the word `L` is cyclically reduced, i.e., it is reduced and furthermore
the first and the last letter of the word do not cancel. The empty word is by convention also
cyclically reduced. -/
@[to_additive /-- Predicate asserting that the word `L` is cyclically reduced, i.e., it is reduced
and furthermore the first and the last letter of the word do not cancel. The empty word is by
convention also cyclically reduced. -/]
def IsCyclicallyReduced (L : List (α × Bool)) : Prop :=
  IsReduced L ∧ ∀ a ∈ L.getLast?, ∀ b ∈ L.head?, a.1 = b.1 → a.2 = b.2

@[to_additive]
theorem isCyclicallyReduced_iff :
    IsCyclicallyReduced L ↔
    IsReduced L ∧ ∀ a ∈ L.getLast?, ∀ b ∈ L.head?, a.1 = b.1 → a.2 = b.2 := Iff.rfl

@[to_additive]
theorem isCyclicallyReduced_cons_append_iff {a b : α × Bool} :
    IsCyclicallyReduced (b :: L ++ [a]) ↔
    IsReduced (b :: L ++ [a]) ∧ (a.1 = b.1 → a.2 = b.2) := by
  rw [isCyclicallyReduced_iff, List.getLast?_concat]
  simp

namespace IsCyclicallyReduced

@[to_additive (attr := simp)]
protected theorem nil : IsCyclicallyReduced ([] : List (α × Bool)) := by
  simp [IsCyclicallyReduced]

@[to_additive (attr := simp)]
protected theorem singleton {x : (α × Bool)} : IsCyclicallyReduced [x] := by
  simp [IsCyclicallyReduced]


@[to_additive]
theorem isReduced (h : IsCyclicallyReduced L) : IsReduced L := h.1

@[to_additive]
theorem flatten_replicate (n : ℕ) (h : IsCyclicallyReduced L) :
    IsCyclicallyReduced (List.replicate n L).flatten := by match n, L with
  | 0, _ => simp
  | n + 1, [] => simp
  | n + 1, (head :: tail) =>
    rw [isCyclicallyReduced_iff, IsReduced, List.isChain_flatten (by simp)]
    refine ⟨⟨by simpa [IsReduced] using h.isReduced, List.isChain_replicate_of_rel _ h.2⟩,
      fun _ ha _ hb ↦ ?_⟩
    rw [Option.mem_def, List.getLast?_flatten_replicate (h := by simp +arith)] at ha
    rw [Option.mem_def, List.head?_flatten_replicate (h := by simp +arith)] at hb
    exact h.2 _ ha _ hb

end IsCyclicallyReduced

/-- This function produces a subword of a word `w` by cancelling the first and last letters of `w`
as long as possible. If `w` is reduced, the resulting word will be cyclically reduced. -/
@[to_additive /-- This function produces a subword of a word `w` by cancelling the first and last
letters of `w` as long as possible. If `w` is reduced, the resulting word will be cyclically
reduced. -/]
def reduceCyclically [DecidableEq α] : List (α × Bool) → List (α × Bool) :=
  List.bidirectionalRec
    (nil := [])
    (singleton := fun x => [x])
    (cons_append := fun a l b rC => if b.1 = a.1 ∧ (!b.2) = a.2 then rC else a :: l ++ [b])

namespace reduceCyclically
variable [DecidableEq α]

@[to_additive (attr := simp)]
protected theorem nil : reduceCyclically ([] : List (α × Bool)) = [] := by simp [reduceCyclically]

@[to_additive (attr := simp)]
protected theorem singleton {a : α × Bool} : reduceCyclically [a] = [a] := by
  simp [reduceCyclically]

@[to_additive]
protected theorem cons_append {a b : α × Bool} (l : List (α × Bool)) :
    reduceCyclically (a :: (l ++ [b])) =
    if b.1 = a.1 ∧ (!b.2) = a.2 then reduceCyclically l else a :: l ++ [b] := by
  simp [reduceCyclically]


@[to_additive]
theorem isCyclicallyReduced (w : List (α × Bool)) (h : IsReduced w) :
    IsCyclicallyReduced (reduceCyclically w) := by
  induction w using List.bidirectionalRec
  case nil => simp
  case singleton => simp
  case cons_append a l b ih =>
    rw [reduceCyclically.cons_append]
    split
    case isTrue => exact ih (h.infix ⟨[a], [b], rfl⟩)
    case isFalse h' =>
      rw [isCyclicallyReduced_cons_append_iff]
      exact ⟨h, by simpa using h'⟩

/-- Partner function to `reduceCyclically`. See `reduceCyclically.conjugation`. -/
@[to_additive /-- Partner function to `reduceCyclically`. See `reduceCyclically.conjugation`. -/]
def conjugator : List (α × Bool) → List (α × Bool) :=
  List.bidirectionalRec
    (nil := [])
    (singleton := fun _ => [])
    (cons_append := fun a _ b rCC => if b.1 = a.1 ∧ (!b.2) = a.2 then a :: rCC else [] )

@[to_additive (attr := simp)]
protected theorem conjugator.nil : conjugator ([] : List (α × Bool)) = [] := by simp [conjugator]

@[to_additive (attr := simp)]
protected theorem conjugator.singleton {a : α × Bool} : conjugator [a] = [] := by simp [conjugator]

@[to_additive]
protected theorem conjugator.cons_append {a b : α × Bool} (l : List (α × Bool)) :
    conjugator (a :: (l ++ [b])) = if b.1 = a.1 ∧ (!b.2) = a.2 then a :: conjugator l else [] := by
  simp [conjugator]

@[to_additive]
theorem conj_conjugator_reduceCyclically (w : List (α × Bool)) :
    conjugator w ++ reduceCyclically w ++ invRev (conjugator w) = w := by
  induction w using List.bidirectionalRec
  case nil => simp
  case singleton => simp
  case cons_append a l b eq =>
    rw [reduceCyclically.cons_append, conjugator.cons_append]
    split
    case isTrue h =>
      nth_rw 4 [← eq]
      simp [invRev, h.1.symm, h.2.symm]
    case isFalse => simp

end reduceCyclically
end FreeGroup
