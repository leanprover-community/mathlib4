/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn, Mario Carneiro, Martin Dvorak
-/
module

public import Mathlib.Tactic.GCongr.Core

/-!
# Join of a list of lists

This file proves basic properties of `List.flatten`, which concatenates a list of lists. It is
defined in `Init.Prelude`.
-/

public section

-- Make sure we don't import algebra
assert_not_exists Monoid

variable {α β : Type*}

namespace List

@[gcongr]
protected theorem Sublist.flatten {l₁ l₂ : List (List α)} (h : l₁ <+ l₂) :
    l₁.flatten <+ l₂.flatten := by
  induction h with grind

@[gcongr]
protected theorem Sublist.flatMap {l₁ l₂ : List α} (h : l₁ <+ l₂) (f : α → List β) :
    l₁.flatMap f <+ l₂.flatMap f :=
  (h.map f).flatten

protected theorem Sublist.flatMap_right (l : List α) {f g : α → List β} (h : ∀ a ∈ l, f a <+ g a) :
    l.flatMap f <+ l.flatMap g := by
  induction l with grind

/-- Taking only the first `i+1` elements in a list, and then dropping the first `i` ones, one is
left with a list of length `1` made of the `i`-th element of the original list. -/
theorem drop_take_succ_eq_cons_getElem (L : List α) (i : Nat) (h : i < L.length) :
    (L.take (i + 1)).drop i = [L[i]] := by
  induction L generalizing i with grind

/-- We can rebracket `x ++ (l₁ ++ x) ++ (l₂ ++ x) ++ ... ++ (lₙ ++ x)` to
`(x ++ l₁) ++ (x ++ l₂) ++ ... ++ (x ++ lₙ) ++ x` where `L = [l₁, l₂, ..., lₙ]`. -/
theorem append_flatten_map_append (L : List (List α)) (x : List α) :
    x ++ (L.map (· ++ x)).flatten = (L.map (x ++ ·)).flatten ++ x := by
  induction L with grind

/-- See also `head_flatten_eq_head_head`, which switches around the proof obligations. -/
theorem head_head_eq_head_flatten {l : List (List α)} (hl : l ≠ []) (hl' : l.head hl ≠ []) :
    (l.head hl).head hl' = l.flatten.head (flatten_ne_nil_iff.2 ⟨_, head_mem hl, hl'⟩) := by
  cases l with grind

/-- See also `head_head_eq_head_flatten`, which switches around the proof obligations. -/
theorem head_flatten_eq_head_head {l : List (List α)} (hl : l.flatten ≠ [])
    (hl' : l.head (by grind) ≠ []) : l.flatten.head hl = (l.head (by grind)).head hl' :=
  (head_head_eq_head_flatten ..).symm

/-- See also `getLast_flatten_of_flatten_ne_nil`, which switches around the proof obligations. -/
theorem getLast_flatten_of_getLast_ne_nil {l : List (List α)}
    (hl : l ≠ []) (hl' : l.getLast hl ≠ []) :
    l.flatten.getLast (flatten_ne_nil_iff.2 ⟨_, getLast_mem hl, hl'⟩) =
      (l.getLast hl).getLast hl' := by
  cases eq_nil_or_concat l with grind

/-- See also `getLast_flatten_of_getLast_ne_nil`, which switches around the proof obligations. -/
theorem getLast_flatten_of_flatten_ne_nil {l : List (List α)}
    (hl : l.flatten ≠ []) (hl' : l.getLast (by grind) ≠ []) :
    (l.getLast (by grind)).getLast hl' = l.flatten.getLast hl :=
  (getLast_flatten_of_getLast_ne_nil ..).symm

end List
