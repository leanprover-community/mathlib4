/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Batteries.Logic
public import Mathlib.Tactic.Lemma
public import Mathlib.Tactic.TypeStar
public import Mathlib.Logic.OpClass

/-!
# Bird–Wadler duality of list folds

In their 1988 book _Introduction to Functional Programming_ [birdwadler],
Richard Bird and Philip Wadler stated three duality theorems between `foldl` and `foldr`.
Denoting the combining function as `f : α → β → β`, the theorems are:

1. If `α = β` and `f` is commutative and associative, `l.foldl = l.foldr`
2. If `f` is left-commutative, `l.foldl = l.foldr`
3. `l.reverse.foldl = l.foldr` and `l.reverse.foldr = l.foldl`

However, formalising these theorems in Lean (or Haskell or Scheme but not Rocq) presents a problem:
`f`'s type in `foldl` is `β → α → β`. The history behind this difference is explored in an
appendix to a paper by Olivier Danvy [danvy] about transforming functional programs
between direct and continuation-passing styles. This paper uses a version of `foldl` whose `f` has
type `α → β → β`, which not only removes the need for `flip` in the duality theorems' statements
but also allows slightly generalising the first theorem to

1. If `α = β`, `f` is associative and `a` is a commuting element, `l.foldl f a = l.foldr f a`

This file defines the modified version of `foldl` as `foldf`, using it to state the duality theorems
in their simplest and most general forms.
Versions of the second theorem using `foldl` and `flip` are derived as corollaries.
Note that versions of the third theorem using `foldl` and `flip` exist in Lean's standard library
as `foldl_reverse`, `foldr_reverse`, `foldl_eq_foldr_reverse` and `foldr_eq_foldl_reverse`.

## Main declarations

* `List.foldf`: `List.foldl` with a type signature matching `List.foldr`.
* `List.foldl_eq_foldr_of_commute`, `List.foldl_eq_foldr`: first duality theorem.
* `List.foldf_eq_foldr`: second duality theorem.
* `List.foldf_reverse_eq_foldr`, `List.foldr_reverse_eq_foldf`: third duality theorem.
-/

@[expose] public section

namespace List

variable {α β : Type*} {l : List α} {f : α → β → β} {v : β → α → β} {a : α} {b : β}

/--
Folds a function over a list from the left, accumulating a value starting with `init`.
The accumulated value is combined with the each element of the list in order, using `f`.

This function differs from `List.foldl` in that its type signature matches `List.foldr`:
`f` has type `α → β → β` instead of `β → α → β`.

Examples:
 * `[a, b, c].foldf f init = f c (f b (f a init))`
 * `[1, 2, 3].foldf (toString · ++ ·) "" = "321"`
 * `[1, 2, 3].foldf (s!"({·} {·})") "!" = "(3 (2 (1 !)))"`
-/
def foldf (f : α → β → β) (init : β) : List α → β
  | []     => init
  | a :: l => foldf f (f a init) l

@[simp, grind =] lemma foldf_nil : [].foldf f b = b := rfl
@[simp, grind =] lemma foldf_cons : (a :: l).foldf f b = l.foldf f (f a b) := rfl

@[simp]
lemma foldl_flip_eq_foldf : l.foldl (flip f) b = l.foldf f b := by
  induction l generalizing b <;> simp [flip, *]

@[simp]
lemma foldf_flip_eq_foldl : l.foldf (flip v) b = l.foldl v b := by
  induction l generalizing b <;> simp [flip, *]

@[simp]
lemma foldf_cons_eq_append {f : α → β} {l' : List β} :
    l.foldf (f · :: ·) l' = (l.map f).reverse ++ l' := by
  induction l generalizing l' <;> simp [*]

/-- Variant of `foldf_cons_eq_append` specalized to `f = id`. -/
@[simp, grind =]
lemma foldf_cons_eq_append' {l' : List α} : l.foldf cons l' = l.reverse ++ l' := by
  induction l generalizing l' <;> simp [*]

lemma foldf_cons_nil : l.foldf cons [] = l.reverse := by simp

@[simp, grind _=_]
lemma foldf_append {l' : List α} : (l ++ l').foldf f b = l'.foldf f (l.foldf f b) := by
  induction l generalizing b <;> simp [*]

lemma foldl_permute [hv : RightCommutative v] : l.foldl v (v b a) = v (l.foldl v b) a := by
  induction l generalizing a b <;> simp [*, hv.right_comm]

lemma foldf_permute [hf : LeftCommutative f] : l.foldf f (f a b) = f a (l.foldf f b) := by
  induction l generalizing b <;> simp [*, hf.left_comm]

lemma foldr_permute [hf : LeftCommutative f] : l.foldr f (f a b) = f a (l.foldr f b) := by
  induction l <;> simp [*, hf.left_comm]

/-- First Bird–Wadler duality theorem. -/
theorem foldl_eq_foldr_of_commute {f : α → α → α} [Std.Associative f] (ha : ∀ x, f a x = f x a) :
    l.foldl f a = l.foldr f a := by
  induction l <;> simp [*, foldl_assoc]

/-- First Bird–Wadler duality theorem for commutative functions. -/
theorem foldl_eq_foldr {f : α → α → α} [hf : Std.Commutative f] [Std.Associative f] :
    l.foldl f a = l.foldr f a :=
  foldl_eq_foldr_of_commute (hf.comm _)

/-- Second Bird–Wadler duality theorem. -/
theorem foldf_eq_foldr [LeftCommutative f] : l.foldf f b = l.foldr f b := by
  induction l <;> simp [*, foldf_permute]

lemma foldl_flip_eq_foldr [LeftCommutative f] : l.foldl (flip f) b = l.foldr f b := by
  rw [foldl_flip_eq_foldf, foldf_eq_foldr]

lemma foldr_flip_eq_foldl [RightCommutative v] : l.foldr (flip v) b = l.foldl v b := by
  have : flip (flip v) = v := rfl
  rw [← this, foldl_flip_eq_foldf, this, foldf_eq_foldr]

/-- Third Bird–Wadler duality theorem. -/
theorem foldf_reverse_eq_foldr : l.reverse.foldf f b = l.foldr f b := by
  induction l <;> simp [*]

/-- Third Bird–Wadler duality theorem. -/
theorem foldr_reverse_eq_foldf : l.reverse.foldr f b = l.foldf f b := by
  induction l generalizing b <;> simp [*]

@[deprecated (since := "2026-02-24")] alias foldl_eq_of_comm' := foldl_permute
@[deprecated (since := "2026-02-24")] alias foldr_eq_of_comm' := foldr_permute
@[deprecated (since := "2026-02-24")] alias foldl_eq_foldr' := foldr_flip_eq_foldl

end List
