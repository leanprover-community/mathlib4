/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Batteries.Tactic.Alias
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
between direct and continuation-passing styles. That paper uses a version of `foldl` whose `f` has
type `α → β → β`, which not only removes the need for `flip` in the duality theorems' statements
but also allows slightly generalising the first theorem to

1. If `α = β`, `f` is associative and `a` commutes with all `x : α`, `l.foldl f a = l.foldr f a`

This file defines the modified version of `foldl` as `foldf`, using it to state the duality theorems
in their simplest and most general forms. Versions of the second theorem using `foldl` and `flip`
are derived as corollaries.

## Main declarations

* `List.foldf`: `List.foldl` with a type signature matching `List.foldr`.
* `List.foldl_eq_foldr_of_commute`, `List.foldl_eq_foldr`: first duality theorem.
* `List.foldf_eq_foldr`: second duality theorem.
* `List.foldf_reverse_eq_foldr`, `List.foldr_reverse_eq_foldf`: third duality theorem.
-/

@[expose] public section

universe u v

namespace List

variable {α : Type u} {β : Type v} {l : List α} {f : α → β → β} {v : β → α → β} {a : α} {b : β}

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
  | a :: l => l.foldf f (f a init)

@[simp, grind =] theorem foldf_nil : [].foldf f b = b := rfl
@[simp, grind =] theorem foldf_cons : (a :: l).foldf f b = l.foldf f (f a b) := rfl

@[simp]
theorem foldl_flip_eq_foldf : l.foldl (flip f) b = l.foldf f b := by
  induction l generalizing b <;> simp [flip, *]

@[simp]
theorem foldf_flip_eq_foldl : l.foldf (flip v) b = l.foldl v b := by
  induction l generalizing b <;> simp [flip, *]

@[simp]
theorem foldf_cons_eq_append {f : α → β} {l' : List β} :
    l.foldf (f · :: ·) l' = (l.map f).reverse ++ l' := by
  induction l generalizing l' <;> simp [*]

@[simp, grind =]
theorem foldf_cons_eq_append' {l' : List α} : l.foldf cons l' = l.reverse ++ l' := by
  induction l generalizing l' <;> simp [*]

theorem foldf_cons_nil : l.foldf cons [] = l.reverse := by simp

@[simp, grind _=_]
theorem foldf_append {l' : List α} : (l ++ l').foldf f b = l'.foldf f (l.foldf f b) := by
  induction l generalizing b <;> simp [*]

theorem foldl_cons_eq_apply_foldl [hv : RightCommutative v] :
    (a :: l).foldl v b = v (l.foldl v b) a := by
  rw [foldl_cons]
  induction l generalizing a b <;> simp [*, hv.right_comm]

theorem foldf_cons_eq_apply_foldf [hf : LeftCommutative f] :
    (a :: l).foldf f b = f a (l.foldf f b) := by
  rw [foldf_cons]
  induction l generalizing b <;> simp [*, hf.left_comm]

theorem foldr_cons_eq_foldr_apply [hf : LeftCommutative f] :
    (a :: l).foldr f b = l.foldr f (f a b) := by
  rw [foldr_cons]
  induction l generalizing a b <;> simp [*, hf.left_comm]

theorem foldl1_eq_foldr1 {f : α → α → α} [ha : Std.Associative f] {a b : α} :
    f (l.foldl f a) b = f a (l.foldr f b) := by
  induction l generalizing a <;> simp [*, ha.assoc]

/-- First Bird–Wadler duality theorem. -/
theorem foldl_eq_foldr_of_commute {f : α → α → α} [Std.Associative f] (ha : ∀ x, f a x = f x a) :
    l.foldl f a = l.foldr f a := by
  induction l <;> simp [*, foldl_assoc]

/-- First Bird–Wadler duality theorem for commutative functions. -/
theorem foldl_eq_foldr {f : α → α → α} [hf : Std.Commutative f] [Std.Associative f] :
    l.foldl f a = l.foldr f a :=
  foldl_eq_foldr_of_commute (hf.comm a)

/-- Second Bird–Wadler duality theorem. -/
theorem foldf_eq_foldr [LeftCommutative f] : l.foldf f b = l.foldr f b := by
  induction l <;> simp [*, foldf_cons_eq_apply_foldf, -foldf_cons]

theorem foldl_flip_eq_foldr [LeftCommutative f] : l.foldl (flip f) b = l.foldr f b := by
  rw [foldl_flip_eq_foldf, foldf_eq_foldr]

theorem foldr_flip_eq_foldl [RightCommutative v] : l.foldr (flip v) b = l.foldl v b := by
  unfold flip
  rw [← foldf_eq_foldr, ← foldf_flip_eq_foldl]
  rfl

/-- Third Bird–Wadler duality theorem.
Corresponds to `foldl_reverse` and `foldr_eq_foldl_reverse` in the standard library. -/
theorem foldf_reverse_eq_foldr : l.reverse.foldf f b = l.foldr f b := by
  induction l <;> simp [*]

/-- Third Bird–Wadler duality theorem.
Corresponds to `foldr_reverse` and `foldl_eq_foldr_reverse` in the standard library. -/
theorem foldr_reverse_eq_foldf : l.reverse.foldr f b = l.foldf f b := by
  induction l generalizing b <;> simp [*]

@[deprecated (since := "2026-02-24")] alias foldl_eq_of_comm' := foldl_cons_eq_apply_foldl
@[deprecated (since := "2026-02-24")] alias foldr_eq_of_comm' := foldr_cons_eq_foldr_apply
@[deprecated (since := "2026-02-24")] alias foldl_eq_foldr' := foldr_flip_eq_foldl
@[deprecated (since := "2026-02-24")] alias foldl_eq_of_comm_of_assoc := foldl_cons_eq_apply_foldl
@[deprecated (since := "2026-02-24")] alias foldl_op_eq_op_foldr_assoc := foldl1_eq_foldr1
@[deprecated (since := "2026-02-24")] alias foldl_assoc_comm_cons := foldl_cons_eq_apply_foldl

end List
