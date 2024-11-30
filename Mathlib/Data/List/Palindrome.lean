/-
Copyright (c) 2020 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Wong
-/
import Mathlib.Data.List.Basic

/-!
# Palindromes

This module defines *palindromes*, lists which are equal to their reverse.

The main result is the `Palindrome` inductive type, and its associated `Palindrome.rec` induction
principle. Also provided are conversions to and from other equivalent definitions.

## References

* [Pierre Castéran, *On palindromes*][casteran]

[casteran]: https://www.labri.fr/perso/casteran/CoqArt/inductive-prop-chap/palindrome.html

## Tags

palindrome, reverse, induction
-/


variable {α β : Type*}

namespace List

/-- `Palindrome l` asserts that `l` is a palindrome. This is defined inductively:

* The empty list is a palindrome;
* A list with one element is a palindrome;
* Adding the same element to both ends of a palindrome results in a bigger palindrome.
-/
inductive Palindrome : List α → Prop
  | nil : Palindrome []
  | singleton : ∀ x, Palindrome [x]
  | cons_concat : ∀ (x) {l}, Palindrome l → Palindrome (x :: (l ++ [x]))

namespace Palindrome

variable {l : List α}

theorem reverse_eq {l : List α} (p : Palindrome l) : reverse l = l := by
  induction p <;> try (exact rfl)
  simpa

theorem of_reverse_eq {l : List α} : reverse l = l → Palindrome l := by
  refine bidirectionalRecOn l (fun _ => Palindrome.nil) (fun a _ => Palindrome.singleton a) ?_
  intro x l y hp hr
  rw [reverse_cons, reverse_append] at hr
  rw [head_eq_of_cons_eq hr]
  have : Palindrome l := hp (append_inj_left' (tail_eq_of_cons_eq hr) rfl)
  exact Palindrome.cons_concat x this

theorem iff_reverse_eq {l : List α} : Palindrome l ↔ reverse l = l :=
  Iff.intro reverse_eq of_reverse_eq

theorem append_reverse (l : List α) : Palindrome (l ++ reverse l) := by
  apply of_reverse_eq
  rw [reverse_append, reverse_reverse]

protected theorem map (f : α → β) (p : Palindrome l) : Palindrome (map f l) :=
  of_reverse_eq <| by rw [← map_reverse, p.reverse_eq]

instance [DecidableEq α] (l : List α) : Decidable (Palindrome l) :=
  decidable_of_iff' _ iff_reverse_eq

end Palindrome

end List
