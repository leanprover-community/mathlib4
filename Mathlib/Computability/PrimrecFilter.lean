/-
Copyright (c) 2025 David J. Webb. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David J. Webb
-/
import Mathlib.Computability.Primrec

/-!

# Bounded quantifiers are primitive recursive
This file contains lemmata for showing bounded existentially and universally quantified
statements are primitive recursive, as well as more general filtering for arbitrary
primcodable types.

## Main results
- Filtering for elements from a list that meet a primrec criterion is primrec
- Checking whether a list has some element meeting a primrec criterion is primrec
- Checking whether every element of a list meets a primrec criterion is primrec
- Primitive recursive functions are closed under bounded existential and universal quantifiers

## References
- [R. I. Soare *Turing Computability - Theory and Applications*] [Soare2016]
-/

open List Primrec

namespace Primrec

variable {α} [Primcodable α] {f : α → Prop} [DecidablePred f]

/-- Filtering a list for elements that satisfy a decidable predicate is primitive recursive. -/
lemma listFilter (hf : PrimrecPred f) : Primrec fun L ↦ filter (f ·) L := by
  rw [← List.filterMap_eq_filter]
  apply listFilterMap .id
  simp only [Primrec₂, Option.guard, decide_eq_true_eq]
  exact ite (hf.comp snd) (option_some_iff.mpr snd) (const none)

/-- Checking if any element of a list satisfies a decidable predicate is primitive recursive. -/
lemma exists_mem_list (hf : PrimrecPred f) : PrimrecPred fun L : List α ↦ ∃ a ∈ L, f a := by
  let g := fun L ↦ List.filter (f ·) L
  have h (L : List α) : (g L).length ≠ 0 ↔ ∃ a ∈ L, f a := by simp [g]
  apply PrimrecPred.of_eq (PrimrecPred.not ?_) h
  exact PrimrecRel.comp .eq (comp list_length (listFilter hf)) (const 0)

/-- Checking if every element of a list satisfies a decidable predicate is primitive recursive. -/
lemma forall_mem_list (hf : PrimrecPred f) : PrimrecPred fun L : List α ↦ ∀ a ∈ L, f a := by
  let g := fun L ↦ List.filter (f ·) L
  have h (L : List α): (g L).length = L.length ↔ ∀ a ∈ L, f a := by simp [g]
  apply PrimrecPred.of_eq ?_ h
  exact PrimrecRel.comp .eq (comp list_length (listFilter hf)) list_length

variable {f : ℕ → Prop} [DecidablePred f]

/-- Bounded existential quantifiers are primitive recursive. -/
lemma exists_lt (hf : PrimrecPred f) : PrimrecPred fun n ↦ ∃ x < n, f x :=
  of_eq (PrimrecPred.comp (exists_mem_list hf) list_range) (by simp)

/-- Bounded universal quantifiers are primitive recursive. -/
lemma forall_lt (hf : PrimrecPred f) : PrimrecPred fun n ↦ ∀ x < n, f x :=
  of_eq (PrimrecPred.comp (forall_mem_list hf) list_range) (by simp)

end Primrec

namespace Primrec₂

variable {α β : Type} {b : β} {f : α → β → Prop} {L : List α} [DecidableRel f]

/-- If `f a b` is decidable, then given `L : List α` and `b : β`, it is primitive recurisve
to filter `L` for elements `a` with `f a b` -/
lemma listFilter [Primcodable α] [Primcodable β] (hf : PrimrecRel f) :
    Primrec₂ fun (L : List α) b ↦ L.filter (fun a ↦ f a b) := by
  simp only [Eq.symm (filterMap_ite _ fun a ↦ f a _)]
  refine listFilterMap fst (Primrec.ite ?_ ?_ (Primrec.const Option.none))
  · exact PrimrecRel.comp hf snd (Primrec.comp snd fst)
  · exact Primrec.comp (option_some) snd

end Primrec₂

namespace PrimrecRel

variable {α β : Type} {f : α → β → Prop} [DecidableRel f] {L : List α} {b : β}

variable [Primcodable α] [Primcodable β]

/-- If `f a b` is decidable, then given `L : List α` and `b : β`, `"g L b ↔ ∃ a L, f a b"`
is a primitive recursive relation. -/
lemma filterExists (hf : PrimrecRel f) : PrimrecRel fun (L : List α) b ↦ ∃ a ∈ L, f a b := by
  have h (L) (b) : (filter (f · b) L).length ≠ 0 ↔ ∃ a ∈ L, f a b := by simp
  apply of_eq ?_ h
  apply PrimrecPred.not (comp Primrec.eq (Primrec.comp list_length ?_) (const 0))
  have h1 := Primrec₂.listFilter hf
  unfold Primrec₂ at h1
  simp only [h1]

/-- If `f a b` is decidable, then given `L : List α` and `b : β`, `"g L b ↔ ∀ a L, f a b"`
is a primitive recursive relation. -/
lemma filterForall (hf : PrimrecRel f) : PrimrecRel fun (L : List α) b ↦ ∀ a ∈ L, f a b := by
  have h (L) (b) : (filter (f · b) L).length = L.length ↔ ∀ a ∈ L, f a b := by simp
  apply of_eq ?_ h
  apply comp Primrec.eq (Primrec.comp list_length ?_) (Primrec.comp list_length fst)
  have h1 := Primrec₂.listFilter hf
  unfold Primrec₂ at h1
  simp only [h1]

variable {f : ℕ → ℕ → Prop} [DecidableRel f]

/-- If `f a b` is decidable, then for any fixed `n` and `y`,  `"g n y ↔ ∃ x < n, f x y"` is a
primitive recursive relation. -/
lemma exists_lt (hf : PrimrecRel f) : PrimrecRel fun n y ↦ ∃ x < n, f x y := by
  have h := comp (filterExists hf) (Primrec.comp list_range fst) snd
  exact PrimrecPred.of_eq h (by simp)

/-- If `f a b` is decidable, then for any fixed `n` and `y`,  `"g n y ↔ ∀ x < n, f x y"` is a
primitive recursive relation. -/
lemma forall_lt (hf : PrimrecRel f) : PrimrecRel fun n y ↦ ∀ x < n, f x y := by
  have h := comp (filterForall hf) (Primrec.comp list_range fst) snd
  exact PrimrecPred.of_eq h (by simp)

end PrimrecRel

namespace Primrec

/-- A helper lemma for proofs about bounded quantifiers on decidable relations. -/
lemma nat_rel_list_filter {f : ℕ → ℕ → Prop} (s : ℕ) [DecidableRel f] (hf : PrimrecRel f) :
    Primrec fun n ↦ (range s).filter (fun y ↦ f y n) := by
  simp only [Eq.symm (filterMap_ite (range s) fun a ↦ f a _)]
  refine listFilterMap (.const (range s)) ?_
  refine ite ?_ (option_some_iff.mpr snd) (.const Option.none)
  exact PrimrecRel.comp hf snd fst

end Primrec

namespace PrimrecPred

variable {f : ℕ → ℕ → Prop} (s : ℕ) [DecidableRel f]

/-- If `f a b` is decidable, then for any fixed `n` and `y`, `"∃ x < n, f x y"` is a
primitive recursive predicate in `n`. This is sometimes easier to work with than the fully
general case involving a primitive recursive relation. -/
lemma exists_lt (hf : PrimrecRel f) : PrimrecPred fun n ↦ ∃ y < s, f y n := by
  have h (n) : decide (∃ y < s, f y n) = decide ((List.range s).filter (f · n) ≠ []) := by simp
  simp only [PrimrecPred, h]
  exact not (PrimrecRel.comp Primrec.eq (nat_rel_list_filter _ hf) (const []))

/-- If `f a b` is decidable, then for any fixed `n` and `y`, `"∀ x < n, f x y"` is a
primitive recursive predicate in `n`. This is sometimes easier to work with than the fully
general case involving a primitive recursive relation. -/
lemma forall_lt (hf : PrimrecRel f) : PrimrecPred fun n ↦ ∀ y < s, f y n := by
  have h (n) : decide (∀ y < s, f y n) = decide ((range s).filter (fun y ↦ f y n) = range s) := by
    simp
  simp only [PrimrecPred, h]
  exact PrimrecRel.comp Primrec.eq (nat_rel_list_filter _ hf) (Primrec.const (range s))

end PrimrecPred
