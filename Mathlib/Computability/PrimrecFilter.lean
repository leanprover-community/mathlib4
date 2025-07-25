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

variable {α} [Primcodable α] (f : α → Prop) [DecidablePred f]

/-- Filtering a list for elements that satisfy a decidable predicate is primitive recursive. -/
lemma list_filter (hf : PrimrecPred f) : Primrec fun L ↦ (filter (fun a ↦ f a) L) := by
  rw [← List.filterMap_eq_filter]
  apply listFilterMap Primrec.id
  simp only [Primrec₂, Option.guard, decide_eq_true_eq]
  exact ite (PrimrecPred.comp hf snd) (option_some_iff.mpr snd) (const none)

/-- Checking if any element of a list satisfies a decidable predicate is primitive recursive. -/
lemma filter_exists (hf : PrimrecPred f) : PrimrecPred fun (L : List α) ↦ (∃ a ∈ L, f a) := by
  let g := fun L ↦ List.filter (fun a ↦ f a) L
  have h (L : List α): ((g L).length ≠ 0) ↔ (∃ a ∈ L, f a) := by simp [g]
  apply PrimrecPred.of_eq (PrimrecPred.not ?_) h
  exact PrimrecRel.comp Primrec.eq (comp list_length (list_filter f hf)) (const 0)

/-- Checking if every element of a list satisfies a decidable predicate is primitive recursive. -/
lemma filter_forall (hf : PrimrecPred f) : PrimrecPred fun (L : List α) ↦ (∀ a ∈ L, f a) := by
  let g := fun L ↦ List.filter (fun a ↦ f a) L
  have h (L : List α): ((g L).length = L.length) ↔ (∀ a ∈ L, f a) := by simp [g]
  apply PrimrecPred.of_eq ?_ h
  exact PrimrecRel.comp Primrec.eq (comp list_length (list_filter f hf)) list_length

variable (f : ℕ → Prop) [DecidablePred f]

/-- Bounded existential quantifiers are primitive recursive. -/
lemma bounded_exists (hf : PrimrecPred f) : PrimrecPred fun n ↦ ∃ x < n, f x :=
  PrimrecPred.of_eq (PrimrecPred.comp (filter_exists f hf) list_range) (by simp)

/-- Bounded universal quantifiers are primitive recursive. -/
lemma bounded_forall (hf : PrimrecPred f) : PrimrecPred fun n ↦ ∀ x < n, f x :=
  PrimrecPred.of_eq (PrimrecPred.comp (filter_forall f hf) list_range) (by simp)

end Primrec

namespace primrec₂

/-- If f a b is decidable, then given L : List α and b : β, it is primitive recurisve
to filter L for elements a with f a b -/

lemma filter_filtermap_lemma {α β : Type} (b : β) (f : α → β → Prop) (L : List α) [DecidableRel f] :
    L.filter (fun a ↦ f a b) =
    filterMap ((fun b a ↦ if f a b = True then some a else none) b) L := by
  rw [← List.filterMap_eq_filter]
  apply filterMap_congr
  simp only [Option.guard, decide_eq_true_eq, eq_iff_iff, iff_true, implies_true]

lemma list_filter {α β : Type} [Primcodable α] [Primcodable β] (f : α → β → Prop) [DecidableRel f]
    (hf : PrimrecRel f) : Primrec₂ fun (L : List α) ↦ fun b ↦ (L.filter (fun a ↦ f a b)) := by
  let g (b : β) : α → Option α := (fun a ↦ (if f a b = True then a else Option.none))
  have h (b : β) (L : List α) := filter_filtermap_lemma b f L
  simp only [h]
  refine listFilterMap fst (Primrec.ite ?_ (option_some_iff.mpr snd) (Primrec.const Option.none))
  simp only [eq_iff_iff, iff_true]
  exact PrimrecRel.comp hf snd (Primrec.comp snd fst)

end primrec₂

namespace PrimrecRel

variable {α β : Type} (f : α → β → Prop) [DecidableRel f]

/-- If f a b is decidable, then given L : List α and b : β, "g L b ↔ ∃ a L, f a b"
is a primitive recurisve relation. -/

lemma filter_length_ne_zero_exists (L : List α) (b : β) :
    ((fun L ↦ List.filter (fun a ↦ f a b) L) L).length ≠ 0 ↔ (∃ a ∈ L, f a b) := by simp

lemma filter_length_eq_length_for_all (L : List α) (b : β) :
    ((fun L ↦ List.filter (fun a ↦ f a b) L) L).length = L.length ↔ (∀ a ∈ L, f a b) := by simp

variable [Primcodable α] [Primcodable β]

lemma filter_exists (hf : PrimrecRel f) :
    PrimrecRel fun (L : List α) ↦ fun b ↦ (∃ a ∈ L, f a b) := by
  let g (b : β) := fun L ↦ List.filter (fun a ↦ f a b) L
  have h (L : List α) (b : β) : (g b L).length ≠ 0 ↔ (∃ a ∈ L, f a b) :=
    filter_length_ne_zero_exists f L b
  apply of_eq ?_ h
  apply PrimrecPred.not (PrimrecRel.comp Primrec.eq (Primrec.comp list_length ?_) (const 0))
  exact Primrec₂.comp (Primrec₂.swap (primrec₂.list_filter f hf)) snd fst

/-- If f a b is decidable, then given L : List α and b : β, "g L b ↔ ∀ a L, f a b"
is a primitive recurisve relation. -/
lemma filter_forall (hf : PrimrecRel f) :
    PrimrecRel fun (L : List α) ↦ fun b ↦ (∀ a ∈ L, f a b) := by
  let g (b : β) := fun L ↦ List.filter (fun a ↦ f a b) L
  have h (L : List α) (b : β) : (g b L).length = L.length ↔ (∀ a ∈ L, f a b) :=
    filter_length_eq_length_for_all f L b
  apply PrimrecRel.of_eq ?_ h
  unfold PrimrecRel Primrec₂
  rw [← PrimrecPred]
  apply PrimrecRel.comp Primrec.eq (Primrec.comp list_length ?_) (Primrec.comp list_length fst)
  exact Primrec₂.comp (Primrec₂.swap (primrec₂.list_filter f hf)) snd fst

variable (f : ℕ → ℕ → Prop) [DecidableRel f]

/-- If f a b is decidable, then for any fixed n and y,  "g n y ↔ ∃ x < n, f x y" is a
primitive recursive relation. -/
lemma bounded_exists (hf : PrimrecRel f) : PrimrecRel (fun n ↦ (fun y ↦ (∃ x < n, f x y))) := by
  have h : PrimrecRel (fun n ↦ (fun y ↦ (∃ x ∈ range n, f x y))) :=
    PrimrecRel.comp (filter_exists f hf) (Primrec.comp list_range fst) snd
  exact PrimrecRel.of_eq h (by simp)

/-- If f a b is decidable, then for any fixed n and y,  "g n y ↔ ∀ x < n, f x y" is a
primitive recursive relation. -/
lemma bounded_forall (hf : PrimrecRel f) : PrimrecRel (fun n ↦ (fun y ↦ (∀ x < n, f x y))) := by
  have h : PrimrecRel (fun n ↦ (fun y ↦ (∀ x ∈ range n, f x y))) :=
    PrimrecRel.comp (filter_forall f hf) (Primrec.comp list_range fst) snd
  exact PrimrecRel.of_eq h (by simp)

end PrimrecRel

namespace Primrec

/-- A helper lemma for proofs about bounded quantifiers on decidable relations. -/
lemma nat_rel_list_filter (f : ℕ → ℕ → Prop) (s : ℕ) [DecidableRel f] (hf : PrimrecRel f) :
    Primrec fun n ↦ ((List.range (s)).filter (fun y ↦ f y n)) := by
  let g (n : ℕ) : ℕ → Option Nat := (fun y ↦ (if f y n = True then y else Option.none))
  have h (n : ℕ) : (range (s)).filter (fun y ↦ f y n) = filterMap (g n) (List.range s) :=
    primrec₂.filter_filtermap_lemma n f (range s)
  simp only [h]
  refine listFilterMap (Primrec.const (range s)) ?_
  refine Primrec.ite ?_ (option_some_iff.mpr snd) (Primrec.const Option.none)
  simp only [eq_iff_iff, iff_true]
  exact PrimrecRel.comp hf snd fst

end Primrec

namespace PrimrecPred

variable (f : ℕ → ℕ → Prop) (s : ℕ) [DecidableRel f]

/-- If f a b is decidable, then for any fixed n and y, "∃ x < n, f x y" is a
primitive recursive predicate in n. This is sometimes easier to work with than the fully
general case involving a primitive recursive relation. -/
lemma bounded_exists (hf : PrimrecRel f) : PrimrecPred (fun n ↦ ∃ y < s, (f y n)) := by
  have h1 : (fun n ↦ decide (∃ y < s, f y n)) =
            (fun n ↦ decide ((List.range s).filter (fun y ↦ f y n) ≠ [])) := by simp
  simp only [PrimrecPred, h1]
  exact PrimrecPred.not (PrimrecRel.comp Primrec.eq (nat_rel_list_filter _ _ hf) (const []))

/-- If f a b is decidable, then for any fixed n and y, "∀ x < n, f x y" is a
primitive recursive predicate in n. This is sometimes easier to work with than the fully
general case involving a primitive recursive relation. -/
lemma bounded_forall (hf : PrimrecRel f) : PrimrecPred (fun n ↦ ∀ y < s, (f y n)) := by
  have h1 : (fun n ↦ decide (∀ y < s, f y n)) =
            (fun n ↦ decide ((List.range s).filter (fun y ↦ f y n) = List.range s)) := by simp
  simp only [PrimrecPred, h1]
  exact PrimrecRel.comp Primrec.eq (nat_rel_list_filter _ _ hf) (Primrec.const (range s))

end PrimrecPred
