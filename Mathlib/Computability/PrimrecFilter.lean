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

/-- Filtering a list for elements that satisfy a decidable predicate is primitive recursive. -/
lemma list_filter {α} [Primcodable α] (f : α → Prop) [DecidablePred f]
(hf : PrimrecPred f) : Primrec fun L ↦ (filter (fun a ↦ f a) L) := by
  rw [← List.filterMap_eq_filter]
  apply listFilterMap Primrec.id
  simp only [Primrec₂, Option.guard, decide_eq_true_eq]
  exact ite (PrimrecPred.comp hf snd) (option_some_iff.mpr snd) (const none)

/-- Checking if any element of a list satisfies a decidable predicate is primitive recursive. -/
lemma filter_exists {α} [Primcodable α] (f : α → Prop) [DecidablePred f]
    (hf : PrimrecPred f) : PrimrecPred fun (L : List α) ↦ (∃ a ∈ L, f a) := by
  let g := fun L ↦ List.filter (fun a ↦ f a) L
  have h (L : List α): ((g L).length ≠ 0) ↔ (∃ a ∈ L, f a) := by simp [g]
  apply PrimrecPred.of_eq ?_ h
  apply PrimrecPred.not
  apply PrimrecRel.comp Primrec.eq ?_ (const 0)
  exact comp list_length (list_filter f hf)

/-- Checking if every element of a list satisfies a decidable predicate is primitive recursive. -/
lemma filter_forall {α} [Primcodable α] (f : α → Prop) [DecidablePred f]
    (hf : PrimrecPred f) : PrimrecPred fun (L : List α) ↦ (∀ a ∈ L, f a) := by
  let g := fun L ↦ List.filter (fun a ↦ f a) L
  have h (L : List α): ((g L).length = L.length) ↔ (∀ a ∈ L, f a) := by simp [g]
  apply PrimrecPred.of_eq ?_ h
  refine PrimrecRel.comp Primrec.eq ?_ list_length
  exact comp list_length (list_filter f hf)

/-- Bounded existential quantifiers are primitive recursive. -/
lemma bounded_exists (f : ℕ → Prop) [DecidablePred f] (hf : PrimrecPred f) :
    PrimrecPred fun n ↦ ∃ x < n, f x := by
  have h : PrimrecPred fun n ↦ (∃ a ∈ (range n), f a) :=
    PrimrecPred.comp (filter_exists f hf) list_range
  apply PrimrecPred.of_eq h (by simp)

/-- Bounded universal quantifiers are primitive recursive. -/
lemma bounded_forall (f : ℕ → Prop) [DecidablePred f] (hf : PrimrecPred f) :
    PrimrecPred fun n ↦ ∀ x < n, f x := by
  have h : PrimrecPred fun n ↦ (∀ a ∈ (range n), f a) :=
    PrimrecPred.comp (filter_forall f hf) list_range
  apply PrimrecPred.of_eq h (by simp)

end Primrec

namespace primrec₂

/-- If f a b is decidable, then given L : List α and b : β, it is primitive recurisve
to filter L for elements a with f a b -/

lemma list_filter {α β} [Primcodable α] [Primcodable β] (f : α → β → Prop)
    [DecidableRel f] (hf : PrimrecRel f) :
    Primrec₂ fun (L : List α) ↦ fun b ↦ (L.filter (fun a ↦ f a b)) := by
  let g (b : β) : α → Option α := (fun a ↦ (if f a b = True then a else Option.none))
  have h (b : β) (L : List α): L.filter (fun a ↦ f a b) = filterMap (g b) L := by
    simp only [eq_iff_iff, iff_true, g]
    rw [← List.filterMap_eq_filter]
    apply filterMap_congr
    simp [Option.guard]
  simp only [h]
  apply listFilterMap
  · exact fst
  · apply Primrec.ite
    · simp only [eq_iff_iff, iff_true]
      exact PrimrecRel.comp hf snd (Primrec.comp snd fst)
    · exact option_some_iff.mpr snd
    · exact Primrec.const Option.none

end primrec₂

namespace PrimrecRel

/-- If f a b is decidable, then given L : List α and b : β, "g L b ↔ ∃ a L, f a b"
is a primitive recurisve relation. -/

lemma filter_exists {α β} [Primcodable α] [Primcodable β] (f : α → β → Prop)
    [DecidableRel f] (hf : PrimrecRel f) :
    PrimrecRel fun (L : List α) ↦ fun b ↦ (∃ a ∈ L, f a b) := by
  let g (b : β) := fun L ↦ List.filter (fun a ↦ f a b) L
  have h (L : List α) (b : β) : (g b L).length ≠ 0 ↔ (∃ a ∈ L, f a b) := by simp [g]
  apply of_eq ?_ h
  unfold PrimrecRel Primrec₂
  simp only
  rw [← PrimrecPred]
  apply PrimrecPred.not
  refine PrimrecRel.comp Primrec.eq ?_ (const 0)
  apply Primrec.comp list_length
  refine Primrec₂.comp ?_ snd fst
  apply Primrec₂.swap
  exact primrec₂.list_filter f hf

/-- If f a b is decidable, then given L : List α and b : β, "g L b ↔ ∀ a L, f a b"
is a primitive recurisve relation. -/
lemma filter_forall {α β} [Primcodable α] [Primcodable β] (f : α → β → Prop)
    [DecidableRel f] (hf : PrimrecRel f) :
    PrimrecRel fun (L : List α) ↦ fun b ↦ (∀ a ∈ L, f a b) := by
  let g (b : β) := fun L ↦ List.filter (fun a ↦ f a b) L
  have h (L : List α) (b : β) : (g b L).length = L.length ↔ (∀ a ∈ L, f a b) := by simp [g]
  apply PrimrecRel.of_eq ?_ h
  unfold PrimrecRel Primrec₂
  simp only
  rw [← PrimrecPred]
  refine PrimrecRel.comp Primrec.eq ?_ (Primrec.comp list_length fst)
  apply Primrec.comp list_length
  refine Primrec₂.comp ?_ snd fst
  apply Primrec₂.swap
  exact primrec₂.list_filter f hf

/-- If f a b is decidable, then for any fixed n and y,  "g n y ↔ ∃ x < n, f x y" is a
primitive recursive relation. -/
lemma bounded_exists (f : ℕ → ℕ → Prop) [DecidableRel f]
    (hf : PrimrecRel f) : PrimrecRel (fun n ↦ (fun y ↦ (∃ x < n, f x y))) := by
  have h : PrimrecRel (fun n ↦ (fun y ↦ (∃ x ∈ range n, f x y))) :=
    PrimrecRel.comp (filter_exists f hf) (Primrec.comp list_range fst) snd
  apply PrimrecRel.of_eq h (by simp)

/-- If f a b is decidable, then for any fixed n and y,  "g n y ↔ ∀ x < n, f x y" is a
primitive recursive relation. -/
lemma bounded_forall (f : ℕ → ℕ → Prop) [DecidableRel f]
    (hf : PrimrecRel f) : PrimrecRel (fun n ↦ (fun y ↦ (∀ x < n, f x y))) := by
  have h : PrimrecRel (fun n ↦ (fun y ↦ (∀ x ∈ range n, f x y))) :=
    PrimrecRel.comp (filter_forall f hf) (Primrec.comp list_range fst) snd
  apply PrimrecRel.of_eq h (by simp)

end PrimrecRel

namespace Primrec

/-- A helper lemma for proofs about bounded quantifiers on decidable relations. -/
lemma nat_rel_list_filter (f : ℕ → ℕ → Prop) (s : ℕ) [DecidableRel f] (hf : PrimrecRel f) :
    Primrec fun n ↦ ((List.range (s)).filter (fun y ↦ f y n)) := by
  let g (n : ℕ): ℕ → Option Nat := (fun y ↦ (if f y n = True then y else Option.none))
  have h (n : ℕ): (range (s)).filter (fun y ↦ f y n) = filterMap (g n) (List.range s) := by
    simp only [eq_iff_iff, iff_true, g]
    rw [← List.filterMap_eq_filter]
    refine filterMap_congr ?_
    simp [Option.guard]
  simp only [h]
  apply listFilterMap
  · exact Primrec.const (range s)
  · apply Primrec.ite
    · simp only [eq_iff_iff, iff_true]
      exact PrimrecRel.comp hf snd fst
    · exact option_some_iff.mpr snd
    · exact Primrec.const Option.none

end Primrec

namespace PrimrecPred

/-- If f a b is decidable, then for any fixed n and y, "∃ x < n, f x y" is a
primitive recursive predicate in n. This is sometimes easier to work with than the fully
general case involving a primitive recursive relation. -/
lemma bounded_exists (f : ℕ → ℕ → Prop) (s : ℕ) [DecidableRel f]
    (hf : PrimrecRel f) :
    PrimrecPred (fun n ↦ ∃ y < s, (f y n)) := by
  have h1 : (fun n ↦ decide (∃ y < s, f y n)) =
            (fun n ↦ decide ((List.range s).filter (fun y ↦ f y n) ≠ [])) := by simp
  simp only [PrimrecPred, h1]
  apply PrimrecPred.not
  apply PrimrecRel.comp Primrec.eq ?_ (const [])
  apply nat_rel_list_filter hf

/-- If f a b is decidable, then for any fixed n and y, "∀ x < n, f x y" is a
primitive recursive predicate in n. This is sometimes easier to work with than the fully
general case involving a primitive recursive relation. -/
lemma bounded_forall (f : ℕ → ℕ → Prop) (s : ℕ) [DecidableRel f]
    (hf : PrimrecRel f) :
    PrimrecPred (fun n ↦ ∀ y < s, (f y n)) := by
  have h1 : (fun n ↦ decide (∀ y < s, f y n)) =
            (fun n ↦ decide ((List.range s).filter (fun y ↦ f y n) = List.range s)) := by simp
  simp only [PrimrecPred, h1]
  apply PrimrecRel.comp Primrec.eq
  · apply nat_rel_list_filter
    exact hf
  · exact Primrec.const (range s)

end PrimrecPred
