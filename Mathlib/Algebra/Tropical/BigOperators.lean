/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Data.List.MinMax
import Mathlib.Algebra.Tropical.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!

# Tropicalization of finitary operations

This file provides the "big-op" or notation-based finitary operations on tropicalized types.
This allows easy conversion between sums to Infs and prods to sums. Results here are important
for expressing that evaluation of tropical polynomials are the minimum over a finite piecewise
collection of linear functions.

## Main declarations

* `untrop_sum`

## Implementation notes

No concrete (semi)ring is used here, only ones with inferable order/lattice structure, to support
`Real`, `Rat`, `EReal`, and others (`ERat` is not yet defined).

Minima over `List α` are defined as producing a value in `WithTop α` so proofs about lists do not
directly transfer to minima over multisets or finsets.

-/

variable {R S : Type*}

open Tropical Finset

theorem List.trop_sum [AddMonoid R] (l : List R) : trop l.sum = List.prod (l.map trop) := by
  induction' l with hd tl IH
  · simp
  · simp [← IH]

theorem Multiset.trop_sum [AddCommMonoid R] (s : Multiset R) :
    trop s.sum = Multiset.prod (s.map trop) :=
  Quotient.inductionOn s (by simpa using List.trop_sum)

theorem trop_sum [AddCommMonoid R] (s : Finset S) (f : S → R) :
    trop (∑ i ∈ s, f i) = ∏ i ∈ s, trop (f i) := by
  convert Multiset.trop_sum (s.val.map f)
  simp only [Multiset.map_map, Function.comp_apply]
  rfl

theorem List.untrop_prod [AddMonoid R] (l : List (Tropical R)) :
    untrop l.prod = List.sum (l.map untrop) := by
  induction' l with hd tl IH
  · simp
  · simp [← IH]

theorem Multiset.untrop_prod [AddCommMonoid R] (s : Multiset (Tropical R)) :
    untrop s.prod = Multiset.sum (s.map untrop) :=
  Quotient.inductionOn s (by simpa using List.untrop_prod)

theorem untrop_prod [AddCommMonoid R] (s : Finset S) (f : S → Tropical R) :
    untrop (∏ i ∈ s, f i) = ∑ i ∈ s, untrop (f i) := by
  convert Multiset.untrop_prod (s.val.map f)
  simp only [Multiset.map_map, Function.comp_apply]
  rfl

theorem List.trop_minimum [LinearOrder R] (l : List R) :
    trop l.minimum = List.sum (l.map (trop ∘ WithTop.some)) := by
  induction' l with hd tl IH
  · simp
  · simp [List.minimum_cons, ← IH]

theorem Multiset.trop_inf [LinearOrder R] [OrderTop R] (s : Multiset R) :
    trop s.inf = Multiset.sum (s.map trop) := by
  induction' s using Multiset.induction with s x IH
  · simp
  · simp [← IH]

theorem Finset.trop_inf [LinearOrder R] [OrderTop R] (s : Finset S) (f : S → R) :
    trop (s.inf f) = ∑ i ∈ s, trop (f i) := by
  convert Multiset.trop_inf (s.val.map f)
  simp only [Multiset.map_map, Function.comp_apply]
  rfl

theorem trop_sInf_image [ConditionallyCompleteLinearOrder R] (s : Finset S) (f : S → WithTop R) :
    trop (sInf (f '' s)) = ∑ i ∈ s, trop (f i) := by
  rcases s.eq_empty_or_nonempty with (rfl | h)
  · simp only [Set.image_empty, coe_empty, sum_empty, WithTop.sInf_empty, trop_top]
  rw [← inf'_eq_csInf_image _ h, inf'_eq_inf, s.trop_inf]

theorem trop_iInf [ConditionallyCompleteLinearOrder R] [Fintype S] (f : S → WithTop R) :
    trop (⨅ i : S, f i) = ∑ i : S, trop (f i) := by
  rw [iInf, ← Set.image_univ, ← coe_univ, trop_sInf_image]

theorem Multiset.untrop_sum [LinearOrder R] [OrderTop R] (s : Multiset (Tropical R)) :
    untrop s.sum = Multiset.inf (s.map untrop) := by
  induction' s using Multiset.induction with s x IH
  · simp
  · simp only [sum_cons, untrop_add, map_cons, inf_cons, ← IH]

theorem Finset.untrop_sum' [LinearOrder R] [OrderTop R] (s : Finset S) (f : S → Tropical R) :
    untrop (∑ i ∈ s, f i) = s.inf (untrop ∘ f) := by
  convert Multiset.untrop_sum (s.val.map f)
  simp only [Multiset.map_map, Function.comp_apply, inf_def]

theorem untrop_sum_eq_sInf_image [ConditionallyCompleteLinearOrder R] (s : Finset S)
    (f : S → Tropical (WithTop R)) : untrop (∑ i ∈ s, f i) = sInf (untrop ∘ f '' s) := by
  rcases s.eq_empty_or_nonempty with (rfl | h)
  · simp only [Set.image_empty, coe_empty, sum_empty, WithTop.sInf_empty, untrop_zero]
  · rw [← inf'_eq_csInf_image _ h, inf'_eq_inf, Finset.untrop_sum']

theorem untrop_sum [ConditionallyCompleteLinearOrder R] [Fintype S] (f : S → Tropical (WithTop R)) :
    untrop (∑ i : S, f i) = ⨅ i : S, untrop (f i) := by
  rw [iInf, ← Set.image_univ, ← coe_univ, untrop_sum_eq_sInf_image, Function.comp_def]

/-- Note we cannot use `i ∈ s` instead of `i : s` here
as it is simply not true on conditionally complete lattices! -/
theorem Finset.untrop_sum [ConditionallyCompleteLinearOrder R] (s : Finset S)
    (f : S → Tropical (WithTop R)) : untrop (∑ i ∈ s, f i) = ⨅ i : s, untrop (f i) := by
  simpa [← _root_.untrop_sum] using (sum_attach _ _).symm
