/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky

! This file was ported from Lean 3 source module algebra.tropical.big_operators
! leanprover-community/mathlib commit d6fad0e5bf2d6f48da9175d25c3dc5706b3834ce
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Data.List.MinMax
import Mathbin.Algebra.Tropical.Basic
import Mathbin.Order.ConditionallyCompleteLattice.Finset

/-!

# Tropicalization of finitary operations

This file provides the "big-op" or notation-based finitary operations on tropicalized types.
This allows easy conversion between sums to Infs and prods to sums. Results here are important
for expressing that evaluation of tropical polynomials are the minimum over a finite piecewise
collection of linear functions.

## Main declarations

* `untrop_sum`

## Implementation notes

No concrete (semi)ring is used here, only ones with inferrable order/lattice structure, to support
real, rat, ereal, and others (erat is not yet defined).

Minima over `list α` are defined as producing a value in `with_top α` so proofs about lists do not
directly transfer to minima over multisets or finsets.

-/


open BigOperators

variable {R S : Type _}

open Tropical Finset

theorem List.trop_sum [AddMonoid R] (l : List R) : trop l.Sum = List.prod (l.map trop) :=
  by
  induction' l with hd tl IH
  · simp
  · simp [← IH]
#align list.trop_sum List.trop_sum

theorem Multiset.trop_sum [AddCommMonoid R] (s : Multiset R) :
    trop s.Sum = Multiset.prod (s.map trop) :=
  Quotient.inductionOn s (by simpa using List.trop_sum)
#align multiset.trop_sum Multiset.trop_sum

theorem trop_sum [AddCommMonoid R] (s : Finset S) (f : S → R) :
    trop (∑ i in s, f i) = ∏ i in s, trop (f i) :=
  by
  cases s
  convert Multiset.trop_sum _
  simp
#align trop_sum trop_sum

theorem List.untrop_prod [AddMonoid R] (l : List (Tropical R)) :
    untrop l.Prod = List.sum (l.map untrop) :=
  by
  induction' l with hd tl IH
  · simp
  · simp [← IH]
#align list.untrop_prod List.untrop_prod

theorem Multiset.untrop_prod [AddCommMonoid R] (s : Multiset (Tropical R)) :
    untrop s.Prod = Multiset.sum (s.map untrop) :=
  Quotient.inductionOn s (by simpa using List.untrop_prod)
#align multiset.untrop_prod Multiset.untrop_prod

theorem untrop_prod [AddCommMonoid R] (s : Finset S) (f : S → Tropical R) :
    untrop (∏ i in s, f i) = ∑ i in s, untrop (f i) :=
  by
  cases s
  convert Multiset.untrop_prod _
  simp
#align untrop_prod untrop_prod

theorem List.trop_minimum [LinearOrder R] (l : List R) :
    trop l.minimum = List.sum (l.map (trop ∘ coe)) :=
  by
  induction' l with hd tl IH
  · simp
  · simp [List.minimum_cons, ← IH]
#align list.trop_minimum List.trop_minimum

theorem Multiset.trop_inf [LinearOrder R] [OrderTop R] (s : Multiset R) :
    trop s.inf = Multiset.sum (s.map trop) :=
  by
  induction' s using Multiset.induction with s x IH
  · simp
  · simp [← IH]
#align multiset.trop_inf Multiset.trop_inf

theorem Finset.trop_inf [LinearOrder R] [OrderTop R] (s : Finset S) (f : S → R) :
    trop (s.inf f) = ∑ i in s, trop (f i) := by
  cases s
  convert Multiset.trop_inf _
  simp
#align finset.trop_inf Finset.trop_inf

theorem trop_infₛ_image [ConditionallyCompleteLinearOrder R] (s : Finset S) (f : S → WithTop R) :
    trop (infₛ (f '' s)) = ∑ i in s, trop (f i) :=
  by
  rcases s.eq_empty_or_nonempty with (rfl | h)
  · simp only [Set.image_empty, coe_empty, sum_empty, WithTop.infₛ_empty, trop_top]
  rw [← inf'_eq_cInf_image _ h, inf'_eq_inf, s.trop_inf]
#align trop_Inf_image trop_infₛ_image

theorem trop_infᵢ [ConditionallyCompleteLinearOrder R] [Fintype S] (f : S → WithTop R) :
    trop (⨅ i : S, f i) = ∑ i : S, trop (f i) := by
  rw [infᵢ, ← Set.image_univ, ← coe_univ, trop_infₛ_image]
#align trop_infi trop_infᵢ

theorem Multiset.untrop_sum [LinearOrder R] [OrderTop R] (s : Multiset (Tropical R)) :
    untrop s.Sum = Multiset.inf (s.map untrop) :=
  by
  induction' s using Multiset.induction with s x IH
  · simp
  · simpa [← IH]
#align multiset.untrop_sum Multiset.untrop_sum

theorem Finset.untrop_sum' [LinearOrder R] [OrderTop R] (s : Finset S) (f : S → Tropical R) :
    untrop (∑ i in s, f i) = s.inf (untrop ∘ f) :=
  by
  cases s
  convert Multiset.untrop_sum _
  simpa
#align finset.untrop_sum' Finset.untrop_sum'

theorem untrop_sum_eq_infₛ_image [ConditionallyCompleteLinearOrder R] (s : Finset S)
    (f : S → Tropical (WithTop R)) : untrop (∑ i in s, f i) = infₛ (untrop ∘ f '' s) :=
  by
  rcases s.eq_empty_or_nonempty with (rfl | h)
  · simp only [Set.image_empty, coe_empty, sum_empty, WithTop.infₛ_empty, untrop_zero]
  rw [← inf'_eq_cInf_image _ h, inf'_eq_inf, Finset.untrop_sum']
#align untrop_sum_eq_Inf_image untrop_sum_eq_infₛ_image

theorem untrop_sum [ConditionallyCompleteLinearOrder R] [Fintype S] (f : S → Tropical (WithTop R)) :
    untrop (∑ i : S, f i) = ⨅ i : S, untrop (f i) := by
  rw [infᵢ, ← Set.image_univ, ← coe_univ, untrop_sum_eq_infₛ_image]
#align untrop_sum untrop_sum

/-- Note we cannot use `i ∈ s` instead of `i : s` here
as it is simply not true on conditionally complete lattices! -/
theorem Finset.untrop_sum [ConditionallyCompleteLinearOrder R] (s : Finset S)
    (f : S → Tropical (WithTop R)) : untrop (∑ i in s, f i) = ⨅ i : s, untrop (f i) := by
  simpa [← untrop_sum] using sum_attach.symm
#align finset.untrop_sum Finset.untrop_sum

