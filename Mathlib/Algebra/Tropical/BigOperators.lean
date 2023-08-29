/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.List.MinMax
import Mathlib.Algebra.Tropical.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset

#align_import algebra.tropical.big_operators from "leanprover-community/mathlib"@"d6fad0e5bf2d6f48da9175d25c3dc5706b3834ce"

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
`Real`, `Rat`, `EReal`, and others (`ERat` is not yet defined).

Minima over `List α` are defined as producing a value in `WithTop α` so proofs about lists do not
directly transfer to minima over multisets or finsets.

-/

open BigOperators

variable {R S : Type*}

open Tropical Finset

theorem List.trop_sum [AddMonoid R] (l : List R) : trop l.sum = List.prod (l.map trop) := by
  induction' l with hd tl IH
  -- ⊢ trop (sum []) = prod (map trop [])
  · simp
    -- 🎉 no goals
  · simp [← IH]
    -- 🎉 no goals
#align list.trop_sum List.trop_sum

theorem Multiset.trop_sum [AddCommMonoid R] (s : Multiset R) :
    trop s.sum = Multiset.prod (s.map trop) :=
  Quotient.inductionOn s (by simpa using List.trop_sum)
                             -- 🎉 no goals
#align multiset.trop_sum Multiset.trop_sum

theorem trop_sum [AddCommMonoid R] (s : Finset S) (f : S → R) :
    trop (∑ i in s, f i) = ∏ i in s, trop (f i) := by
  convert Multiset.trop_sum (s.val.map f)
  -- ⊢ ∏ i in s, trop (f i) = Multiset.prod (Multiset.map trop (Multiset.map f s.va …
  simp only [Multiset.map_map, Function.comp_apply]
  -- ⊢ ∏ i in s, trop (f i) = Multiset.prod (Multiset.map (fun i => trop (f i)) s.v …
  rfl
  -- 🎉 no goals
#align trop_sum trop_sum

theorem List.untrop_prod [AddMonoid R] (l : List (Tropical R)) :
    untrop l.prod = List.sum (l.map untrop) := by
  induction' l with hd tl IH
  -- ⊢ untrop (prod []) = sum (map untrop [])
  · simp
    -- 🎉 no goals
  · simp [← IH]
    -- 🎉 no goals
#align list.untrop_prod List.untrop_prod

theorem Multiset.untrop_prod [AddCommMonoid R] (s : Multiset (Tropical R)) :
    untrop s.prod = Multiset.sum (s.map untrop) :=
  Quotient.inductionOn s (by simpa using List.untrop_prod)
                             -- 🎉 no goals
#align multiset.untrop_prod Multiset.untrop_prod

theorem untrop_prod [AddCommMonoid R] (s : Finset S) (f : S → Tropical R) :
    untrop (∏ i in s, f i) = ∑ i in s, untrop (f i) := by
  convert Multiset.untrop_prod (s.val.map f)
  -- ⊢ ∑ i in s, untrop (f i) = Multiset.sum (Multiset.map untrop (Multiset.map f s …
  simp only [Multiset.map_map, Function.comp_apply]
  -- ⊢ ∑ i in s, untrop (f i) = Multiset.sum (Multiset.map (fun i => untrop (f i))  …
  rfl
  -- 🎉 no goals
#align untrop_prod untrop_prod

-- Porting note: replaced `coe` with `WithTop.some` in statement
theorem List.trop_minimum [LinearOrder R] (l : List R) :
    trop l.minimum = List.sum (l.map (trop ∘ WithTop.some)) := by
  induction' l with hd tl IH
  -- ⊢ trop (minimum []) = sum (map (trop ∘ WithTop.some) [])
  · simp
    -- 🎉 no goals
  · simp [List.minimum_cons, ← IH]
    -- 🎉 no goals
#align list.trop_minimum List.trop_minimum

theorem Multiset.trop_inf [LinearOrder R] [OrderTop R] (s : Multiset R) :
    trop s.inf = Multiset.sum (s.map trop) := by
  induction' s using Multiset.induction with s x IH
  -- ⊢ trop (inf 0) = sum (map trop 0)
  · simp
    -- 🎉 no goals
  · simp [← IH]
    -- 🎉 no goals
#align multiset.trop_inf Multiset.trop_inf

theorem Finset.trop_inf [LinearOrder R] [OrderTop R] (s : Finset S) (f : S → R) :
    trop (s.inf f) = ∑ i in s, trop (f i) := by
  convert Multiset.trop_inf (s.val.map f)
  -- ⊢ ∑ i in s, trop (f i) = Multiset.sum (Multiset.map trop (Multiset.map f s.val))
  simp only [Multiset.map_map, Function.comp_apply]
  -- ⊢ ∑ i in s, trop (f i) = Multiset.sum (Multiset.map (fun i => trop (f i)) s.val)
  rfl
  -- 🎉 no goals
#align finset.trop_inf Finset.trop_inf

theorem trop_sInf_image [ConditionallyCompleteLinearOrder R] (s : Finset S) (f : S → WithTop R) :
    trop (sInf (f '' s)) = ∑ i in s, trop (f i) := by
  rcases s.eq_empty_or_nonempty with (rfl | h)
  -- ⊢ trop (sInf (f '' ↑∅)) = ∑ i in ∅, trop (f i)
  · simp only [Set.image_empty, coe_empty, sum_empty, WithTop.sInf_empty, trop_top]
    -- 🎉 no goals
  rw [← inf'_eq_csInf_image _ h, inf'_eq_inf, s.trop_inf]
  -- 🎉 no goals
#align trop_Inf_image trop_sInf_image

theorem trop_iInf [ConditionallyCompleteLinearOrder R] [Fintype S] (f : S → WithTop R) :
    trop (⨅ i : S, f i) = ∑ i : S, trop (f i) := by
  rw [iInf, ← Set.image_univ, ← coe_univ, trop_sInf_image]
  -- 🎉 no goals
#align trop_infi trop_iInf

theorem Multiset.untrop_sum [LinearOrder R] [OrderTop R] (s : Multiset (Tropical R)) :
    untrop s.sum = Multiset.inf (s.map untrop) := by
  induction' s using Multiset.induction with s x IH
  -- ⊢ untrop (sum 0) = inf (map untrop 0)
  · simp
    -- 🎉 no goals
  · simp only [sum_cons, ge_iff_le, untrop_add, untrop_le_iff, map_cons, inf_cons, ← IH]
    -- ⊢ min (untrop s) (untrop (sum x)) = untrop s ⊓ untrop (sum x)
    rfl
    -- 🎉 no goals
#align multiset.untrop_sum Multiset.untrop_sum

theorem Finset.untrop_sum' [LinearOrder R] [OrderTop R] (s : Finset S) (f : S → Tropical R) :
    untrop (∑ i in s, f i) = s.inf (untrop ∘ f) := by
  convert Multiset.untrop_sum (s.val.map f)
  -- ⊢ inf s (untrop ∘ f) = Multiset.inf (Multiset.map untrop (Multiset.map f s.val))
  simp only [Multiset.map_map, Function.comp_apply]
  -- ⊢ inf s (untrop ∘ f) = Multiset.inf (Multiset.map (fun x => untrop (f x)) s.val)
  rfl
  -- 🎉 no goals
#align finset.untrop_sum' Finset.untrop_sum'

theorem untrop_sum_eq_sInf_image [ConditionallyCompleteLinearOrder R] (s : Finset S)
    (f : S → Tropical (WithTop R)) : untrop (∑ i in s, f i) = sInf (untrop ∘ f '' s) := by
  rcases s.eq_empty_or_nonempty with (rfl | h)
  -- ⊢ untrop (∑ i in ∅, f i) = sInf (untrop ∘ f '' ↑∅)
  · simp only [Set.image_empty, coe_empty, sum_empty, WithTop.sInf_empty, untrop_zero]
    -- 🎉 no goals
  · rw [← inf'_eq_csInf_image _ h, inf'_eq_inf, Finset.untrop_sum']
    -- 🎉 no goals
#align untrop_sum_eq_Inf_image untrop_sum_eq_sInf_image

theorem untrop_sum [ConditionallyCompleteLinearOrder R] [Fintype S] (f : S → Tropical (WithTop R)) :
    untrop (∑ i : S, f i) = ⨅ i : S, untrop (f i) := by
  rw [iInf,← Set.image_univ,← coe_univ, untrop_sum_eq_sInf_image]
  -- ⊢ sInf ((untrop ∘ fun i => f i) '' ↑univ) = sInf ((fun i => untrop (f i)) '' ↑ …
  rfl
  -- 🎉 no goals
#align untrop_sum untrop_sum

/-- Note we cannot use `i ∈ s` instead of `i : s` here
as it is simply not true on conditionally complete lattices! -/
theorem Finset.untrop_sum [ConditionallyCompleteLinearOrder R] (s : Finset S)
    (f : S → Tropical (WithTop R)) : untrop (∑ i in s, f i) = ⨅ i : s, untrop (f i) := by
  simpa [← _root_.untrop_sum] using sum_attach.symm
  -- 🎉 no goals
#align finset.untrop_sum Finset.untrop_sum
