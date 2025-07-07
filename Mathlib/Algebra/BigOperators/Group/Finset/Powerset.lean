/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset

/-!
# Big operators

In this file we prove theorems about products and sums over a `Finset.powerset`.

-/

variable {α β γ : Type*}

variable {s : Finset α} {a : α}

namespace Finset

variable [CommMonoid β]

/-- A product over all subsets of `s ∪ {x}` is obtained by multiplying the product over all subsets
of `s`, and over all subsets of `s` to which one adds `x`. -/
@[to_additive "A sum over all subsets of `s ∪ {x}` is obtained by summing the sum over all subsets
of `s`, and over all subsets of `s` to which one adds `x`."]
lemma prod_powerset_insert [DecidableEq α] (ha : a ∉ s) (f : Finset α → β) :
    ∏ t ∈ (insert a s).powerset, f t =
      (∏ t ∈ s.powerset, f t) * ∏ t ∈ s.powerset, f (insert a t) := by
  rw [powerset_insert, prod_union, prod_image]
  · exact insert_erase_invOn.2.injOn.mono fun t ht ↦ notMem_mono (mem_powerset.1 ht) ha
  · aesop (add simp [disjoint_left, insert_subset_iff])

/-- A product over all subsets of `s ∪ {x}` is obtained by multiplying the product over all subsets
of `s`, and over all subsets of `s` to which one adds `x`. -/
@[to_additive "A sum over all subsets of `s ∪ {x}` is obtained by summing the sum over all subsets
of `s`, and over all subsets of `s` to which one adds `x`."]
lemma prod_powerset_cons (ha : a ∉ s) (f : Finset α → β) :
    ∏ t ∈ (s.cons a ha).powerset, f t = (∏ t ∈ s.powerset, f t) *
      ∏ t ∈ s.powerset.attach, f (cons a t <| notMem_mono (mem_powerset.1 t.2) ha) := by
  classical
  simp_rw [cons_eq_insert]
  rw [prod_powerset_insert ha, prod_attach _ fun t ↦ f (insert a t)]

/-- A product over `powerset s` is equal to the double product over sets of subsets of `s` with
`#s = k`, for `k = 1, ..., #s`. -/
@[to_additive "A sum over `powerset s` is equal to the double sum over sets of subsets of `s` with
`#s = k`, for `k = 1, ..., #s`"]
lemma prod_powerset (s : Finset α) (f : Finset α → β) :
    ∏ t ∈ powerset s, f t = ∏ j ∈ range (#s + 1), ∏ t ∈ powersetCard j s, f t := by
  rw [powerset_card_disjiUnion, prod_disjiUnion]

/-- A product over `Finset.powersetCard` which only depends on the size of the sets is constant. -/
@[to_additive
"A sum over `Finset.powersetCard` which only depends on the size of the sets is constant."]
lemma prod_powersetCard (n : ℕ) (s : Finset α) (f : ℕ → β) :
    ∏ t ∈ powersetCard n s, f #t = f n ^ (#s).choose n := by
  rw [prod_eq_pow_card, card_powersetCard]; rintro a ha; rw [(mem_powersetCard.1 ha).2]

end Finset
