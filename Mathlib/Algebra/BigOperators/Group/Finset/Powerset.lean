/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Powerset

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Big operators

In this file we prove theorems about products and sums over a `Finset.powerset`.

-/

public section

variable {α β : Type*}

variable {s : Finset α} {a : α}

namespace Finset

variable [CommMonoid β]

/-- A product over all subsets of `s ∪ {x}` is obtained by multiplying the product over all subsets
of `s`, and over all subsets of `s` to which one adds `x`. -/
@[to_additive /-- A sum over all subsets of `s ∪ {x}` is obtained by summing the sum over all
subsets of `s`, and over all subsets of `s` to which one adds `x`. -/]
lemma prod_powerset_insert [DecidableEq α] (ha : a ∉ s) (f : Finset α → β) :
    ∏ t ∈ (insert a s).powerset, f t =
      (∏ t ∈ s.powerset, f t) * ∏ t ∈ s.powerset, f (insert a t) := by
  rw [powerset_insert, prod_union, prod_image]
  · exact insert_erase_invOn.2.injOn.mono fun t ht ↦ notMem_mono (mem_powerset.1 ht) ha
  · aesop (add simp [disjoint_left, insert_subset_iff])

/-- A product over all subsets of `s ∪ {x}` is obtained by multiplying the product over all subsets
of `s`, and over all subsets of `s` to which one adds `x`. -/
@[to_additive /-- A sum over all subsets of `s ∪ {x}` is obtained by summing the sum over all
subsets of `s`, and over all subsets of `s` to which one adds `x`. -/]
lemma prod_powerset_cons (ha : a ∉ s) (f : Finset α → β) :
    ∏ t ∈ (s.cons a ha).powerset, f t = (∏ t ∈ s.powerset, f t) *
      ∏ t ∈ s.powerset.attach, f (cons a t <| notMem_mono (mem_powerset.1 t.2) ha) := by
  classical
  simp_rw [cons_eq_insert]
  rw [prod_powerset_insert ha, prod_attach _ fun t ↦ f (insert a t)]

set_option backward.isDefEq.respectTransparency false in
/-- A product over `powerset s` is equal to the double product over sets of subsets of `s` with
`#s = k`, for `k = 0, ..., #s`. -/
@[to_additive /-- A sum over `powerset s` is equal to the double sum over sets of subsets of `s`
with `#s = k`, for `k = 0, ..., #s` -/]
lemma prod_powerset (s : Finset α) (f : Finset α → β) :
    ∏ t ∈ powerset s, f t = ∏ j ∈ range (#s + 1), ∏ t ∈ powersetCard j s, f t := by
  rw [powerset_card_disjiUnion, prod_disjiUnion]

/-- A product over `Finset.powersetCard` which only depends on the size of the sets is constant. -/
@[to_additive
/-- A sum over `Finset.powersetCard` which only depends on the size of the sets is constant. -/]
lemma prod_powersetCard (n : ℕ) (s : Finset α) (f : ℕ → β) :
    ∏ t ∈ powersetCard n s, f #t = f n ^ (#s).choose n := by
  rw [prod_eq_pow_card, card_powersetCard]; rintro a ha; rw [(mem_powersetCard.1 ha).2]

/-- Multiply `f u` over all `r`-element subsets `u` of every `k`-element subset of `s`. If
`r ≤ k`, this equals the product over all `r`-element subsets of `s`, raised to
`Nat.choose (#s - r) (k - r)`. Indeed, each fixed `r`-element subset is contained in exactly that
many `k`-element subsets of `s`. -/
@[to_additive
/-- Sum `f u` over all `r`-element subsets `u` of every `k`-element subset of `s`. If `r ≤ k`,
this equals `Nat.choose (#s - r) (k - r)` times the sum over all `r`-element subsets of `s`.
Indeed, each fixed `r`-element subset is contained in exactly that many `k`-element subsets of
`s`. -/]
lemma prod_powersetCard_prod_powersetCard (r k : ℕ) (s : Finset α) (f : Finset α → β)
    (hrk : r ≤ k) :
    ∏ t ∈ s.powersetCard k, ∏ u ∈ t.powersetCard r, f u =
      (∏ u ∈ s.powersetCard r, f u) ^ ((s.card - r).choose (k - r)) := by
  classical
  calc
    ∏ t ∈ s.powersetCard k, ∏ u ∈ t.powersetCard r, f u =
        ∏ u ∈ s.powersetCard r,
          ∏ _t ∈ (s.powersetCard k).filter (u ⊆ ·), f u := by
      apply prod_comm'
      intro t u
      simp only [mem_powersetCard, mem_filter]
      constructor
      · rintro ⟨hts, hut⟩
        exact ⟨⟨hts, hut.1⟩, ⟨hut.1.trans hts.1, hut.2⟩⟩
      · rintro ⟨⟨hts, hut⟩, hus⟩
        exact ⟨hts, hut, hus.2⟩
    _ = ∏ u ∈ s.powersetCard r, f u ^ ((s.card - r).choose (k - r)) := by
      apply prod_congr rfl
      intro u hu
      obtain ⟨hus, rfl⟩ := mem_powersetCard.mp hu
      rw [prod_const, card_filter_powersetCard_subset u s k hus hrk]
    _ = (∏ u ∈ s.powersetCard r, f u) ^ ((s.card - r).choose (k - r)) := by
      exact prod_pow _ _ _

/-- Multiply `f x` over every element `x` of every `k`-element subset of `s`. If `0 < k`, this
equals the product over all elements of `s`, raised to `Nat.choose (#s - 1) (k - 1)`. Indeed, each
element of `s` is contained in exactly that many `k`-element subsets. -/
@[to_additive
/-- Sum `f x` over every element `x` of every `k`-element subset of `s`. If `0 < k`, this equals
`Nat.choose (#s - 1) (k - 1)` times the sum over all elements of `s`. Indeed, each element of `s`
is contained in exactly that many `k`-element subsets. -/]
lemma prod_powersetCard_prod (k : ℕ) (s : Finset α) (f : α → β) (hk : 0 < k) :
    ∏ t ∈ s.powersetCard k, ∏ x ∈ t, f x =
      (∏ x ∈ s, f x) ^ ((s.card - 1).choose (k - 1)) := by
  classical
  simpa only [powersetCard_one, prod_map, Function.Embedding.coeFn_mk, prod_singleton] using
    prod_powersetCard_prod_powersetCard 1 k s (fun u ↦ ∏ x ∈ u, f x) hk

end Finset
