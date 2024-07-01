/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Order.Chain

#align_import order.zorn from "leanprover-community/mathlib"@"46a64b5b4268c594af770c44d9e502afc6a515cb"

/-!
# Zorn's lemmas

This file proves several formulations of Zorn's Lemma.

## Variants

The primary statement of Zorn's lemma is `exists_maximal_of_chains_bounded`. Then it is specialized
to particular relations:
* `(≤)` with `zorn_partialOrder`
* `(⊆)` with `zorn_subset`
* `(⊇)` with `zorn_superset`

Lemma names carry modifiers:
* `₀`: Quantifies over a set, as opposed to over a type.
* `_nonempty`: Doesn't ask to prove that the empty chain is bounded and lets you give an element
  that will be smaller than the maximal element found (the maximal element is no smaller than any
  other element, but it can also be incomparable to some).

## How-to

This file comes across as confusing to those who haven't yet used it, so here is a detailed
walkthrough:
1. Know what relation on which type/set you're looking for. See Variants above. You can discharge
  some conditions to Zorn's lemma directly using a `_nonempty` variant.
2. Write down the definition of your type/set, put a `suffices ∃ m, ∀ a, m ≺ a → a ≺ m by ...`
  (or whatever you actually need) followed by an `apply some_version_of_zorn`.
3. Fill in the details. This is where you start talking about chains.

A typical proof using Zorn could look like this
```lean
lemma zorny_lemma : zorny_statement := by
  let s : Set α := {x | whatever x}
  suffices ∃ x ∈ s, ∀ y ∈ s, y ⊆ x → y = x by -- or with another operator xxx
    proof_post_zorn
  apply zorn_subset -- or another variant
  rintro c hcs hc
  obtain rfl | hcnemp := c.eq_empty_or_nonempty -- you might need to disjunct on c empty or not
  · exact ⟨edge_case_construction,
      proof_that_edge_case_construction_respects_whatever,
      proof_that_edge_case_construction_contains_all_stuff_in_c⟩
  · exact ⟨construction,
      proof_that_construction_respects_whatever,
      proof_that_construction_contains_all_stuff_in_c⟩
```

## Notes

Originally ported from Isabelle/HOL. The
[original file](https://isabelle.in.tum.de/dist/library/HOL/HOL/Zorn.html) was written by Jacques D.
Fleuriot, Tobias Nipkow, Christian Sternagel.
-/


open scoped Classical
open Set

variable {α β : Type*} {r : α → α → Prop} {c : Set α}

/-- Local notation for the relation being considered. -/
local infixl:50 " ≺ " => r

/-- **Zorn's lemma**

If every chain has an upper bound, then there exists a maximal element. -/
theorem exists_maximal_of_chains_bounded (h : ∀ c, IsChain r c → ∃ ub, ∀ a ∈ c, a ≺ ub)
    (trans : ∀ {a b c}, a ≺ b → b ≺ c → a ≺ c) : ∃ m, ∀ a, m ≺ a → a ≺ m :=
  have : ∃ ub, ∀ a ∈ maxChain r, a ≺ ub := h _ <| maxChain_spec.left
  let ⟨ub, (hub : ∀ a ∈ maxChain r, a ≺ ub)⟩ := this
  ⟨ub, fun a ha =>
    have : IsChain r (insert a <| maxChain r) :=
      maxChain_spec.1.insert fun b hb _ => Or.inr <| trans (hub b hb) ha
    hub a <| by
      rw [maxChain_spec.right this (subset_insert _ _)]
      exact mem_insert _ _⟩
#align exists_maximal_of_chains_bounded exists_maximal_of_chains_bounded

/-- A variant of Zorn's lemma. If every nonempty chain of a nonempty type has an upper bound, then
there is a maximal element.
-/
theorem exists_maximal_of_nonempty_chains_bounded [Nonempty α]
    (h : ∀ c, IsChain r c → c.Nonempty → ∃ ub, ∀ a ∈ c, a ≺ ub)
    (trans : ∀ {a b c}, a ≺ b → b ≺ c → a ≺ c) : ∃ m, ∀ a, m ≺ a → a ≺ m :=
  exists_maximal_of_chains_bounded
    (fun c hc =>
      (eq_empty_or_nonempty c).elim
        (fun h => ⟨Classical.arbitrary α, fun x hx => (h ▸ hx : x ∈ (∅ : Set α)).elim⟩) (h c hc))
    trans
#align exists_maximal_of_nonempty_chains_bounded exists_maximal_of_nonempty_chains_bounded

section Preorder

variable [Preorder α]

theorem zorn_preorder (h : ∀ c : Set α, IsChain (· ≤ ·) c → BddAbove c) :
    ∃ m : α, ∀ a, m ≤ a → a ≤ m :=
  exists_maximal_of_chains_bounded h le_trans
#align zorn_preorder zorn_preorder

theorem zorn_nonempty_preorder [Nonempty α]
    (h : ∀ c : Set α, IsChain (· ≤ ·) c → c.Nonempty → BddAbove c) : ∃ m : α, ∀ a, m ≤ a → a ≤ m :=
  exists_maximal_of_nonempty_chains_bounded h le_trans
#align zorn_nonempty_preorder zorn_nonempty_preorder

theorem zorn_preorder₀ (s : Set α)
    (ih : ∀ c ⊆ s, IsChain (· ≤ ·) c → ∃ ub ∈ s, ∀ z ∈ c, z ≤ ub) :
    ∃ m ∈ s, ∀ z ∈ s, m ≤ z → z ≤ m :=
  let ⟨⟨m, hms⟩, h⟩ :=
    @zorn_preorder s _ fun c hc =>
      let ⟨ub, hubs, hub⟩ :=
        ih (Subtype.val '' c) (fun _ ⟨⟨_, hx⟩, _, h⟩ => h ▸ hx)
          (by
            rintro _ ⟨p, hpc, rfl⟩ _ ⟨q, hqc, rfl⟩ hpq
            exact hc hpc hqc fun t => hpq (Subtype.ext_iff.1 t))
      ⟨⟨ub, hubs⟩, fun ⟨y, hy⟩ hc => hub _ ⟨_, hc, rfl⟩⟩
  ⟨m, hms, fun z hzs hmz => h ⟨z, hzs⟩ hmz⟩
#align zorn_preorder₀ zorn_preorder₀

theorem zorn_nonempty_preorder₀ (s : Set α)
    (ih : ∀ c ⊆ s, IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ s, ∀ z ∈ c, z ≤ ub) (x : α)
    (hxs : x ∈ s) : ∃ m ∈ s, x ≤ m ∧ ∀ z ∈ s, m ≤ z → z ≤ m := by
  -- Porting note: the first three lines replace the following two lines in mathlib3.
  -- The mathlib3 `rcases` supports holes for proof obligations, this is not yet implemented in 4.
  -- rcases zorn_preorder₀ ({ y ∈ s | x ≤ y }) fun c hcs hc => ?_ with ⟨m, ⟨hms, hxm⟩, hm⟩
  -- · exact ⟨m, hms, hxm, fun z hzs hmz => hm _ ⟨hzs, hxm.trans hmz⟩ hmz⟩
  have H := zorn_preorder₀ ({ y ∈ s | x ≤ y }) fun c hcs hc => ?_
  · rcases H with ⟨m, ⟨hms, hxm⟩, hm⟩
    exact ⟨m, hms, hxm, fun z hzs hmz => hm _ ⟨hzs, hxm.trans hmz⟩ hmz⟩
  · rcases c.eq_empty_or_nonempty with (rfl | ⟨y, hy⟩)
    · exact ⟨x, ⟨hxs, le_rfl⟩, fun z => False.elim⟩
    · rcases ih c (fun z hz => (hcs hz).1) hc y hy with ⟨z, hzs, hz⟩
      exact ⟨z, ⟨hzs, (hcs hy).2.trans <| hz _ hy⟩, hz⟩
#align zorn_nonempty_preorder₀ zorn_nonempty_preorder₀

theorem zorn_nonempty_Ici₀ (a : α)
    (ih : ∀ c ⊆ Ici a, IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub, ∀ z ∈ c, z ≤ ub)
    (x : α) (hax : a ≤ x) : ∃ m, x ≤ m ∧ ∀ z, m ≤ z → z ≤ m := by
  let ⟨m, _, hxm, hm⟩ := zorn_nonempty_preorder₀ (Ici a) (fun c hca hc y hy ↦ ?_) x hax
  · exact ⟨m, hxm, fun z hmz => hm _ (hax.trans <| hxm.trans hmz) hmz⟩
  · have ⟨ub, hub⟩ := ih c hca hc y hy; exact ⟨ub, (hca hy).trans (hub y hy), hub⟩
#align zorn_nonempty_Ici₀ zorn_nonempty_Ici₀

end Preorder

section PartialOrder

variable [PartialOrder α]

theorem zorn_partialOrder (h : ∀ c : Set α, IsChain (· ≤ ·) c → BddAbove c) :
    ∃ m : α, ∀ a, m ≤ a → a = m :=
  let ⟨m, hm⟩ := zorn_preorder h
  ⟨m, fun a ha => le_antisymm (hm a ha) ha⟩
#align zorn_partial_order zorn_partialOrder

theorem zorn_nonempty_partialOrder [Nonempty α]
    (h : ∀ c : Set α, IsChain (· ≤ ·) c → c.Nonempty → BddAbove c) : ∃ m : α, ∀ a, m ≤ a → a = m :=
  let ⟨m, hm⟩ := zorn_nonempty_preorder h
  ⟨m, fun a ha => le_antisymm (hm a ha) ha⟩
#align zorn_nonempty_partial_order zorn_nonempty_partialOrder

theorem zorn_partialOrder₀ (s : Set α)
    (ih : ∀ c ⊆ s, IsChain (· ≤ ·) c → ∃ ub ∈ s, ∀ z ∈ c, z ≤ ub) :
    ∃ m ∈ s, ∀ z ∈ s, m ≤ z → z = m :=
  let ⟨m, hms, hm⟩ := zorn_preorder₀ s ih
  ⟨m, hms, fun z hzs hmz => (hm z hzs hmz).antisymm hmz⟩
#align zorn_partial_order₀ zorn_partialOrder₀

theorem zorn_nonempty_partialOrder₀ (s : Set α)
    (ih : ∀ c ⊆ s, IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ s, ∀ z ∈ c, z ≤ ub) (x : α)
    (hxs : x ∈ s) : ∃ m ∈ s, x ≤ m ∧ ∀ z ∈ s, m ≤ z → z = m :=
  let ⟨m, hms, hxm, hm⟩ := zorn_nonempty_preorder₀ s ih x hxs
  ⟨m, hms, hxm, fun z hzs hmz => (hm z hzs hmz).antisymm hmz⟩
#align zorn_nonempty_partial_order₀ zorn_nonempty_partialOrder₀

end PartialOrder

theorem zorn_subset (S : Set (Set α))
    (h : ∀ c ⊆ S, IsChain (· ⊆ ·) c → ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub) :
    ∃ m ∈ S, ∀ a ∈ S, m ⊆ a → a = m :=
  zorn_partialOrder₀ S h
#align zorn_subset zorn_subset

theorem zorn_subset_nonempty (S : Set (Set α))
    (H : ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty → ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub) (x)
    (hx : x ∈ S) : ∃ m ∈ S, x ⊆ m ∧ ∀ a ∈ S, m ⊆ a → a = m :=
  zorn_nonempty_partialOrder₀ _ (fun _ cS hc y yc => H _ cS hc ⟨y, yc⟩) _ hx
#align zorn_subset_nonempty zorn_subset_nonempty

theorem zorn_superset (S : Set (Set α))
    (h : ∀ c ⊆ S, IsChain (· ⊆ ·) c → ∃ lb ∈ S, ∀ s ∈ c, lb ⊆ s) :
    ∃ m ∈ S, ∀ a ∈ S, a ⊆ m → a = m :=
  (@zorn_partialOrder₀ (Set α)ᵒᵈ _ S) fun c cS hc => h c cS hc.symm
#align zorn_superset zorn_superset

theorem zorn_superset_nonempty (S : Set (Set α))
    (H : ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty → ∃ lb ∈ S, ∀ s ∈ c, lb ⊆ s) (x)
    (hx : x ∈ S) : ∃ m ∈ S, m ⊆ x ∧ ∀ a ∈ S, a ⊆ m → a = m :=
  @zorn_nonempty_partialOrder₀ (Set α)ᵒᵈ _ S (fun _ cS hc y yc => H _ cS hc.symm ⟨y, yc⟩) _ hx
#align zorn_superset_nonempty zorn_superset_nonempty

/-- Every chain is contained in a maximal chain. This generalizes Hausdorff's maximality principle.
-/
theorem IsChain.exists_maxChain (hc : IsChain r c) : ∃ M, @IsMaxChain _ r M ∧ c ⊆ M := by
  -- Porting note: the first three lines replace the following two lines in mathlib3.
  -- The mathlib3 `obtain` supports holes for proof obligations, this is not yet implemented in 4.
  -- obtain ⟨M, ⟨_, hM₀⟩, hM₁, hM₂⟩ :=
  --   zorn_subset_nonempty { s | c ⊆ s ∧ IsChain r s } _ c ⟨Subset.rfl, hc⟩
  have H := zorn_subset_nonempty { s | c ⊆ s ∧ IsChain r s } ?_ c ⟨Subset.rfl, hc⟩
  · obtain ⟨M, ⟨_, hM₀⟩, hM₁, hM₂⟩ := H
    exact ⟨M, ⟨hM₀, fun d hd hMd => (hM₂ _ ⟨hM₁.trans hMd, hd⟩ hMd).symm⟩, hM₁⟩
  rintro cs hcs₀ hcs₁ ⟨s, hs⟩
  refine
    ⟨⋃₀cs, ⟨fun _ ha => Set.mem_sUnion_of_mem ((hcs₀ hs).left ha) hs, ?_⟩, fun _ =>
      Set.subset_sUnion_of_mem⟩
  rintro y ⟨sy, hsy, hysy⟩ z ⟨sz, hsz, hzsz⟩ hyz
  obtain rfl | hsseq := eq_or_ne sy sz
  · exact (hcs₀ hsy).right hysy hzsz hyz
  cases' hcs₁ hsy hsz hsseq with h h
  · exact (hcs₀ hsz).right (h hysy) hzsz hyz
  · exact (hcs₀ hsy).right hysy (h hzsz) hyz
#align is_chain.exists_max_chain IsChain.exists_maxChain
