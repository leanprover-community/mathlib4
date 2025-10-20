/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Order.Filter.Tendsto
import Mathlib.Data.PFun

/-!
# `Tendsto` for relations and partial functions

This file generalizes `Filter` definitions from functions to partial functions and relations.

## Considering functions and partial functions as relations

A function `f : α → β` can be considered as the relation `Rel α β` which relates `x` and `f x` for
all `x`, and nothing else. This relation is called `Function.Graph f`.

A partial function `f : α →. β` can be considered as the relation `Rel α β` which relates `x` and
`f x` for all `x` for which `f x` exists, and nothing else. This relation is called
`PFun.Graph' f`.

In this regard, a function is a relation for which every element in `α` is related to exactly one
element in `β` and a partial function is a relation for which every element in `α` is related to at
most one element in `β`.

This file leverages this analogy to generalize `Filter` definitions from functions to partial
functions and relations.

## Notes

`Set.preimage` can be generalized to relations in two ways:
* `Rel.preimage` returns the image of the set under the inverse relation.
* `Rel.core` returns the set of elements that are only related to those in the set.
Both generalizations are sensible in the context of filters, so `Filter.comap` and `Filter.Tendsto`
get two generalizations each.

We first take care of relations. Then the definitions for partial functions are taken as special
cases of the definitions for relations.
-/


universe u v w

namespace Filter

variable {α : Type u} {β : Type v} {γ : Type w}

open Filter

/-! ### Relations -/


/-- The forward map of a filter under a relation. Generalization of `Filter.map` to relations. Note
that `Rel.core` generalizes `Set.preimage`. -/
def rmap (r : SetRel α β) (l : Filter α) : Filter β where
  sets := { s | r.core s ∈ l }
  univ_sets := by simp
  sets_of_superset hs st := mem_of_superset hs (SetRel.core_mono st)
  inter_sets hs ht := by
    simp only [Set.mem_setOf_eq]
    convert inter_mem hs ht
    rw [← SetRel.core_inter]

theorem rmap_sets (r : SetRel α β) (l : Filter α) : (l.rmap r).sets = r.core ⁻¹' l.sets :=
  rfl

@[simp]
theorem mem_rmap (r : SetRel α β) (l : Filter α) (s : Set β) : s ∈ l.rmap r ↔ r.core s ∈ l :=
  Iff.rfl

@[simp]
theorem rmap_rmap (r : SetRel α β) (s : SetRel β γ) (l : Filter α) :
    rmap s (rmap r l) = rmap (r.comp s) l :=
  filter_eq <| by simp [rmap_sets, Set.preimage, SetRel.core_comp]

@[simp]
theorem rmap_compose (r : SetRel α β) (s : SetRel β γ) : rmap s ∘ rmap r = rmap (r.comp s) :=
  funext <| rmap_rmap _ _

/-- Generic "limit of a relation" predicate. `RTendsto r l₁ l₂` asserts that for every
`l₂`-neighborhood `a`, the `r`-core of `a` is an `l₁`-neighborhood. One generalization of
`Filter.Tendsto` to relations. -/
def RTendsto (r : SetRel α β) (l₁ : Filter α) (l₂ : Filter β) :=
  l₁.rmap r ≤ l₂

theorem rtendsto_def (r : SetRel α β) (l₁ : Filter α) (l₂ : Filter β) :
    RTendsto r l₁ l₂ ↔ ∀ s ∈ l₂, r.core s ∈ l₁ :=
  Iff.rfl

/-- One way of taking the inverse map of a filter under a relation. One generalization of
`Filter.comap` to relations. Note that `Rel.core` generalizes `Set.preimage`. -/
def rcomap (r : SetRel α β) (f : Filter β) : Filter α where
  sets := SetRel.image {(s, t) : _ × _ | r.core s ⊆ t} f.sets
  univ_sets := ⟨Set.univ, univ_mem, Set.subset_univ _⟩
  sets_of_superset := fun ⟨a', ha', ma'a⟩ ab => ⟨a', ha', ma'a.trans ab⟩
  inter_sets := fun ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩ =>
    ⟨a' ∩ b', inter_mem ha₁ hb₁, (r.core_inter a' b').subset.trans (Set.inter_subset_inter ha₂ hb₂)⟩

theorem rcomap_sets (r : SetRel α β) (f : Filter β) :
    (rcomap r f).sets = SetRel.image {(s, t) : _ × _ | r.core s ⊆ t} f.sets :=
  rfl

theorem rcomap_rcomap (r : SetRel α β) (s : SetRel β γ) (l : Filter γ) :
    rcomap r (rcomap s l) = rcomap (r.comp s) l :=
  filter_eq <| by
    ext t
    simp only [rcomap_sets, SetRel.image, Filter.mem_sets, Set.mem_setOf_eq, SetRel.core_comp]
    constructor
    · rintro ⟨u, ⟨v, vsets, hv⟩, h⟩
      exact ⟨v, vsets, Set.Subset.trans (SetRel.core_mono hv) h⟩
    rintro ⟨t, tsets, ht⟩
    exact ⟨SetRel.core s t, ⟨t, tsets, Set.Subset.rfl⟩, ht⟩

@[simp]
theorem rcomap_compose (r : SetRel α β) (s : SetRel β γ) :
    rcomap r ∘ rcomap s = rcomap (r.comp s) :=
  funext <| rcomap_rcomap _ _

theorem rtendsto_iff_le_rcomap (r : SetRel α β) (l₁ : Filter α) (l₂ : Filter β) :
    RTendsto r l₁ l₂ ↔ l₁ ≤ l₂.rcomap r := by
  rw [rtendsto_def]
  simp_rw [← l₂.mem_sets]
  constructor
  · simpa [Filter.le_def, rcomap, SetRel.mem_image]
      using fun h s t tl₂ => mem_of_superset (h t tl₂)
  · simpa [Filter.le_def, rcomap, SetRel.mem_image]
      using fun h t tl₂ => h _ t tl₂ Set.Subset.rfl

-- Interestingly, there does not seem to be a way to express this relation using a forward map.
-- Given a filter `f` on `α`, we want a filter `f'` on `β` such that `r.preimage s ∈ f` if
-- and only if `s ∈ f'`. But the intersection of two sets satisfying the lhs may be empty.
/-- One way of taking the inverse map of a filter under a relation. Generalization of `Filter.comap`
to relations. -/
def rcomap' (r : SetRel α β) (f : Filter β) : Filter α where
  sets := SetRel.image {(s, t) : _ × _ | r.preimage s ⊆ t} f.sets
  univ_sets := ⟨Set.univ, univ_mem, Set.subset_univ _⟩
  sets_of_superset := fun ⟨a', ha', ma'a⟩ ab => ⟨a', ha', ma'a.trans ab⟩
  inter_sets := fun ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩ =>
    ⟨a' ∩ b', inter_mem ha₁ hb₁, r.preimage_inter_subset.trans (Set.inter_subset_inter ha₂ hb₂)⟩

@[simp]
theorem mem_rcomap' (r : SetRel α β) (l : Filter β) (s : Set α) :
    s ∈ l.rcomap' r ↔ ∃ t ∈ l, r.preimage t ⊆ s :=
  Iff.rfl

theorem rcomap'_sets (r : SetRel α β) (f : Filter β) :
    (rcomap' r f).sets = SetRel.image {(s, t) | r.preimage s ⊆ t} f.sets :=
  rfl

@[simp]
theorem rcomap'_rcomap' (r : SetRel α β) (s : SetRel β γ) (l : Filter γ) :
    rcomap' r (rcomap' s l) = rcomap' (r.comp s) l :=
  Filter.ext fun t => by
    simp only [mem_rcomap', SetRel.preimage_comp]
    constructor
    · rintro ⟨u, ⟨v, vsets, hv⟩, h⟩
      exact ⟨v, vsets, (SetRel.preimage_mono hv).trans h⟩
    rintro ⟨t, tsets, ht⟩
    exact ⟨s.preimage t, ⟨t, tsets, Set.Subset.rfl⟩, ht⟩

@[simp]
theorem rcomap'_compose (r : SetRel α β) (s : SetRel β γ) :
    rcomap' r ∘ rcomap' s = rcomap' (r.comp s) :=
  funext <| rcomap'_rcomap' _ _

/-- Generic "limit of a relation" predicate. `RTendsto' r l₁ l₂` asserts that for every
`l₂`-neighborhood `a`, the `r`-preimage of `a` is an `l₁`-neighborhood. One generalization of
`Filter.Tendsto` to relations. -/
def RTendsto' (r : SetRel α β) (l₁ : Filter α) (l₂ : Filter β) :=
  l₁ ≤ l₂.rcomap' r

theorem rtendsto'_def (r : SetRel α β) (l₁ : Filter α) (l₂ : Filter β) :
    RTendsto' r l₁ l₂ ↔ ∀ s ∈ l₂, r.preimage s ∈ l₁ := by
  unfold RTendsto' rcomap'; constructor
  · simpa [le_def, SetRel.mem_image] using fun h s hs => h _ _ hs Set.Subset.rfl
  · simpa [le_def, SetRel.mem_image] using fun h s t ht => mem_of_superset (h t ht)

theorem tendsto_iff_rtendsto (l₁ : Filter α) (l₂ : Filter β) (f : α → β) :
    Tendsto f l₁ l₂ ↔ RTendsto (Function.graph f) l₁ l₂ := by
  simp [tendsto_def, Function.graph, rtendsto_def, SetRel.core, Set.preimage]

theorem tendsto_iff_rtendsto' (l₁ : Filter α) (l₂ : Filter β) (f : α → β) :
    Tendsto f l₁ l₂ ↔ RTendsto' (Function.graph f) l₁ l₂ := by
  simp [tendsto_def, Function.graph, rtendsto'_def, SetRel.preimage, Set.preimage]

/-! ### Partial functions -/


/-- The forward map of a filter under a partial function. Generalization of `Filter.map` to partial
functions. -/
def pmap (f : α →. β) (l : Filter α) : Filter β :=
  Filter.rmap f.graph' l

@[simp]
theorem mem_pmap (f : α →. β) (l : Filter α) (s : Set β) : s ∈ l.pmap f ↔ f.core s ∈ l :=
  Iff.rfl

/-- Generic "limit of a partial function" predicate. `PTendsto r l₁ l₂` asserts that for every
`l₂`-neighborhood `a`, the `p`-core of `a` is an `l₁`-neighborhood. One generalization of
`Filter.Tendsto` to partial function. -/
def PTendsto (f : α →. β) (l₁ : Filter α) (l₂ : Filter β) :=
  l₁.pmap f ≤ l₂

theorem ptendsto_def (f : α →. β) (l₁ : Filter α) (l₂ : Filter β) :
    PTendsto f l₁ l₂ ↔ ∀ s ∈ l₂, f.core s ∈ l₁ :=
  Iff.rfl

theorem ptendsto_iff_rtendsto (l₁ : Filter α) (l₂ : Filter β) (f : α →. β) :
    PTendsto f l₁ l₂ ↔ RTendsto f.graph' l₁ l₂ :=
  Iff.rfl

theorem pmap_res (l : Filter α) (s : Set α) (f : α → β) :
    pmap (PFun.res f s) l = map f (l ⊓ 𝓟 s) := by
  ext t
  simp only [PFun.core_res, mem_pmap, mem_map, mem_inf_principal, imp_iff_not_or]
  rfl

theorem tendsto_iff_ptendsto (l₁ : Filter α) (l₂ : Filter β) (s : Set α) (f : α → β) :
    Tendsto f (l₁ ⊓ 𝓟 s) l₂ ↔ PTendsto (PFun.res f s) l₁ l₂ := by
  simp only [Tendsto, PTendsto, pmap_res]

theorem tendsto_iff_ptendsto_univ (l₁ : Filter α) (l₂ : Filter β) (f : α → β) :
    Tendsto f l₁ l₂ ↔ PTendsto (PFun.res f Set.univ) l₁ l₂ := by
  rw [← tendsto_iff_ptendsto]
  simp [principal_univ]

/-- Inverse map of a filter under a partial function. One generalization of `Filter.comap` to
partial functions. -/
def pcomap' (f : α →. β) (l : Filter β) : Filter α :=
  Filter.rcomap' f.graph' l

/-- Generic "limit of a partial function" predicate. `PTendsto' r l₁ l₂` asserts that for every
`l₂`-neighborhood `a`, the `p`-preimage of `a` is an `l₁`-neighborhood. One generalization of
`Filter.Tendsto` to partial functions. -/
def PTendsto' (f : α →. β) (l₁ : Filter α) (l₂ : Filter β) :=
  l₁ ≤ l₂.rcomap' f.graph'

theorem ptendsto'_def (f : α →. β) (l₁ : Filter α) (l₂ : Filter β) :
    PTendsto' f l₁ l₂ ↔ ∀ s ∈ l₂, f.preimage s ∈ l₁ :=
  rtendsto'_def _ _ _

theorem ptendsto_of_ptendsto' {f : α →. β} {l₁ : Filter α} {l₂ : Filter β} :
    PTendsto' f l₁ l₂ → PTendsto f l₁ l₂ := by
  rw [ptendsto_def, ptendsto'_def]
  exact fun h s sl₂ => mem_of_superset (h s sl₂) (PFun.preimage_subset_core _ _)

theorem ptendsto'_of_ptendsto {f : α →. β} {l₁ : Filter α} {l₂ : Filter β} (h : f.Dom ∈ l₁) :
    PTendsto f l₁ l₂ → PTendsto' f l₁ l₂ := by
  rw [ptendsto_def, ptendsto'_def]
  intro h' s sl₂
  rw [PFun.preimage_eq]
  exact inter_mem (h' s sl₂) h

end Filter
