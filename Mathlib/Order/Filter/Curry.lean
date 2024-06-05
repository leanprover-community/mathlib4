/-
Copyright (c) 2022 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
import Mathlib.Order.Filter.Prod

#align_import order.filter.curry from "leanprover-community/mathlib"@"d6fad0e5bf2d6f48da9175d25c3dc5706b3834ce"

/-!
# Curried Filters

This file provides an operation (`Filter.curry`) on filters which provides the equivalence
`∀ᶠ a in l, ∀ᶠ b in l', p (a, b) ↔ ∀ᶠ c in (l.curry l'), p c` (see `Filter.eventually_curry_iff`).

To understand when this operation might arise, it is helpful to think of `∀ᶠ` as a combination of
the quantifiers `∃ ∀`. For instance, `∀ᶠ n in atTop, p n ↔ ∃ N, ∀ n ≥ N, p n`. A curried filter
yields the quantifier order `∃ ∀ ∃ ∀`. For instance,
`∀ᶠ n in atTop.curry atTop, p n ↔ ∃ M, ∀ m ≥ M, ∃ N, ∀ n ≥ N, p (m, n)`.

This is different from a product filter, which instead yields a quantifier order `∃ ∃ ∀ ∀`. For
instance, `∀ᶠ n in atTop ×ˢ atTop, p n ↔ ∃ M, ∃ N, ∀ m ≥ M, ∀ n ≥ N, p (m, n)`. This makes it
clear that if something eventually occurs on the product filter, it eventually occurs on the curried
filter (see `Filter.curry_le_prod` and `Filter.Eventually.curry`), but the converse is not true.

Another way to think about the curried versus the product filter is that tending to some limit on
the product filter is a version of uniform convergence (see `tendsto_prod_filter_iff`) whereas
tending to some limit on a curried filter is just iterated limits (see `Filter.Tendsto.curry`).

In the "generalized set" intuition, `Filter.prod` and `Filter.curry` correspond to two ways of
describing the product of two sets, namely `s ×ˢ t = fst ⁻¹' s ∩ snd ⁻¹' t` and
`s ×ˢ t = ⋃ x ∈ s, (x, ·) '' t`.

## Main definitions

* `Filter.curry`: A binary operation on filters which represents iterated limits

## Main statements

* `Filter.eventually_curry_iff`: An alternative definition of a curried filter
* `Filter.curry_le_prod`: Something that is eventually true on the a product filter is eventually
   true on the curried filter

## Tags

uniform convergence, curried filters, product filters
-/


namespace Filter

variable {α β γ : Type*}

/-- This filter is characterized by `Filter.eventually_curry_iff`:
`(∀ᶠ (x : α × β) in f.curry g, p x) ↔ ∀ᶠ (x : α) in f, ∀ᶠ (y : β) in g, p (x, y)`. Useful
in adding quantifiers to the middle of `Tendsto`s. See
`hasFDerivAt_of_tendstoUniformlyOnFilter`. -/
def curry (f : Filter α) (g : Filter β) : Filter (α × β) :=
  bind f fun a ↦ map (a, ·) g
#align filter.curry Filter.curry

theorem eventually_curry_iff {f : Filter α} {g : Filter β} {p : α × β → Prop} :
    (∀ᶠ x : α × β in f.curry g, p x) ↔ ∀ᶠ x : α in f, ∀ᶠ y : β in g, p (x, y) :=
  Iff.rfl
#align filter.eventually_curry_iff Filter.eventually_curry_iff

theorem frequently_curry_iff {α β : Type*} {l : Filter α} {m : Filter β}
    (p : (α × β) → Prop) : (∃ᶠ x in l.curry m, p x) ↔ ∃ᶠ x in l, ∃ᶠ y in m, p (x, y) := by
  simp_rw [Filter.Frequently, not_iff_not, not_not, eventually_curry_iff]

theorem mem_curry_iff {f : Filter α} {g : Filter β} {s : Set (α × β)} :
    s ∈ f.curry g ↔ ∀ᶠ x : α in f, ∀ᶠ y : β in g, (x, y) ∈ s := Iff.rfl

theorem curry_le_prod {f : Filter α} {g : Filter β} : f.curry g ≤ f.prod g :=
  fun _ => Eventually.curry
#align filter.curry_le_prod Filter.curry_le_prod

theorem Tendsto.curry {f : α → β → γ} {la : Filter α} {lb : Filter β} {lc : Filter γ}
    (h : ∀ᶠ a in la, Tendsto (fun b : β => f a b) lb lc) : Tendsto (↿f) (la.curry lb) lc :=
  fun _s hs => h.mono fun _a ha => ha hs
#align filter.tendsto.curry Filter.Tendsto.curry

theorem frequently_curry_prod_iff {α β : Type*} {l : Filter α} {m : Filter β}
    (s : Set α) (t : Set β) : (∃ᶠ x in l.curry m, x ∈ s ×ˢ t) ↔ sᶜ ∉ l ∧ tᶜ ∉ m := by
  refine ⟨fun h => ?_, fun ⟨hs, ht⟩ => ?_⟩
  · exact frequently_prod_and.mp (Frequently.filter_mono h curry_le_prod)
  rw [frequently_curry_iff]
  exact Frequently.mono hs $ fun x hx => Frequently.mono ht (by simp[hx])

theorem prod_mem_curry {α β : Type*} {l : Filter α} {m : Filter β} {s : Set α} {t : Set β}
    (hs : s ∈ l) (ht : t ∈ m) : s ×ˢ t ∈ l.curry m :=
  curry_le_prod $ prod_mem_prod hs ht

theorem eventually_curry_prod_iff {α β : Type*} {l : Filter α} {m : Filter β}
    [NeBot l] [NeBot m] (s : Set α) (t : Set β) :
    (∀ᶠ x in l.curry m, x ∈ s ×ˢ t) ↔ s ∈ l ∧ t ∈ m := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨hs, ht⟩ => prod_mem_curry hs ht⟩ <;>
    rw [eventually_curry_iff] at h
  · apply mem_of_superset h
    simp
  rcases h.exists with ⟨_, hx⟩
  apply mem_of_superset hx
  exact fun _ hy => hy.2

end Filter
