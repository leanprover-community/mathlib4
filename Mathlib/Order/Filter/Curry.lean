/-
Copyright (c) 2022 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
module

public import Mathlib.Order.Filter.Prod

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

In the "generalized set" intuition, a product filter and `Filter.curry` correspond to two ways
of describing the product of two sets:

* `f ×ˢ g = comap fst f ⊓ comap snd g` corresponds to `s ×ˢ t = fst ⁻¹' s ∩ snd ⁻¹' t`
* `f.curry g = bind f (fun x ↦ map (x, ·) g)` corresponds to `s ×ˢ t = ⋃ x ∈ s, (x, ·) '' t`

## Main definitions

* `Filter.curry`: A binary operation on filters which represents iterated limits

## Main statements

* `Filter.eventually_curry_iff`: An alternative definition of a curried filter
* `Filter.curry_le_prod`: Something that is eventually true on the a product filter is eventually
  true on the curried filter

## Tags

uniform convergence, curried filters, product filters
-/
set_option backward.defeqAttrib.useBackward true

public section


namespace Filter

variable {α β γ : Type*} {l : Filter α} {m : Filter β} {s : Set α} {t : Set β}

theorem eventually_curry_iff {p : α × β → Prop} :
    (∀ᶠ x : α × β in l.curry m, p x) ↔ ∀ᶠ x : α in l, ∀ᶠ y : β in m, p (x, y) :=
  Iff.rfl

theorem frequently_curry_iff
    (p : (α × β) → Prop) : (∃ᶠ x in l.curry m, p x) ↔ ∃ᶠ x in l, ∃ᶠ y in m, p (x, y) := by
  simp_rw [Filter.Frequently, not_iff_not, not_not, eventually_curry_iff]

theorem mem_curry_iff {s : Set (α × β)} :
    s ∈ l.curry m ↔ ∀ᶠ x : α in l, ∀ᶠ y : β in m, (x, y) ∈ s := Iff.rfl

theorem curry_le_prod : l.curry m ≤ l ×ˢ m := fun _ => Eventually.curry

theorem Tendsto.curry {f : α → β → γ} {la : Filter α} {lb : Filter β} {lc : Filter γ}
    (h : ∀ᶠ a in la, Tendsto (fun b : β => f a b) lb lc) : Tendsto ↿f (la.curry lb) lc :=
  fun _s hs => h.mono fun _a ha => ha hs

theorem frequently_curry_prod_iff :
    (∃ᶠ x in l.curry m, x ∈ s ×ˢ t) ↔ (∃ᶠ x in l, x ∈ s) ∧ ∃ᶠ y in m, y ∈ t := by
  simp [frequently_curry_iff]

theorem eventually_curry_prod_iff [NeBot l] [NeBot m] :
    (∀ᶠ x in l.curry m, x ∈ s ×ˢ t) ↔ s ∈ l ∧ t ∈ m := by
  simp [eventually_curry_iff]

theorem prod_mem_curry (hs : s ∈ l) (ht : t ∈ m) : s ×ˢ t ∈ l.curry m :=
  curry_le_prod <| prod_mem_prod hs ht

end Filter
