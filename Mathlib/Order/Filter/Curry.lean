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
the quantifiers `∃ ∀`. For instance, `∀ᶠ n in at_top, p n ↔ ∃ N, ∀ n ≥ N, p n`. A curried filter
yields the quantifier order `∃ ∀ ∃ ∀`. For instance,
`∀ᶠ n in at_top.curry at_top, p n ↔ ∃ M, ∀ m ≥ M, ∃ N, ∀ n ≥ N, p (m, n)`.

This is different from a product filter, which instead yields a quantifier order `∃ ∃ ∀ ∀`. For
instance, `∀ᶠ n in at_top ×ˢ at_top, p n ↔ ∃ M, ∃ N, ∀ m ≥ M, ∀ n ≥ N, p (m, n)`. This makes it
clear that if something eventually occurs on the product filter, it eventually occurs on the curried
filter (see `Filter.curry_le_prod` and `Filter.eventually.curry`), but the converse is not true.

Another way to think about the curried versus the product filter is that tending to some limit on
the product filter is a version of uniform convergence (see `tendsto_prod_filter_iff`) whereas
tending to some limit on a curried filter is just iterated limits (see `Filter.Tendsto.curry`).

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
def curry (f : Filter α) (g : Filter β) : Filter (α × β) where
  sets := { s | ∀ᶠ a : α in f, ∀ᶠ b : β in g, (a, b) ∈ s }
  univ_sets := by simp only [Set.mem_setOf_eq, Set.mem_univ, eventually_true]
                  -- 🎉 no goals
  sets_of_superset := fun hx hxy =>
    hx.mono fun a ha => ha.mono fun b hb => Set.mem_of_subset_of_mem hxy hb
  inter_sets := fun hx hy =>
    (hx.and hy).mono fun a ha => (ha.1.and ha.2).mono fun b hb => hb
#align filter.curry Filter.curry

theorem eventually_curry_iff {f : Filter α} {g : Filter β} {p : α × β → Prop} :
    (∀ᶠ x : α × β in f.curry g, p x) ↔ ∀ᶠ x : α in f, ∀ᶠ y : β in g, p (x, y) :=
  Iff.rfl
#align filter.eventually_curry_iff Filter.eventually_curry_iff

theorem curry_le_prod {f : Filter α} {g : Filter β} : f.curry g ≤ f.prod g :=
  fun _ => Eventually.curry
#align filter.curry_le_prod Filter.curry_le_prod

theorem Tendsto.curry {f : α → β → γ} {la : Filter α} {lb : Filter β} {lc : Filter γ}
    (h : ∀ᶠ a in la, Tendsto (fun b : β => f a b) lb lc) : Tendsto (↿f) (la.curry lb) lc :=
  fun _s hs => h.mono fun _a ha => ha hs
#align filter.tendsto.curry Filter.Tendsto.curry

end Filter
