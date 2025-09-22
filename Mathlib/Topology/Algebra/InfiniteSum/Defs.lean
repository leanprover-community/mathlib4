/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Order.Filter.AtTopBot.BigOperators
import Mathlib.Topology.Separation.Hausdorff

/-!
# Infinite sum and product over a topological monoid

This file defines unconditionally convergent sums over a commutative topological additive monoid.
For Euclidean spaces (finite-dimensional Banach spaces) this is equivalent to absolute
convergence.

We also define unconditionally convergent products over a commutative topological multiplicative
monoid.

Note: There are summable sequences which are not unconditionally convergent! The other way holds
generally, see `HasSum.tendsto_sum_nat`.

## Implementation notes

We say that a function `f : β → α` has an unconditional product of `a` if the function
`fun s : Finset β ↦ ∏ b ∈ s, f b` converges to `a` on the `atTop` filter on `Finset β`. In other
words, for every neighborhood `U` of `a`, there exists a finite set `s : Finset β` of indices such
that `∏ b ∈ s', f b ∈ U` for any finite set `s'` which is a superset of `s`.

This may yield some unexpected results. For example, according to this definition, the product
`∏' n : ℕ, (1 : ℝ) / 2` unconditionally exists and is equal to `0`. More strikingly,
the product `∏' n : ℕ, (n : ℝ)` unconditionally exists and is equal to `0`, because one
of its terms is `0` (even though the product of the remaining terms diverges). Users who would
prefer that these products be considered not to exist can carry them out in the unit group `ℝˣ`
rather than in `ℝ`.

## References

* Bourbaki: General Topology (1995), Chapter 3 §5 (Infinite sums in commutative groups)

-/

/- **NOTE**. This file is intended to be kept short, just enough to state the basic definitions and
six key lemmas relating them together, namely `Summable.hasSum`, `Multipliable.hasProd`,
`HasSum.tsum_eq`, `HasProd.tprod_eq`, `Summable.hasSum_iff`, and `Multipliable.hasProd_iff`.

Do not add further lemmas here -- add them to `InfiniteSum.Basic` or (preferably) another, more
specific file. -/

noncomputable section

open Filter Function

open scoped Topology

variable {α β γ : Type*}

section HasProd

variable [CommMonoid α] [TopologicalSpace α]

/-- `HasProdFilter L f a` means that the (potentially infinite) product of the `f b` for `b : β`
converges to `a` along the filter `L` on `Finset β`. If this filter is `atTop`, this means that the
product is absolutely convergent and we call it `HasProd f a` instead.
-/
@[to_additive]
def HasProdFilter (L : Filter (Finset β)) (f : β → α) (a : α) : Prop :=
  Tendsto (fun s : Finset β ↦ ∏ b ∈ s, f b) L (𝓝 a)

/-- `MultipliableAlongFilter L f` means that `f` has some (infinite) product along the filter `L`.
-/
@[to_additive
/-- `SummableAlongFilter L f` means that `f` has some (infinite) sum along the filter `L`. -/]
def MultipliableFilter (L : Filter (Finset β)) (f : β → α) : Prop :=
  ∃ a, HasProdFilter L f a

/-- `HasProd f a` means that the (potentially infinite) product of the `f b` for `b : β` converges
to `a`.

The `atTop` filter on `Finset β` is the limit of all finite sets towards the entire type. So we take
the product over bigger and bigger sets. This product operation is invariant under reordering.

For the definition and many statements, `α` does not need to be a topological monoid. We only add
this assumption later, for the lemmas where it is relevant.

These are defined in an identical way to infinite sums (`HasSum`). For example, we say that
the function `ℕ → ℝ` sending `n` to `1 / 2` has a product of `0`, rather than saying that it does
not converge as some authors would. -/
@[to_additive /-- `HasSum f a` means that the (potentially infinite) sum of the `f b` for `b : β`
converges to `a`.

The `atTop` filter on `Finset β` is the limit of all finite sets towards the entire type. So we sum
up bigger and bigger sets. This sum operation is invariant under reordering. In particular,
the function `ℕ → ℝ` sending `n` to `(-1)^n / (n+1)` does not have a
sum for this definition, but a series which is absolutely convergent will have the correct sum.

This is based on Mario Carneiro's
[infinite sum `df-tsms` in Metamath](http://us.metamath.org/mpeuni/df-tsms.html).

For the definition and many statements, `α` does not need to be a topological monoid. We only add
this assumption later, for the lemmas where it is relevant. -/]
abbrev HasProd (f : β → α) (a : α) : Prop := HasProdFilter atTop f a

/-- `Multipliable f` means that `f` has some (infinite) product. Use `tprod` to get the value. -/
@[to_additive
/-- `Summable f` means that `f` has some (infinite) sum. Use `tsum` to get the value. -/]
abbrev Multipliable (f : β → α) : Prop := MultipliableFilter atTop f

@[to_additive]
lemma hasProd_iff_hasProdFilter {f : β → α} {a : α} :
    HasProd f a ↔ HasProdFilter atTop f a :=
  Iff.rfl

@[to_additive]
lemma multipliable_iff_multipliableFilter {f : β → α} :
    Multipliable f ↔ MultipliableFilter atTop f :=
  Iff.rfl

open scoped Classical in
/-- `∏'[L] i, f i` is the product of `f` if along the filter `L` if it exists or 1 otherwise. -/
@[to_additive /-- `∑'[L] i, f i` is the sum of `f` if along the filter `L` if it exists
 or 0 otherwise. -/]
noncomputable irreducible_def tprodFilter {β} (L : Filter (Finset β)) (f : β → α) :=
  if h : MultipliableFilter L f then
    if (mulSupport f).Finite ∧ L ≤ atTop then finprod f
    else h.choose
  else 1

open scoped Classical in
/-- `∏' i, f i` is the product of `f` if it exists and is unconditionally convergent,
or 1 otherwise. This is defined as `∏'[] i, f i` -/
@[to_additive /-- `∑' i, f i` is the sum of `f` if it exists and is unconditionally convergent,
or 0 otherwise. This is defined as `∑'[atTop] i, f i`. -/]
abbrev tprod {β} (f : β → α) := tprodFilter atTop f

@[inherit_doc tprod]
notation3 "∏' " "[" L "]" (...)", "r:67:(scoped f => tprodFilter L f) => r
@[inherit_doc tsumFilter]
notation3 "∑' " "[" L "]" (...)", "r:67:(scoped f => tsumFilter L f) => r

-- see Note [operator precedence of big operators]
@[inherit_doc tprod]
notation3 "∏' "(...)", "r:67:(scoped f => tprod f) => r
@[inherit_doc tsum]
notation3 "∑' "(...)", "r:67:(scoped f => tsum f) => r

@[to_additive]
lemma tprod_iff_tprodFilter {f : β → α} :
  ∏' b, f b = ∏' [atTop] b, f b := rfl

variable {L : Filter (Finset β)} {f : β → α} {a : α} {s : Finset β}

@[to_additive]
theorem HasProdFilter.multipliableFilter (h : HasProdFilter L f a) : MultipliableFilter L f :=
  ⟨a, h⟩

@[to_additive]
theorem HasProd.multipliable (h : HasProd f a) : Multipliable f :=
  HasProdFilter.multipliableFilter h

@[to_additive]
theorem tprodFilter_eq_one_of_not_multipliableFilter (h : ¬MultipliableFilter L f) :
    ∏'[L] b, f b = 1 := by
  simp [tprodFilter_def, h]

alias tprod_eq_one_of_not_multipliable := tprodFilter_eq_one_of_not_multipliableFilter
alias tsum_eq_zero_of_not_summable := tsumFilter_eq_zero_of_not_summableFilter

@[to_additive]
theorem Function.Injective.hasProd_iff {g : γ → β} (hg : Injective g)
    (hf : ∀ x, x ∉ Set.range g → f x = 1) : HasProd (f ∘ g) a ↔ HasProd f a := by
  simp only [HasProd, HasProdFilter, Tendsto, comp_apply, hg.map_atTop_finset_prod_eq hf]

@[to_additive]
theorem hasProd_subtype_iff_of_mulSupport_subset {s : Set β} (hf : mulSupport f ⊆ s) :
    HasProd (f ∘ (↑) : s → α) a ↔ HasProd f a :=
  Subtype.coe_injective.hasProd_iff <| by simpa using mulSupport_subset_iff'.1 hf

@[to_additive]
theorem hasProd_fintype [Fintype β] (f : β → α) : HasProd f (∏ b, f b) :=
  OrderTop.tendsto_atTop_nhds _

@[to_additive]
protected theorem Finset.hasProd (s : Finset β) (f : β → α) :
    HasProd (f ∘ (↑) : (↑s : Set β) → α) (∏ b ∈ s, f b) := by
  rw [← prod_attach]
  exact hasProd_fintype _

/-- If a function `f` is `1` outside of a finite set `s`, then it `HasProd` `∏ b ∈ s, f b`. -/
@[to_additive /-- If a function `f` vanishes outside of a finite set `s`, then it `HasSum`
`∑ b ∈ s, f b`. -/]
theorem hasProd_prod_of_ne_finset_one (hf : ∀ b ∉ s, f b = 1) :
    HasProd f (∏ b ∈ s, f b) :=
  (hasProd_subtype_iff_of_mulSupport_subset <| mulSupport_subset_iff'.2 hf).1 <| s.hasProd f

@[to_additive]
theorem multipliable_of_ne_finset_one (hf : ∀ b ∉ s, f b = 1) : Multipliable f :=
  (hasProd_prod_of_ne_finset_one hf).multipliableFilter

@[to_additive]
theorem MultipliableFilter.hasProdFilter {L : Filter (Finset β)} (ha : MultipliableFilter L f) :
    HasProdFilter L f (∏'[L] b, f b) := by
  simp only [tprodFilter_def, ha, dite_true]
  by_cases h : (mulSupport f).Finite ∧ L ≤ atTop
  · simp [h, HasProdFilter]
    simp only [h, finprod_eq_prod]
    have HH := hasProd_prod_of_ne_finset_one (f := f) (s := h.1.toFinset)
    simp only [Set.Finite.mem_toFinset, mem_mulSupport, ne_eq, not_not, imp_self, implies_true,
      HasProd, forall_const] at HH
    exact fun ⦃U⦄ a ↦ h.2 (HH a)
  simp [h]
  apply ha.choose_spec

@[to_additive]
theorem Multipliable.hasProd (h : Multipliable f) : HasProd f (∏' b, f b) :=
  MultipliableFilter.hasProdFilter h

@[to_additive]
theorem HasProdFilter.unique {a₁ a₂ : α} [T2Space α] [L.NeBot] :
    HasProdFilter L f a₁ → HasProdFilter L f a₂ → a₁ = a₂ := by
  classical exact tendsto_nhds_unique

variable [T2Space α]

@[to_additive]
theorem HasProdFilter.tprodFilter_eq (ha : HasProdFilter L f a) [L.NeBot] : ∏'[L] b, f b = a :=
  (MultipliableFilter.hasProdFilter ha.multipliableFilter).unique ha

alias HasProdFilter.tprod_eq := HasProdFilter.tprodFilter_eq
alias HasSumFilter.tsum_eq := HasSumFilter.tsumFilter_eq

@[to_additive]
theorem MultipliableFilter.hasProdFilter_iff (h : MultipliableFilter L f) [L.NeBot] :
    HasProdFilter L f a ↔ ∏'[L] b, f b = a := by
  apply Iff.intro
  · exact fun h ↦ HasProdFilter.tprodFilter_eq h
  · exact fun H ↦ H ▸ hasProdFilter h

omit [T2Space α] in
@[to_additive]
lemma HasProdFilter_bot {f : β → α} {a : α} : HasProdFilter ⊥ f a := by
  simp [HasProdFilter, Tendsto]

omit [T2Space α] in
@[to_additive]
lemma MultipliableFilter_bot (f : β → α) : MultipliableFilter ⊥ f :=
  ⟨1, HasProdFilter_bot⟩

end HasProd
