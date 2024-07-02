/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Topology.Separation
import Mathlib.Algebra.BigOperators.Finprod

#align_import topology.algebra.infinite_sum.basic from "leanprover-community/mathlib"@"3b52265189f3fb43aa631edffce5d060fafaf82f"

/-!
# Infinite sum and product over a topological monoid

This file defines unconditionally convergent sums over a commutative topological additive monoid.
For Euclidean spaces (finite dimensional Banach spaces) this is equivalent to absolute
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

/-- Infinite product on a topological monoid

The `atTop` filter on `Finset β` is the limit of all finite sets towards the entire type. So we take
the product over bigger and bigger sets. This product operation is invariant under reordering.

For the definition and many statements, `α` does not need to be a topological monoid. We only add
this assumption later, for the lemmas where it is relevant.

These are defined in an identical way to infinite sums (`HasSum`). For example, we say that
the function `ℕ → ℝ` sending `n` to `1 / 2` has a product of `0`, rather than saying that it does
not converge as some authors would. -/
@[to_additive "Infinite sum on a topological monoid

The `atTop` filter on `Finset β` is the limit of all finite sets towards the entire type. So we sum
up bigger and bigger sets. This sum operation is invariant under reordering. In particular,
the function `ℕ → ℝ` sending `n` to `(-1)^n / (n+1)` does not have a
sum for this definition, but a series which is absolutely convergent will have the correct sum.

This is based on Mario Carneiro's
[infinite sum `df-tsms` in Metamath](http://us.metamath.org/mpeuni/df-tsms.html).

For the definition and many statements, `α` does not need to be a topological monoid. We only add
this assumption later, for the lemmas where it is relevant."]
def HasProd (f : β → α) (a : α) : Prop :=
  Tendsto (fun s : Finset β ↦ ∏ b ∈ s, f b) atTop (𝓝 a)
#align has_sum HasSum

/-- `Multipliable f` means that `f` has some (infinite) product. Use `tprod` to get the value. -/
@[to_additive "`Summable f` means that `f` has some (infinite) sum. Use `tsum` to get the value."]
def Multipliable (f : β → α) : Prop :=
  ∃ a, HasProd f a
#align summable Summable

open scoped Classical in
/-- `∏' i, f i` is the product of `f` it exists, or 1 otherwise. -/
@[to_additive "`∑' i, f i` is the sum of `f` it exists, or 0 otherwise."]
noncomputable irreducible_def tprod {β} (f : β → α) :=
  if h : Multipliable f then
  /- Note that the product might not be uniquely defined if the topology is not separated.
  When the multiplicative support of `f` is finite, we make the most reasonable choice to use the
  product over the multiplicative support. Otherwise, we choose arbitrarily an `a` satisfying
  `HasProd f a`. -/
    if (mulSupport f).Finite then finprod f
    else h.choose
  else 1
#align tsum tsum

-- see Note [operator precedence of big operators]
@[inherit_doc tprod]
notation3 "∏' "(...)", "r:67:(scoped f => tprod f) => r
@[inherit_doc tsum]
notation3 "∑' "(...)", "r:67:(scoped f => tsum f) => r

variable {f g : β → α} {a b : α} {s : Finset β}

@[to_additive]
theorem HasProd.multipliable (h : HasProd f a) : Multipliable f :=
  ⟨a, h⟩
#align has_sum.summable HasSum.summable

@[to_additive]
theorem tprod_eq_one_of_not_multipliable (h : ¬Multipliable f) : ∏' b, f b = 1 := by
  simp [tprod_def, h]
#align tsum_eq_zero_of_not_summable tsum_eq_zero_of_not_summable

@[to_additive]
theorem Function.Injective.hasProd_iff {g : γ → β} (hg : Injective g)
    (hf : ∀ x, x ∉ Set.range g → f x = 1) : HasProd (f ∘ g) a ↔ HasProd f a := by
  simp only [HasProd, Tendsto, comp_apply, hg.map_atTop_finset_prod_eq hf]
#align function.injective.has_sum_iff Function.Injective.hasSum_iff

@[to_additive]
theorem hasProd_subtype_iff_of_mulSupport_subset {s : Set β} (hf : mulSupport f ⊆ s) :
    HasProd (f ∘ (↑) : s → α) a ↔ HasProd f a :=
  Subtype.coe_injective.hasProd_iff <| by simpa using mulSupport_subset_iff'.1 hf
#align has_sum_subtype_iff_of_support_subset hasSum_subtype_iff_of_support_subset

@[to_additive]
theorem hasProd_fintype [Fintype β] (f : β → α) : HasProd f (∏ b, f b) :=
  OrderTop.tendsto_atTop_nhds _
#align has_sum_fintype hasSum_fintype

@[to_additive]
protected theorem Finset.hasProd (s : Finset β) (f : β → α) :
    HasProd (f ∘ (↑) : (↑s : Set β) → α) (∏ b ∈ s, f b) := by
  rw [← prod_attach]
  exact hasProd_fintype _
#align finset.has_sum Finset.hasSum

/-- If a function `f` is `1` outside of a finite set `s`, then it `HasProd` `∏ b ∈ s, f b`. -/
@[to_additive "If a function `f` vanishes outside of a finite set `s`, then it `HasSum`
`∑ b ∈ s, f b`."]
theorem hasProd_prod_of_ne_finset_one (hf : ∀ b ∉ s, f b = 1) :
    HasProd f (∏ b ∈ s, f b) :=
  (hasProd_subtype_iff_of_mulSupport_subset <| mulSupport_subset_iff'.2 hf).1 <| s.hasProd f
#align has_sum_sum_of_ne_finset_zero hasSum_sum_of_ne_finset_zero

@[to_additive]
theorem multipliable_of_ne_finset_one (hf : ∀ b ∉ s, f b = 1) : Multipliable f :=
  (hasProd_prod_of_ne_finset_one hf).multipliable
#align summable_of_ne_finset_zero summable_of_ne_finset_zero

@[to_additive]
theorem Multipliable.hasProd (ha : Multipliable f) : HasProd f (∏' b, f b) := by
  simp only [tprod_def, ha, dite_true]
  by_cases H : (mulSupport f).Finite
  · simp [H, hasProd_prod_of_ne_finset_one, finprod_eq_prod]
  · simpa [H] using ha.choose_spec
#align summable.has_sum Summable.hasSum

@[to_additive]
theorem HasProd.unique {a₁ a₂ : α} [T2Space α] : HasProd f a₁ → HasProd f a₂ → a₁ = a₂ := by
  classical exact tendsto_nhds_unique
#align has_sum.unique HasSum.unique

variable [T2Space α]

@[to_additive]
theorem HasProd.tprod_eq (ha : HasProd f a) : ∏' b, f b = a :=
  (Multipliable.hasProd ⟨a, ha⟩).unique ha
#align has_sum.tsum_eq HasSum.tsum_eq

@[to_additive]
theorem Multipliable.hasProd_iff (h : Multipliable f) : HasProd f a ↔ ∏' b, f b = a :=
  Iff.intro HasProd.tprod_eq fun eq ↦ eq ▸ h.hasProd
#align summable.has_sum_iff Summable.hasSum_iff

end HasProd
