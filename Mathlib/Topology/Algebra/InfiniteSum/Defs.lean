/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Topology.Separation
import Mathlib.Algebra.BigOperators.Finprod

#align_import topology.algebra.infinite_sum.basic from "leanprover-community/mathlib"@"3b52265189f3fb43aa631edffce5d060fafaf82f"

/-!
# Infinite sum over a topological monoid

This sum is known as unconditionally convergent, as it sums to the same value under all possible
permutations. For Euclidean spaces (finite dimensional Banach spaces) this is equivalent to absolute
convergence.

Note: There are summable sequences which are not unconditionally convergent! The other way holds
generally, see `HasSum.tendsto_sum_nat`.

## References

* Bourbaki: General Topology (1995), Chapter 3 §5 (Infinite sums in commutative groups)

-/

/- **NOTE**. This file is intended to be kept short, just enough to state the basic definitions and
three key lemmas relating them together, namely `Summable.hasSum`, `HasSum.tsum_eq`, and
`Summable.hasSum_iff`.

Do not add further lemmas here -- add them to `InfiniteSum.Basic` or (preferably) another, more
specific file. -/

noncomputable section

open Filter Function

open scoped BigOperators Topology

variable {α β γ : Type*}

section HasSum

variable [AddCommMonoid α] [TopologicalSpace α]

/-- Infinite sum on a topological monoid

The `atTop` filter on `Finset β` is the limit of all finite sets towards the entire type. So we sum
up bigger and bigger sets. This sum operation is invariant under reordering. In particular,
the function `ℕ → ℝ` sending `n` to `(-1)^n / (n+1)` does not have a
sum for this definition, but a series which is absolutely convergent will have the correct sum.

This is based on Mario Carneiro's
[infinite sum `df-tsms` in Metamath](http://us.metamath.org/mpeuni/df-tsms.html).

For the definition or many statements, `α` does not need to be a topological monoid. We only add
this assumption later, for the lemmas where it is relevant.
-/
def HasSum (f : β → α) (a : α) : Prop :=
  Tendsto (fun s : Finset β ↦ ∑ b in s, f b) atTop (𝓝 a)
#align has_sum HasSum

/-- `Summable f` means that `f` has some (infinite) sum. Use `tsum` to get the value. -/
def Summable (f : β → α) : Prop :=
  ∃ a, HasSum f a
#align summable Summable

open Classical in
/-- `∑' i, f i` is the sum of `f` it exists, or 0 otherwise. -/
irreducible_def tsum {β} (f : β → α) :=
  if h : Summable f then
  /- Note that the sum might not be uniquely defined if the topology is not separated.
  When the support of `f` is finite, we make the most reasonable choice to use the finite sum over
  the support. Otherwise, we choose arbitrarily an `a` satisfying `HasSum f a`. -/
    if (support f).Finite then finsum f
    else choose h
  else 0
#align tsum tsum

-- see Note [operator precedence of big operators]
@[inherit_doc tsum]
notation3 "∑' "(...)", "r:67:(scoped f => tsum f) => r

variable {f g : β → α} {a b : α} {s : Finset β}

theorem HasSum.summable (h : HasSum f a) : Summable f :=
  ⟨a, h⟩
#align has_sum.summable HasSum.summable

theorem tsum_eq_zero_of_not_summable (h : ¬Summable f) : ∑' b, f b = 0 := by simp [tsum_def, h]
#align tsum_eq_zero_of_not_summable tsum_eq_zero_of_not_summable

theorem Function.Injective.hasSum_iff {g : γ → β} (hg : Injective g)
    (hf : ∀ x, x ∉ Set.range g → f x = 0) : HasSum (f ∘ g) a ↔ HasSum f a := by
  simp only [HasSum, Tendsto, comp_apply, hg.map_atTop_finset_sum_eq hf]
#align function.injective.has_sum_iff Function.Injective.hasSum_iff

theorem hasSum_subtype_iff_of_support_subset {s : Set β} (hf : support f ⊆ s) :
    HasSum (f ∘ (↑) : s → α) a ↔ HasSum f a :=
  Subtype.coe_injective.hasSum_iff <| by simpa using support_subset_iff'.1 hf
#align has_sum_subtype_iff_of_support_subset hasSum_subtype_iff_of_support_subset

theorem hasSum_fintype [Fintype β] (f : β → α) : HasSum f (∑ b, f b) :=
  OrderTop.tendsto_atTop_nhds _
#align has_sum_fintype hasSum_fintype

protected theorem Finset.hasSum (s : Finset β) (f : β → α) :
    HasSum (f ∘ (↑) : (↑s : Set β) → α) (∑ b in s, f b) := by
  rw [← sum_attach]
  exact hasSum_fintype _
#align finset.has_sum Finset.hasSum

/-- If a function `f` vanishes outside of a finite set `s`, then it `HasSum` `∑ b in s, f b`. -/
theorem hasSum_sum_of_ne_finset_zero (hf : ∀ (b) (_ : b ∉ s), f b = 0) : HasSum f (∑ b in s, f b) :=
  (hasSum_subtype_iff_of_support_subset <| support_subset_iff'.2 hf).1 <| s.hasSum f
#align has_sum_sum_of_ne_finset_zero hasSum_sum_of_ne_finset_zero

theorem summable_of_ne_finset_zero (hf : ∀ (b) (_ : b ∉ s), f b = 0) : Summable f :=
  (hasSum_sum_of_ne_finset_zero hf).summable
#align summable_of_ne_finset_zero summable_of_ne_finset_zero

theorem Summable.hasSum (ha : Summable f) : HasSum f (∑' b, f b) := by
  simp only [tsum_def, ha, dite_true]
  by_cases H : (support f).Finite
  · simp [H, hasSum_sum_of_ne_finset_zero, finsum_eq_sum]
  · simpa [H] using Classical.choose_spec ha
#align summable.has_sum Summable.hasSum

theorem HasSum.unique {a₁ a₂ : α} [T2Space α] : HasSum f a₁ → HasSum f a₂ → a₁ = a₂ := by
  classical exact tendsto_nhds_unique
#align has_sum.unique HasSum.unique

variable [T2Space α]

theorem HasSum.tsum_eq (ha : HasSum f a) : ∑' b, f b = a :=
  (Summable.hasSum ⟨a, ha⟩).unique ha
#align has_sum.tsum_eq HasSum.tsum_eq

theorem Summable.hasSum_iff (h : Summable f) : HasSum f a ↔ ∑' b, f b = a :=
  Iff.intro HasSum.tsum_eq fun eq ↦ eq ▸ h.hasSum
#align summable.has_sum_iff Summable.hasSum_iff

end HasSum
