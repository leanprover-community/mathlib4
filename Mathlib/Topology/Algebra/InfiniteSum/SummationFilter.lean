/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Data.Finset.Preimage
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.LiminfLimsup


/-!
# Summation filters

We define a `SummationFilter` on `β` to be a filter on the finite subsets of `β`. These are used
in defining summability: if `L` is a summation filter, we define the `L`-sum of `f` to be the
limit along `L` of the sums over finsets (if this limit exists). This file only develops the basic
machinery of summation filters - the key definitions `HasSum`, `tsum` and `summable` (and their
product variants) are in the file `Mathlib.Topology.Algebra.InfiniteSum.Defs`.
-/

open Set Filter Function

variable {α β γ : Type*}

/-- A filter on the set of finite subsets of a type `β`. (Used for defining infinite topological
sums and products, as limits along the given filter of partial sums / products over finsets.) -/
structure SummationFilter (β) where
  /-- The filter -/
  filter : Filter (Finset β)

namespace SummationFilter

/-- Typeclass asserting that a summation filter `L` is consistent with unconditional summation,
so that any unconditionally-summable function is `L`-summable with the same sum. -/
class LeAtTop (L : SummationFilter β) : Prop where
  le_atTop : L.filter ≤ atTop

export LeAtTop (le_atTop)

/-- Typeclass asserting that a summation filter is non-vacuous (if this is not satisfied, then
every function is summable with every possible sum simultaneously). -/
class NeBot (L : SummationFilter β) : Prop where
  ne_bot : L.filter.NeBot

/-- Makes the `NeBot` instance visible to the typeclass machinery. -/
instance (L : SummationFilter β) [L.NeBot] : L.filter.NeBot := NeBot.ne_bot

lemma neBot_or_eq_bot (L : SummationFilter β) : L.NeBot ∨ L.filter = ⊥ := by
  by_cases h : L.filter = ⊥
  · exact .inr h
  · exact .inl ⟨⟨h⟩⟩

section support

/-- The support of a summation filter (its `lim inf`, considered as a filter of sets). -/
def support (L : SummationFilter β) : Set β := {b | ∀ᶠ s in L.filter, b ∈ s}

lemma support_eq_limsInf (L : SummationFilter β) :
    support L = limsInf (L.filter.map (↑)) := by
  refine eq_of_forall_ge_iff fun c ↦ ?_
  simpa [support, limsInf, setOf_subset] using
    ⟨fun hL b hb x hx ↦ hL x <| hb.mp <| .of_forall fun c hc ↦ hc hx,
      fun hL x hx ↦ singleton_subset_iff.mp <| hL _ <| by simpa using hx⟩

lemma support_eq_univ_iff {L : SummationFilter β} :
    L.support = univ ↔ L.filter ≤ atTop := by
  simp only [support, Set.eq_univ_iff_forall, Set.mem_setOf]
  refine ⟨fun h s hs ↦ ?_, fun h b ↦ .filter_mono h ?_⟩
  · obtain ⟨t, ht⟩ := mem_atTop_sets.mp hs
    have := (Filter.biInter_finset_mem t).mpr fun b hb ↦ h b
    exact Filter.mem_of_superset this fun r hr ↦ ht r (by simpa using hr)
  · filter_upwards [eventually_ge_atTop {b}] using by simp

@[simp] lemma support_eq_univ (L : SummationFilter β) [L.LeAtTop] : L.support = univ :=
  support_eq_univ_iff.mpr L.le_atTop

instance [IsEmpty β] (L : SummationFilter β) : L.LeAtTop :=
  ⟨support_eq_univ_iff.mp <| Subsingleton.elim ..⟩

lemma leAtTop_of_not_NeBot (L : SummationFilter β) (hL : ¬L.NeBot) : L.LeAtTop := by
  have hLs : L.support = Set.univ := by
    simp [SummationFilter.support, L.neBot_or_eq_bot.resolve_left hL]
  exact ⟨L.support_eq_univ_iff.mp hLs⟩

/-- Decidability instance: useful when working with `Finset` sums / products. -/
instance (L : SummationFilter β) [L.LeAtTop] : DecidablePred (· ∈ L.support) :=
  fun b ↦ isTrue (by simp)

end support

section has_support

/-- Typeclass asserting that the sets in `L.filter` are eventually contained in `L.support`. This
is a sufficient condition for `L`-summation to behave well on finitely-supported functions: every
finitely-supported `f` is `L`-summable with the sum `∑ᶠ x ∈ L.support, f x` (and similarly for
products). -/
class HasSupport (L : SummationFilter β) : Prop where
  eventually_le_support : ∀ᶠ s in L.filter, ↑s ⊆ L.support

export HasSupport (eventually_le_support)

instance (L : SummationFilter β) [L.LeAtTop] : HasSupport L := ⟨by simp⟩

lemma eventually_mem_or_not_mem (L : SummationFilter β) [HasSupport L] (b : β) :
    (∀ᶠ s in L.filter, b ∈ s) ∨ (∀ᶠ s in L.filter, b ∉ s) := by
  rw [or_iff_not_imp_left]
  intro hb
  filter_upwards [L.eventually_le_support] with a ha using notMem_subset ha hb

end has_support

section map_comap

/-- Pushforward of a summation filter along an embedding.

(We define this only for embeddings, rather than arbitrary maps, since this is the only case needed
for the intended applications, and this avoids requiring a `DecidableEq` instance on `γ`.) -/
@[simps] def map (L : SummationFilter β) (f : β ↪ γ) : SummationFilter γ where
  filter := L.filter.map (Finset.map f)

@[simp] lemma support_map (L : SummationFilter β) [L.NeBot] (f : β ↪ γ) :
    (L.map f).support = f '' L.support := by
  ext c
  rcases em (c ∈ range f) with ⟨b, rfl⟩ | hc
  · simp [support]
  · exact ⟨fun hc' ↦ have := hc'.exists; by grind, by grind⟩

/-- If `L` has well-defined support, then so does its map along an embedding. -/
instance (L : SummationFilter β) [HasSupport L] (f : β ↪ γ) : HasSupport (L.map f) := by
  constructor
  by_cases h : L.NeBot
  · simp only [map_filter, eventually_map, Finset.coe_map, image_subset_iff, support_map]
    filter_upwards [L.eventually_le_support] with a using by grind
  · have : L.filter = ⊥ := by contrapose! h; exact ⟨⟨h⟩⟩
    simp [this]

/-- Pullback of a summation filter along an embedding. -/
@[simps] def comap (L : SummationFilter β) (f : γ ↪ β) : SummationFilter γ where
  filter := L.filter.map (fun s ↦ s.preimage f f.injective.injOn)

@[simp] lemma support_comap (L : SummationFilter β) (f : γ ↪ β) :
    (L.comap f).support = f ⁻¹' L.support := by
  simp [support]

/-- If `L` has well-defined support, then so does its comap along an embedding. -/
instance (L : SummationFilter β) [HasSupport L] (f : γ ↪ β) : HasSupport (L.comap f) := by
  constructor
  simp only [support_comap, comap_filter, eventually_map, Finset.coe_preimage]
  filter_upwards [L.eventually_le_support] with a using Set.preimage_mono

instance (L : SummationFilter β) [LeAtTop L] (f : γ ↪ β) : LeAtTop (L.comap f) :=
  ⟨by rw [← support_eq_univ_iff]; simp⟩

end map_comap

section examples
/-!
## Examples of summation filters
-/
variable (β)

/-- **Unconditional summation**: a function on `β` is said to be *unconditionally summable* if its
partial sums over finite subsets converge with respect to the `atTop` filter. -/
@[simps] def unconditional : SummationFilter β where
  filter := atTop

instance : (unconditional β).LeAtTop := ⟨le_rfl⟩

instance : (unconditional β).NeBot := ⟨atTop_neBot⟩

/-- This instance is useful for some measure-theoretic statements. -/
instance [Countable β] : IsCountablyGenerated (unconditional β).filter :=
  atTop.isCountablyGenerated

/-- The unconditional filter is preserved by comaps. -/
@[simp] lemma comap_unconditional {β} (f : γ ↪ β) :
    (unconditional β).comap f = unconditional γ := by
  classical
  simp only [unconditional, comap]
  congr 1 with s
  simp only [mem_map, mem_atTop_sets, ge_iff_le, Finset.le_eq_subset, mem_preimage]
  constructor <;> rintro ⟨t, ht⟩
  · refine ⟨t.preimage f (by simp), fun x hx ↦ ?_⟩
    simpa [Finset.union_eq_right.mpr hx] using ht (t ∪ x.map f) t.subset_union_left
  · exact ⟨_, fun b hb ↦ ht _ (Finset.map_subset_iff_subset_preimage.mp hb)⟩

/-- If `β` is finite, then `unconditional β` is the only summation filter `L` on `β` satisfying
`L.LeAtTop` and `L.NeBot`. -/
lemma eq_unconditional_of_finite {β} [Finite β]
    (L : SummationFilter β) [L.LeAtTop] [L.NeBot] : L = unconditional β := by
  classical
  haveI := Fintype.ofFinite β
  have hAtTop : (atTop : Filter (Finset β)) = pure Finset.univ := by
    rw [(isTop_iff_eq_top.mpr rfl).atTop_eq (a := Finset.univ), ← Finset.top_eq_univ,
      Ici_top, principal_singleton]
  have hL := L.le_atTop
  have hL' : ∅ ∉ L.filter := empty_mem_iff_bot.not.mpr <| NeBot.ne_bot.ne'
  cases L with | mk F =>
  simp only [unconditional, hAtTop] at *
  congr 1
  refine eq_of_le_of_ge hL (pure_le_iff.mpr ?_)
  contrapose! hL'
  obtain ⟨s, hs, hs'⟩ := hL'
  simpa [inter_singleton_eq_empty.mpr hs'] using inter_mem hs (le_pure_iff.mp hL)

section conditionalTop

variable [Preorder β] [LocallyFiniteOrder β]

/-- **Conditional summation**, for ordered types `β` such that closed intervals `[x, y]` are
finite: this corresponds to limits of finite sums over larger and larger intervals. -/
@[simps] def conditional : SummationFilter β where
  filter := (atBot ×ˢ atTop).map (fun p ↦ Finset.Icc p.1 p.2)

instance : (conditional β).LeAtTop := ⟨support_eq_univ_iff.mp <| by
  simpa [eq_univ_iff_forall, support, -eventually_and]
    using fun x ↦ prod_mem_prod (eventually_le_atBot x) (eventually_ge_atTop x)⟩

instance [Nonempty β] [IsDirected β (· ≤ ·)] [IsDirected β (· ≥ ·)] : (conditional β).NeBot :=
  ⟨by simp; infer_instance⟩

instance [IsCountablyGenerated (atTop : Filter β)] [IsCountablyGenerated (atBot : Filter β)] :
    IsCountablyGenerated (conditional β).filter :=
  map.isCountablyGenerated ..

/-- When `β` has a bottom element, `conditional β` is given by limits over finite intervals
`{y | y ≤ x}` as `x → atTop`. -/
@[simp high] -- want this to be prioritized over `conditional_filter` when they both apply
lemma conditional_filter_eq_map_Iic {γ} [PartialOrder γ] [LocallyFiniteOrder γ] [OrderBot γ] :
    (conditional γ).filter = atTop.map Finset.Iic := by
  simp [(isBot_bot).atBot_eq, comp_def, Finset.Icc_bot]

/-- When `β` has a top element, `conditional β` is given by limits over finite intervals
`{y | x ≤ y}` as `x → atBot`. -/
@[simp high] -- want this to be prioritized over `conditional_filter` when they both apply
lemma conditional_filter_eq_map_Ici {γ} [PartialOrder γ] [LocallyFiniteOrder γ] [OrderTop γ] :
    (conditional γ).filter = atBot.map Finset.Ici := by
  simp [(isTop_top).atTop_eq, comp_def, Finset.Icc_top]

/-- Conditional summation over `ℕ` is given by limits of sums over `Finset.range n` as `n → ∞`. -/
@[simp high + 1] -- want this to be prioritized over `conditional_filter_eq_map_Ici`
lemma conditional_filter_eq_map_range : (conditional ℕ).filter = atTop.map Finset.range := by
  have (n : ℕ) : Finset.Iic n = Finset.range (n + 1) := by ext x; simp [Nat.lt_succ]
  simp only [conditional_filter_eq_map_Iic, funext this]
  apply le_antisymm <;>
      rw [← Tendsto] <;>
      simp only [tendsto_atTop', mem_map, mem_atTop_sets, mem_preimage] <;>
      rintro s ⟨a, ha⟩
  · exact ⟨a + 1, fun b hb ↦ ha (b + 1) (by omega)⟩
  · exact ⟨a + 1, fun b hb ↦ by convert ha (b - 1) (by omega); omega⟩

end conditionalTop

end examples

end SummationFilter
