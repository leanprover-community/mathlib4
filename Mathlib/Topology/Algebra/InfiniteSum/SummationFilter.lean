/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Data.Finset.Preimage
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Order.LiminfLimsup

/-!
# Summation filters

We define a `SummationFilter` on `β` to be a filter on the finite subsets of `β`. These are used
in defining summability.
-/

open Set Filter Function

variable {α β γ : Type*}

/-- A filter on the set of finsets of a type. (Used for defining summation methods.) -/
structure SummationFilter (β) where
  /-- The filter -/
  filter : Filter (Finset β)

/-- Unconditional summation: a function on `β` is said to be *unconditionally summable* if its
partial sums over finite subsets converge with respect to the `atTop` filter. -/
@[simps] def unconditional (β) : SummationFilter β where
  filter := atTop

namespace SummationFilter

/-- Typeclass asserting that a summation filter `L` is consistent with unconditional summation,
so that any unconditionally-summable function is `L`-summable with the same sum. -/
class LeAtTop (L : SummationFilter β) : Prop where
  private le_atTop' : L.filter ≤ atTop

lemma le_atTop (L : SummationFilter β) [L.LeAtTop] : L.filter ≤ atTop :=
  LeAtTop.le_atTop'

instance : (unconditional β).LeAtTop := ⟨le_rfl⟩

/-- Typeclass asserting that a summation filter is non-vacuous (if this is not satisfied, then
every function is summable with every possible sum simultaneously). -/
class NeBot (L : SummationFilter β) : Prop where
  private ne_bot' : L.filter.NeBot

instance : (unconditional β).NeBot := ⟨atTop_neBot⟩

/-- Makes the `NeBot` instance visible to the typeclass machinery. -/
instance (L : SummationFilter β) [L.NeBot] : L.filter.NeBot := NeBot.ne_bot'

section support

/-- The support of a summation filter (its `lim inf`, considered as a filter of sets). -/
def support (L : SummationFilter β) : Set β := {b | ∀ᶠ s in L.filter, b ∈ s}

lemma support_eq_limsInf (L : SummationFilter β) :
    support L = limsInf (L.filter.map Finset.toSet) := by
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

instance [IsEmpty β] (L : SummationFilter β) : L.LeAtTop where
  le_atTop' := support_eq_univ_iff.mp <| Subsingleton.elim ..

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
  private eventually_le_support' : ∀ᶠ s in L.filter, ↑s ⊆ L.support

lemma eventually_le_support (L : SummationFilter β) [HasSupport L] :
    ∀ᶠ s in L.filter, ↑s ⊆ L.support :=
  HasSupport.eventually_le_support'

instance (L : SummationFilter β) [L.LeAtTop] : HasSupport L where
  eventually_le_support' := by simp

lemma eventually_mem_or_not_mem (L : SummationFilter β) [HasSupport L] (b : β) :
    (∀ᶠ s in L.filter, b ∈ s) ∨ (∀ᶠ s in L.filter, b ∉ s) :=
  or_iff_not_imp_left.mpr fun hb ↦ by
    filter_upwards [HasSupport.eventually_le_support'] with a ha using Set.notMem_subset ha hb

end has_support

section map_comap

/-- Pushforward of a summation filter along a map (mostly useful for embeddings). -/
@[simps] def map (L : SummationFilter β) (f : β ↪ γ) : SummationFilter γ where
  filter := L.filter.map (Finset.map f)

@[simp] lemma support_map (L : SummationFilter β) [L.NeBot] (f : β ↪ γ) :
    (L.map f).support = f '' L.support := ext fun c ↦ by
  rcases em (c ∈ range f) with ⟨b, rfl⟩ | hc
  · simp [SummationFilter.support]
  · refine ⟨fun hc' ↦ ?_, by grind⟩
    have := Eventually.exists hc'
    grind

/-- Pullback of a summation filter along an embedding. -/
@[simps] def comap (L : SummationFilter β) (f : γ ↪ β) : SummationFilter γ where
  filter := L.filter.map (fun s ↦ s.preimage f f.injective.injOn)

@[simp] lemma support_comap (L : SummationFilter β) (f : γ ↪ β) :
    (L.comap f).support = f ⁻¹' L.support := by
  simp [support]

/-- If `L` has well-defined support, then so does its comap along an embedding. -/
instance (L : SummationFilter β) [HasSupport L] (f : γ ↪ β) : HasSupport (L.comap f) where
  eventually_le_support' := by
    simp only [support_comap, comap_filter, eventually_map, Finset.coe_preimage]
    filter_upwards [L.eventually_le_support] with a using Set.preimage_mono

/-- If `L` has well-defined support, then so does its map along an embedding. -/
instance (L : SummationFilter β) [HasSupport L] (f : β ↪ γ) : HasSupport (L.map f) where
  eventually_le_support' := by
    by_cases h : L.NeBot
    · simp only [map_filter, eventually_map, Finset.coe_map, image_subset_iff, support_map]
      filter_upwards [L.eventually_le_support] with a using by grind
    · have : L.filter = ⊥ := by contrapose! h; exact ⟨⟨h⟩⟩
      simp [this]

end map_comap

/-- This instance is useful for some measure-theoretic statements. -/
instance [Countable β] : IsCountablyGenerated (unconditional β).filter :=
  atTop.isCountablyGenerated

end SummationFilter
