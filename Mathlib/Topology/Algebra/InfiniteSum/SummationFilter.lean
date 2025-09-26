/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Data.Finset.Preimage
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

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

/-- Typeclass asserting that a summation filter is consistent with unconditional summation,
so that any unconditionally-summable function is summable for the filter with the same sum. -/
class LeAtTop (L : SummationFilter β) : Prop where
  private le_atTop' : L.filter ≤ atTop

instance : (unconditional β).LeAtTop := ⟨le_rfl⟩

lemma le_atTop (L : SummationFilter β) [L.LeAtTop] : L.filter ≤ atTop :=
  LeAtTop.le_atTop'

/-- Typeclass asserting that a summation filter is non-vacuous (if this is not satisfied, then
every function is summable with every possible sum simultaneously). -/
class NeBot (L : SummationFilter β) : Prop where
  private ne_bot' : L.filter.NeBot

instance : (unconditional β).NeBot := ⟨atTop_neBot⟩

/-- Makes the `NeBot`instance visible to the typeclass machinery. -/
instance (L : SummationFilter β) [L.NeBot] : L.filter.NeBot := NeBot.ne_bot'

/-- The support of a summation filter (the set of arguments that contribute to the summation).
This usually only interesting when `L.HasSupport` holds. -/
def support (L : SummationFilter β) : Set β := {b | ∀ᶠ s in L.filter, b ∈ s}

@[simp] lemma support_eq_univ (L : SummationFilter β) [L.LeAtTop] : L.support = univ := by
  refine eq_univ_iff_forall.mpr fun b ↦ ?_
  filter_upwards [L.le_atTop (eventually_ge_atTop {b})] using by simp

/-- Decidability instance: useful when working with `Finset` sums / products. -/
instance (L : SummationFilter β) [L.LeAtTop] : DecidablePred (· ∈ L.support) :=
  fun b ↦ isTrue (by simp)

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

section has_support

/-- Sanity condition: every `b` is either eventually in all sets in the filter, or eventually
not in any set in the filter. This is required for finitely-supported functions to be summable. -/
class HasSupport (L : SummationFilter β) : Prop where
  private eventually_le_support' : ∀ᶠ s in L.filter, ↑s ⊆ L.support

lemma eventually_le_support (L : SummationFilter β) [HasSupport L] :
    ∀ᶠ s in L.filter, ↑s ⊆ L.support :=
  HasSupport.eventually_le_support'

instance (L : SummationFilter β) [L.LeAtTop] : HasSupport L where
  eventually_le_support' := by simp

instance (L : SummationFilter β) [IsEmpty β] : L.HasSupport :=
  ⟨Eventually.of_forall fun _ ↦ le_of_eq <| Subsingleton.elim _ _⟩

lemma eventually_mem_or_not_mem (L : SummationFilter β) [HasSupport L] (b : β) :
    (∀ᶠ s in L.filter, b ∈ s) ∨ (∀ᶠ s in L.filter, b ∉ s) :=
  or_iff_not_imp_left.mpr fun hb ↦ by
    filter_upwards [HasSupport.eventually_le_support'] with a ha using Set.notMem_subset ha hb

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

end has_support

/-- This instance is useful for some measure-theoretic statements. -/
instance [Countable β] : IsCountablyGenerated (unconditional β).filter :=
  atTop.isCountablyGenerated

end SummationFilter
