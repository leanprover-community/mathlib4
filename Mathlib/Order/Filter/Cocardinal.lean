/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
import Mathlib.Order.Filter.CountableInter
import Mathlib.Order.Filter.CardinalInter
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Cofinality

/-!
# The cocardinal filter

In this file we define `Filter.cocardinal hc`: the filter of sets with cardinality less than
  `c` that satisfies `Cardinal.aleph0 < c`. Such filters are `CardinalInterFilter` with cardinality
  `c`.

-/

open Set Filter

universe u

variable {α : Type*} {c : Cardinal}

namespace Filter

/-- Construct a filter with cardinal intersection property. This constructor deduces
`Filter.univ_sets` and `Filter.inter_sets` from the cardinal intersection property. -/
def ofCardinalInter (hc : 2 < c) (l : Set (Set α))
    (hp : ∀ S : Set (Set α), (Cardinal.mk S < c) → S ⊆ l → ⋂₀ S ∈ l)
    (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l) : Filter α where
  sets := l
  univ_sets := by
    apply @sInter_empty α ▸ hp ∅ ?_ (empty_subset l)
    rw [Cardinal.mk_eq_zero]
    exact pos_of_gt hc
  sets_of_superset := fun {x y} a a_1 ↦ h_mono x y a a_1
  inter_sets {s t} hs ht := by
    apply sInter_pair s t ▸ hp {s, t} ?_
    · exact insert_subset_iff.2 ⟨hs, singleton_subset_iff.2 ht⟩
    · by_cases h : s = t
      · rw [h]
        have : 1 < c := by
          apply lt_trans _ hc
          norm_num
        simp_all only [mem_singleton_iff, insert_eq_of_mem, Cardinal.mk_fintype,
          Fintype.card_ofSubsingleton,Nat.cast_one]
      · rw [Cardinal.mk_insert, Cardinal.mk_singleton]
        · exact lt_of_eq_of_lt one_add_one_eq_two hc
        · exact h

/-- Construct a filter sets whose complements satisfy a property that is stable under unions
with a certain cardinality. -/
def ofCardinalUnion (hc : 2 < c) (p : Set α → Prop)
    (hUnion : ∀ S : Set (Set α), (Cardinal.mk S < c) → (∀ s ∈ S, p s) → p (⋃₀ S))
    (hmono : ∀ t, p t → ∀ s ⊆ t, p s) : Filter α := by
  refine .ofCardinalInter hc {s | p sᶜ} (fun S hSc hSp ↦ ?_)
    fun s t ht hsub ↦ hmono sᶜ ht tᶜ (compl_subset_compl.2 hsub)
  rw [mem_setOf_eq, compl_sInter]
  exact hUnion (compl '' S) (lt_of_le_of_lt Cardinal.mk_image_le hSc) (forall_mem_image.2 hSp)

-- TO DO: Generalises, CardinalInterFilter generalisation of CountableInterFilter is in another PR.
instance countableInter_ofCardinalnter (hc : Cardinal.aleph0 < c) (l : Set (Set α))
    (hp : ∀ S : Set (Set α), (Cardinal.mk S < c) → S ⊆ l → ⋂₀ S ∈ l)
    (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l) :
    CountableInterFilter (Filter.ofCardinalInter ((Cardinal.nat_lt_aleph0 2).trans hc) l hp h_mono)
  where
    countable_sInter_mem := fun S hS a ↦ hp S (lt_of_le_of_lt (Countable.le_aleph0 hS) hc) a

/-- The filter defined by all sets that have a complement with at most cardinality `c`. For a union
of `c` sets of `c` elements to have `c` elements, we need that `c` is a regular cardinal. -/
def cocardinal {hreg : Cardinal.IsRegular c} : Filter α := by
  have hc : Cardinal.aleph0 ≤ c := Cardinal.IsRegular.aleph0_le hreg
  apply ofCardinalUnion (lt_of_lt_of_le (Cardinal.nat_lt_aleph0 2) hc) (fun s ↦ Cardinal.mk s < c)
  · intro s hS hSc
    apply lt_of_le_of_lt (Cardinal.mk_sUnion_le _)
    apply Cardinal.mul_lt_of_lt hc hS
    apply Cardinal.iSup_lt_of_isRegular hreg hS
    intro i
    simp_all only [Subtype.coe_prop]
  · exact fun _ hSc _ ht ↦ lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset ht) hSc

@[simp]
theorem mem_cocardinal {s : Set α} {hreg : Cardinal.IsRegular c} :
    s ∈ @cocardinal α c hreg ↔ Cardinal.mk (sᶜ : Set α) < c := Iff.rfl
