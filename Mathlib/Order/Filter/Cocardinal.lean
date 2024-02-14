/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
import Mathlib.Order.Filter.CountableInter
import Mathlib.SetTheory.Cardinal.Ordinal

/-!
# The cocardinal filter

In this file we define `Filter.cocardinal hc`: the filter of sets with cardinality less than
  `c` that satisfies `c ≥ Cardinal.aleph0`.

-/

open Set Filter

universe u

variable {α : Type*}

namespace Filter

/-- Construct a filter with cardinal intersection property. This constructor deduces
`Filter.univ_sets` and `Filter.inter_sets` from the cardinal intersection property. -/
def ofCardinalInter {c : Cardinal} (hc : Cardinal.aleph0 ≤ c) (l : Set (Set α))
    (hp : ∀ S : Set (Set α), (Cardinal.mk S < c) → S ⊆ l → ⋂₀ S ∈ l)
    (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l) : Filter α where
  sets := l
  univ_sets := by
    apply @sInter_empty α ▸ hp ∅ ?_ (empty_subset l)
    rw [Cardinal.mk_eq_zero]
    exact gt_of_ge_of_gt hc Cardinal.aleph0_pos
  sets_of_superset := fun {x y} a a_1 ↦ h_mono x y a a_1
  inter_sets {s t} hs ht := by
    apply sInter_pair s t ▸ hp {s, t} ?_
    · exact insert_subset_iff.2 ⟨hs, singleton_subset_iff.2 ht⟩
    · exact gt_of_ge_of_gt hc (Cardinal.lt_aleph0_of_finite _)

/-- Construct a filter sets whose complements satisfy a property that is stable under unions
with a certain cardinality. -/
def ofCardinalUnion {c : Cardinal} (hc : Cardinal.aleph0 ≤ c) (p : Set α → Prop)
    (hUnion : ∀ S : Set (Set α), (Cardinal.mk S < c) → (∀ s ∈ S, p s) → p (⋃₀ S))
    (hmono : ∀ t, p t → ∀ s ⊆ t, p s) : Filter α := by
  refine .ofCardinalInter hc {s | p sᶜ} (fun S hSc hSp ↦ ?_) fun s t ht hsub ↦ hmono sᶜ ht tᶜ (compl_subset_compl.2 hsub)
  rw [mem_setOf_eq, compl_sInter]
  exact hUnion (compl '' S) (lt_of_le_of_lt Cardinal.mk_image_le hSc) (ball_image_iff.2 hSp)

-- Of course, this would generalise to CardinalInterFilter under a suitable definition for these.
instance countableInter_ofCardinalnter {c : Cardinal} (hc : Cardinal.aleph0 < c) (l : Set (Set α))
    (hp : ∀ S : Set (Set α), (Cardinal.mk S < c) → S ⊆ l → ⋂₀ S ∈ l)
    (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l) :
    CountableInterFilter (Filter.ofCardinalInter hc.le l hp h_mono) where
  countable_sInter_mem := fun S hS a ↦ hp S (lt_of_le_of_lt (Countable.le_aleph0 hS) hc) a

/-- The filter defined by all sets that have a complement with at most cardinality `c`. -/
def cocardinal {c : Cardinal} (hc : Cardinal.aleph0 ≤ c) : Filter α := by
  apply ofCardinalUnion hc (fun s ↦ Cardinal.mk s < c)
  · intro s hS hSc
    apply lt_of_le_of_lt
    apply Cardinal.mk_sUnion_le
    apply Cardinal.mul_lt_of_lt hc hS
    sorry
  · exact fun _ hSc _ ht ↦ lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset ht) hSc

@[simp]
theorem mem_cocardinal {s : Set α} {c : Cardinal} {hc : Cardinal.aleph0 ≤ c} :
    s ∈ @cocardinal α c hc ↔ Cardinal.mk (sᶜ : Set α) < c := Iff.rfl
