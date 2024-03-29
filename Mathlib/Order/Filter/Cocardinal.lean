/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Order.Filter.Pi
import Mathlib.Order.Filter.CountableInter
import Mathlib.Order.Filter.CardinalInter
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Cofinality

/-!
# The cocardinal filter

In this file we define `Filter.cocardinal hc`: the filter of sets with cardinality less than
  a regular cardinal `c` that satisfies `Cardinal.aleph0 < c`.
  Such filters are `CardinalInterFilter` with cardinality `c`.

-/

open Set Filter Cardinal

universe u
variable {ι : Type u} {α β : Type u}
variable {c : Cardinal.{u}} {hreg : Cardinal.IsRegular c}
variable {l : Filter α}

namespace Filter

/-- The filter defined by all sets that have a complement with at most cardinality `c`. For a union
of `c` sets of `c` elements to have `c` elements, we need that `c` is a regular cardinal. -/
def cocardinal (hreg : Cardinal.IsRegular c) : Filter α := by
  have hc : Cardinal.aleph0 ≤ c := Cardinal.IsRegular.aleph0_le hreg
  apply ofCardinalUnion (fun s ↦ Cardinal.mk s < c) (lt_of_lt_of_le (Cardinal.nat_lt_aleph0 2) hc)
  · intro s hS hSc
    apply lt_of_le_of_lt (Cardinal.mk_sUnion_le _)
    apply Cardinal.mul_lt_of_lt hc hS
    apply Cardinal.iSup_lt_of_isRegular hreg hS
    intro i
    simp_all only [Subtype.coe_prop]
  · exact fun _ hSc _ ht ↦ lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset ht) hSc

@[simp]
theorem mem_cocardinal {s : Set α} :
    s ∈ @cocardinal α c hreg ↔ Cardinal.mk (sᶜ : Set α) < c := Iff.rfl

instance cardinalInter_ofCoCardinal :
    CardinalInterFilter (@cocardinal α c hreg) c where
  cardinal_sInter_mem := by
    have hc : Cardinal.aleph0 ≤ c := Cardinal.IsRegular.aleph0_le hreg
    intro S hS hSs
    rw [mem_cocardinal]
    have := fun s hs => mem_cocardinal.1 (hSs s hs)
    rw [Set.compl_sInter]
    apply lt_of_le_of_lt (Cardinal.mk_sUnion_le _)
    apply Cardinal.mul_lt_of_lt hc
    · apply lt_of_le_of_lt Cardinal.mk_image_le hS
    · apply Cardinal.iSup_lt_of_isRegular hreg
      apply lt_of_le_of_lt Cardinal.mk_image_le hS
      intro i
      aesop

@[simp]
theorem eventually_cocardinal {p : α → Prop} :
    (∀ᶠ x in cocardinal hreg, p x) ↔ #{ x | ¬p x } < c := Iff.rfl

theorem hasBasis_cocardinal : HasBasis (cocardinal hreg)
    (fun s : Set α => (#s < c)) compl :=
  ⟨fun s =>
    ⟨fun h => ⟨sᶜ, h, (compl_compl s).subset⟩, fun ⟨_t, htf, hts⟩ => by
      have : #↑sᶜ < c := by
        apply lt_of_le_of_lt _ htf
        rw [compl_subset_comm] at hts
        apply Cardinal.mk_le_mk_of_subset hts
      simp_all only [mem_cocardinal] ⟩⟩

theorem frequently_cocardinal_iff_cardinal_le {p : α → Prop} :
    (∃ᶠ x in cocardinal hreg, p x) ↔ c ≤ # { x | p x }  := by
  simp only [Filter.Frequently, eventually_cocardinal, not_not,coe_setOf,
    not_lt]

lemma frequently_cocardinal_mem_iff_cardinal_le {s : Set α} :
    (∃ᶠ x in cocardinal hreg, x ∈ s) ↔ c ≤ #s := frequently_cocardinal_iff_cardinal_le

@[simp]
lemma cocardinal_inf_principal_neBot_iff {s : Set α} :
    (cocardinal hreg ⊓ 𝓟 s).NeBot ↔ c ≤ #s :=
  frequently_mem_iff_neBot.symm.trans frequently_cocardinal_iff_cardinal_le

theorem _root_.Set.compl_mem_cocardinal {s : Set α} (hs : #s < c) :
    sᶜ ∈ @cocardinal α c hreg :=
  mem_cocardinal.2 <| (compl_compl s).symm ▸ hs

theorem _root_.Set.Finite.compl_mem_cocardinal {s : Set α} (hs : s.Finite) :
    sᶜ ∈ @cocardinal α c hreg := by
  have : #s < c := lt_of_lt_of_le (Finite.lt_aleph0 hs) (Cardinal.IsRegular.aleph0_le hreg)
  exact Set.compl_mem_cocardinal this

theorem _root_.Set.eventually_cocardinal_nmem {s : Set α} (hs : #s < c) :
    ∀ᶠ x in cocardinal hreg, x ∉ s :=
  s.compl_mem_cocardinal hs

theorem _root_.Finset.eventually_cocardinal_nmem (s : Finset α) :
    ∀ᶠ x in cocardinal hreg, x ∉ s := by
  have : #s < c := lt_of_lt_of_le (finset_card_lt_aleph0 s) (Cardinal.IsRegular.aleph0_le hreg)
  exact Set.eventually_cocardinal_nmem this

theorem _root_.Set.cardinal_iff_frequently_cocardinal {s : Set α} :
    c ≤ #s ↔ ∃ᶠ x in cocardinal hreg, x ∈ s :=
  frequently_cocardinal_iff_cardinal_le.symm

theorem eventually_cocardinal_ne (x : α) : ∀ᶠ a in cocardinal hreg, a ≠ x := by
  simp [Set.finite_singleton x]
  exact IsRegular.nat_lt hreg 1

abbrev cocountable : Filter α := cocardinal Cardinal.isRegular_aleph_one

@[simp]
theorem mem_cocountable {s : Set α} :
    s ∈ @cocountable α ↔ (sᶜ : Set α).Countable := by
  rw [Cardinal.countable_iff_lt_aleph_one, mem_cocardinal]
