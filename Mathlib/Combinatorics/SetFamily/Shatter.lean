/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Combinatorics.SetFamily.Compression.Down
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Shattering families

This file defines the shattering property and VC-dimension of set families.

## Main declarations

* `Finset.Shatters`: The shattering property.
* `Finset.shatterer`: The set family of sets shattered by a set family.
* `Finset.vcDim`: The Vapnik-Chervonenkis dimension.

## TODO

* Order-shattering
* Strong shattering
-/

@[expose] public section

open scoped FinsetFamily

namespace Finset
variable {α : Type*} [DecidableEq α] {𝒜 ℬ : Finset (Finset α)} {s t : Finset α} {a : α}

/-- A set family `𝒜` shatters a set `s` if all subsets of `s` can be obtained as the intersection
of `s` and some element of the set family, and we denote this `𝒜.Shatters s`. We also say that `s`
is *traced* by `𝒜`. -/
def Shatters (𝒜 : Finset (Finset α)) (s : Finset α) : Prop := ∀ ⦃t⦄, t ⊆ s → ∃ u ∈ 𝒜, s ∩ u = t

instance : DecidablePred 𝒜.Shatters := fun _s ↦ decidableForallOfDecidableSubsets

lemma Shatters.exists_inter_eq_singleton (hs : Shatters 𝒜 s) (ha : a ∈ s) : ∃ t ∈ 𝒜, s ∩ t = {a} :=
  hs <| singleton_subset_iff.2 ha

lemma Shatters.mono_left (h : 𝒜 ⊆ ℬ) (h𝒜 : 𝒜.Shatters s) : ℬ.Shatters s :=
  fun _t ht ↦ let ⟨u, hu, hut⟩ := h𝒜 ht; ⟨u, h hu, hut⟩

lemma Shatters.mono_right (h : t ⊆ s) (hs : 𝒜.Shatters s) : 𝒜.Shatters t := fun u hu ↦ by
  obtain ⟨v, hv, rfl⟩ := hs (hu.trans h); exact ⟨v, hv, inf_congr_right hu <| inf_le_of_left_le h⟩

lemma Shatters.exists_superset (h : 𝒜.Shatters s) : ∃ t ∈ 𝒜, s ⊆ t :=
  let ⟨t, ht, hst⟩ := h Subset.rfl; ⟨t, ht, inter_eq_left.1 hst⟩

lemma shatters_of_forall_subset (h : ∀ t, t ⊆ s → t ∈ 𝒜) : 𝒜.Shatters s :=
  fun t ht ↦ ⟨t, h _ ht, inter_eq_right.2 ht⟩

protected lemma Shatters.nonempty (h : 𝒜.Shatters s) : 𝒜.Nonempty :=
  let ⟨t, ht, _⟩ := h Subset.rfl; ⟨t, ht⟩

@[simp] lemma shatters_empty : 𝒜.Shatters ∅ ↔ 𝒜.Nonempty :=
  ⟨Shatters.nonempty, fun ⟨s, hs⟩ t ht ↦ ⟨s, hs, by rwa [empty_inter, eq_comm, ← subset_empty]⟩⟩

protected lemma Shatters.subset_iff (h : 𝒜.Shatters s) : t ⊆ s ↔ ∃ u ∈ 𝒜, s ∩ u = t :=
  ⟨fun ht ↦ h ht, by rintro ⟨u, _, rfl⟩; exact inter_subset_left⟩

lemma shatters_iff : 𝒜.Shatters s ↔ 𝒜.image (fun t ↦ s ∩ t) = s.powerset :=
  ⟨fun h ↦ by ext t; rw [mem_image, mem_powerset, h.subset_iff],
    fun h t ht ↦ by rwa [← mem_powerset, ← h, mem_image] at ht⟩

lemma univ_shatters [Fintype α] : univ.Shatters s :=
  shatters_of_forall_subset fun _ _ ↦ mem_univ _

@[simp] lemma shatters_univ [Fintype α] : 𝒜.Shatters univ ↔ 𝒜 = univ := by
  rw [shatters_iff, powerset_univ]; simp_rw [univ_inter, image_id']

/-- The set family of sets that are shattered by `𝒜`. -/
def shatterer (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  {s ∈ 𝒜.biUnion powerset | 𝒜.Shatters s}

@[simp] lemma mem_shatterer : s ∈ 𝒜.shatterer ↔ 𝒜.Shatters s := by
  refine mem_filter.trans <| and_iff_right_of_imp fun h ↦ ?_
  simp_rw [mem_biUnion, mem_powerset]
  exact h.exists_superset

@[gcongr] lemma shatterer_mono (h : 𝒜 ⊆ ℬ) : 𝒜.shatterer ⊆ ℬ.shatterer :=
  fun _ ↦ by simpa using Shatters.mono_left h

lemma subset_shatterer (h : IsLowerSet (𝒜 : Set (Finset α))) : 𝒜 ⊆ 𝒜.shatterer :=
  fun _s hs ↦ mem_shatterer.2 fun t ht ↦ ⟨t, h ht hs, inter_eq_right.2 ht⟩

@[simp] lemma isLowerSet_shatterer (𝒜 : Finset (Finset α)) :
    IsLowerSet (𝒜.shatterer : Set (Finset α)) := fun s t ↦ by simpa using Shatters.mono_right

@[simp] lemma shatterer_eq : 𝒜.shatterer = 𝒜 ↔ IsLowerSet (𝒜 : Set (Finset α)) := by
  refine ⟨fun h ↦ ?_, fun h ↦ Subset.antisymm (fun s hs ↦ ?_) <| subset_shatterer h⟩
  · rw [← h]
    exact isLowerSet_shatterer _
  · obtain ⟨t, ht, hst⟩ := (mem_shatterer.1 hs).exists_superset
    exact h hst ht

@[simp] lemma shatterer_idem : 𝒜.shatterer.shatterer = 𝒜.shatterer := by simp

@[simp] lemma shatters_shatterer : 𝒜.shatterer.Shatters s ↔ 𝒜.Shatters s := by
  simp_rw [← mem_shatterer, shatterer_idem]

protected alias ⟨_, Shatters.shatterer⟩ := shatters_shatterer

private lemma aux (h : ∀ t ∈ 𝒜, a ∉ t) (ht : 𝒜.Shatters t) : a ∉ t := by
  obtain ⟨u, hu, htu⟩ := ht.exists_superset; exact notMem_mono htu <| h u hu

/-- Pajor's variant of the **Sauer-Shelah lemma**. -/
lemma card_le_card_shatterer (𝒜 : Finset (Finset α)) : #𝒜 ≤ #𝒜.shatterer := by
  refine memberFamily_induction_on 𝒜 ?_ ?_ ?_
  · simp
  · rfl
  intro a 𝒜 ih₀ ih₁
  set ℬ : Finset (Finset α) :=
    ((memberSubfamily a 𝒜).shatterer ∩ (nonMemberSubfamily a 𝒜).shatterer).image (insert a)
  have hℬ : #ℬ = #((memberSubfamily a 𝒜).shatterer ∩ (nonMemberSubfamily a 𝒜).shatterer) := by
    refine card_image_of_injOn <| insert_erase_invOn.2.injOn.mono ?_
    simp only [coe_inter, Set.subset_def, Set.mem_inter_iff, mem_coe, Set.mem_setOf_eq, and_imp,
      mem_shatterer]
    exact fun s _ ↦ aux (fun t ht ↦ (mem_filter.1 ht).2)
  rw [← card_memberSubfamily_add_card_nonMemberSubfamily a]
  refine (Nat.add_le_add ih₁ ih₀).trans ?_
  rw [← card_union_add_card_inter, ← hℬ, ← card_union_of_disjoint]
  swap
  · simp only [ℬ, disjoint_left, mem_union, mem_shatterer, mem_image, not_exists, not_and]
    rintro _ (hs | hs) s - rfl
    · exact aux (fun t ht ↦ (mem_memberSubfamily.1 ht).2) hs <| mem_insert_self _ _
    · exact aux (fun t ht ↦ (mem_nonMemberSubfamily.1 ht).2) hs <| mem_insert_self _ _
  refine card_mono <| union_subset (union_subset ?_ <| shatterer_mono <| filter_subset _ _) ?_
  · simp only [subset_iff, mem_shatterer]
    rintro s hs t ht
    obtain ⟨u, hu, rfl⟩ := hs ht
    rw [mem_memberSubfamily] at hu
    refine ⟨insert a u, hu.1, inter_insert_of_notMem fun ha ↦ ?_⟩
    obtain ⟨v, hv, hsv⟩ := hs.exists_inter_eq_singleton ha
    rw [mem_memberSubfamily] at hv
    rw [← singleton_subset_iff (a := a), ← hsv] at hv
    exact hv.2 inter_subset_right
  · refine forall_mem_image.2 fun s hs ↦ mem_shatterer.2 fun t ht ↦ ?_
    simp only [mem_inter, mem_shatterer] at hs
    rw [subset_insert_iff] at ht
    by_cases ha : a ∈ t
    · obtain ⟨u, hu, hsu⟩ := hs.1 ht
      rw [mem_memberSubfamily] at hu
      refine ⟨_, hu.1, ?_⟩
      rw [← insert_inter_distrib, hsu, insert_erase ha]
    · obtain ⟨u, hu, hsu⟩ := hs.2 ht
      rw [mem_nonMemberSubfamily] at hu
      refine ⟨_, hu.1, ?_⟩
      rwa [insert_inter_of_notMem hu.2, hsu, erase_eq_self]

lemma Shatters.of_compression (hs : (𝓓 a 𝒜).Shatters s) : 𝒜.Shatters s := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := hs ht
  rw [Down.mem_compression] at hu
  obtain hu | hu := hu
  · exact ⟨u, hu.1, rfl⟩
  by_cases ha : a ∈ s
  · obtain ⟨v, hv, hsv⟩ := hs <| insert_subset ha ht
    rw [Down.mem_compression] at hv
    obtain hv | hv := hv
    · refine ⟨erase v a, hv.2, ?_⟩
      rw [inter_erase, hsv, erase_insert]
      rintro ha
      rw [insert_eq_self.2 (mem_inter.1 ha).2] at hu
      exact hu.1 hu.2
    rw [insert_eq_self.2 <| inter_subset_right (s₁ := s) ?_] at hv
    cases hv.1 hv.2
    rw [hsv]
    exact mem_insert_self _ _
  · refine ⟨insert a u, hu.2, ?_⟩
    rw [inter_insert_of_notMem ha]

lemma shatterer_compress_subset_shatterer (a : α) (𝒜 : Finset (Finset α)) :
    (𝓓 a 𝒜).shatterer ⊆ 𝒜.shatterer := by
  simp only [subset_iff, mem_shatterer]; exact fun s hs ↦ hs.of_compression

/-! ### Vapnik-Chervonenkis dimension -/

/-- The Vapnik-Chervonenkis dimension of a set family is the maximal size of a set it shatters. -/
@[informal "VC dimension"]
def vcDim (𝒜 : Finset (Finset α)) : ℕ := 𝒜.shatterer.sup card

@[gcongr] lemma vcDim_mono (h𝒜ℬ : 𝒜 ⊆ ℬ) : 𝒜.vcDim ≤ ℬ.vcDim := by unfold vcDim; gcongr

lemma Shatters.card_le_vcDim (hs : 𝒜.Shatters s) : #s ≤ 𝒜.vcDim := le_sup <| mem_shatterer.2 hs

/-- Down-compressing decreases the VC-dimension. -/
lemma vcDim_compress_le (a : α) (𝒜 : Finset (Finset α)) : (𝓓 a 𝒜).vcDim ≤ 𝒜.vcDim :=
  sup_mono <| shatterer_compress_subset_shatterer _ _

/-- The **Sauer-Shelah lemma**. -/
@[informal "Sauer-Shelah lemma"]
lemma card_shatterer_le_sum_vcDim [Fintype α] :
    #𝒜.shatterer ≤ ∑ k ∈ Iic 𝒜.vcDim, (Fintype.card α).choose k := by
  simp_rw [← card_univ, ← card_powersetCard]
  refine (card_le_card fun s hs ↦ mem_biUnion.2 ⟨#s, ?_⟩).trans card_biUnion_le
  exact ⟨mem_Iic.2 (mem_shatterer.1 hs).card_le_vcDim, mem_powersetCard_univ.2 rfl⟩

end Finset
