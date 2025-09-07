/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Yury Kudryashov
-/
import Mathlib.Topology.NhdsSet
import Mathlib.Topology.Inseparable

/-!
# Neighborhoods kernel of a set

In `Mathlib/Topology/Defs/Filter.lean`, `nhdsKer s` is defined to be the intersection of all
neighborhoods of `s`.
Note that this construction has no standard name in the literature.

In this file we prove basic properties of this operation.
-/

open Set Filter
open scoped Topology

variable {ι : Sort*} {X : Type*} [TopologicalSpace X] {s t : Set X} {x y : X}

lemma nhdsKer_singleton_eq_ker_nhds (x : X) : nhdsKer {x} = (𝓝 x).ker := by simp [nhdsKer]

@[deprecated (since := "2025-07-09")]
alias exterior_singleton_eq_ker_nhds := nhdsKer_singleton_eq_ker_nhds

@[simp]
theorem mem_nhdsKer_singleton : x ∈ nhdsKer {y} ↔ x ⤳ y := by
  rw [nhdsKer_singleton_eq_ker_nhds, ker_nhds_eq_specializes, mem_setOf]

@[deprecated (since := "2025-07-09")] alias mem_exterior_singleton := mem_nhdsKer_singleton

lemma nhdsKer_def (s : Set X) : nhdsKer s = ⋂₀ {t : Set X | IsOpen t ∧ s ⊆ t} :=
  (hasBasis_nhdsSet _).ker.trans sInter_eq_biInter.symm

@[deprecated (since := "2025-07-09")] alias exterior_def := nhdsKer_def

lemma mem_nhdsKer : x ∈ nhdsKer s ↔ ∀ U, IsOpen U → s ⊆ U → x ∈ U := by simp [nhdsKer_def]

@[deprecated (since := "2025-07-09")] alias mem_exterior := mem_nhdsKer

lemma subset_nhdsKer_iff : s ⊆ nhdsKer t ↔ ∀ U, IsOpen U → t ⊆ U → s ⊆ U := by
  simp [nhdsKer_def]

@[deprecated (since := "2025-07-09")] alias subset_exterior_iff := subset_nhdsKer_iff

lemma subset_nhdsKer : s ⊆ nhdsKer s := subset_nhdsKer_iff.2 fun _ _ ↦ id

@[deprecated (since := "2025-07-09")] alias subset_exterior := subset_nhdsKer

lemma nhdsKer_minimal (h₁ : s ⊆ t) (h₂ : IsOpen t) : nhdsKer s ⊆ t := by
  rw [nhdsKer_def]; exact sInter_subset_of_mem ⟨h₂, h₁⟩

@[deprecated (since := "2025-07-09")] alias exterior_minimal := nhdsKer_minimal

lemma IsOpen.nhdsKer_eq (h : IsOpen s) : nhdsKer s = s :=
  (nhdsKer_minimal Subset.rfl h).antisymm subset_nhdsKer

@[deprecated (since := "2025-07-09")] alias IsOpen.exterior_eq := IsOpen.nhdsKer_eq

lemma IsOpen.nhdsKer_subset (ht : IsOpen t) : nhdsKer s ⊆ t ↔ s ⊆ t :=
  ⟨subset_nhdsKer.trans, fun h ↦ nhdsKer_minimal h ht⟩

@[deprecated (since := "2025-07-09")] alias IsOpen.exterior_subset := IsOpen.nhdsKer_subset

@[simp]
theorem nhdsKer_iUnion (s : ι → Set X) : nhdsKer (⋃ i, s i) = ⋃ i, nhdsKer (s i) := by
  simp only [nhdsKer, nhdsSet_iUnion, ker_iSup]

@[deprecated (since := "2025-07-09")] alias exterior_iUnion := nhdsKer_iUnion

@[simp]
theorem nhdsKer_union (s t : Set X) : nhdsKer (s ∪ t) = nhdsKer s ∪ nhdsKer t := by
  simp only [nhdsKer, nhdsSet_union, ker_sup]

@[deprecated (since := "2025-07-09")] alias exterior_union := nhdsKer_union

@[simp]
theorem nhdsKer_sUnion (S : Set (Set X)) : nhdsKer (⋃₀ S) = ⋃ s ∈ S, nhdsKer s := by
  simp only [sUnion_eq_biUnion, nhdsKer_iUnion]

@[deprecated (since := "2025-07-09")] alias exterior_sUnion := nhdsKer_sUnion

theorem mem_nhdsKer_iff_specializes : x ∈ nhdsKer s ↔ ∃ y ∈ s, x ⤳ y := calc
  x ∈ nhdsKer s ↔ x ∈ nhdsKer (⋃ y ∈ s, {y}) := by simp
  _ ↔ ∃ y ∈ s, x ⤳ y := by
    simp only [nhdsKer_iUnion, mem_nhdsKer_singleton, mem_iUnion₂, exists_prop]

@[deprecated (since := "2025-07-09")]
alias mem_exterior_iff_specializes := mem_nhdsKer_iff_specializes

@[mono] lemma nhdsKer_mono : Monotone (nhdsKer : Set X → Set X) :=
  fun _s _t h ↦ ker_mono <| nhdsSet_mono h

@[deprecated (since := "2025-07-09")] alias exterior_mono := nhdsKer_mono

/-- This name was used to be used for the `Iff` version,
see `nhdsKer_subset_nhdsKer_iff_nhdsSet`.
-/
@[gcongr] lemma nhdsKer_subset_nhdsKer (h : s ⊆ t) : nhdsKer s ⊆ nhdsKer t := nhdsKer_mono h

@[deprecated (since := "2025-07-09")] alias exterior_subset_exterior := nhdsKer_subset_nhdsKer

@[simp] lemma nhdsKer_subset_nhdsKer_iff_nhdsSet : nhdsKer s ⊆ nhdsKer t ↔ 𝓝ˢ s ≤ 𝓝ˢ t := by
  simp +contextual only [subset_nhdsKer_iff, (hasBasis_nhdsSet _).ge_iff,
    and_imp, IsOpen.mem_nhdsSet, IsOpen.nhdsKer_subset]

@[deprecated (since := "2025-07-09")]
alias exterior_subset_exterior_iff_nhdsSet := nhdsKer_subset_nhdsKer_iff_nhdsSet

theorem nhdsKer_eq_nhdsKer_iff_nhdsSet : nhdsKer s = nhdsKer t ↔ 𝓝ˢ s = 𝓝ˢ t := by
  simp [le_antisymm_iff]

@[deprecated (since := "2025-07-09")]
alias exterior_eq_exterior_iff_nhdsSet := nhdsKer_eq_nhdsKer_iff_nhdsSet

lemma specializes_iff_nhdsKer_subset : x ⤳ y ↔ nhdsKer {x} ⊆ nhdsKer {y} := by
  simp [Specializes]

@[deprecated (since := "2025-07-09")]
alias specializes_iff_exterior_subset := specializes_iff_nhdsKer_subset

theorem nhdsKer_iInter_subset {s : ι → Set X} : nhdsKer (⋂ i, s i) ⊆ ⋂ i, nhdsKer (s i) :=
  nhdsKer_mono.map_iInf_le

@[deprecated (since := "2025-07-09")] alias exterior_iInter_subset := nhdsKer_iInter_subset

theorem nhdsKer_inter_subset {s t : Set X} : nhdsKer (s ∩ t) ⊆ nhdsKer s ∩ nhdsKer t :=
  nhdsKer_mono.map_inf_le _ _

@[deprecated (since := "2025-07-09")] alias exterior_inter_subset := nhdsKer_inter_subset

theorem nhdsKer_sInter_subset {s : Set (Set X)} : nhdsKer (⋂₀ s) ⊆ ⋂ x ∈ s, nhdsKer x :=
  nhdsKer_mono.map_sInf_le

@[deprecated (since := "2025-07-09")] alias exterior_sInter_subset := nhdsKer_sInter_subset

@[simp] lemma nhdsKer_empty : nhdsKer (∅ : Set X) = ∅ := isOpen_empty.nhdsKer_eq

@[deprecated (since := "2025-07-09")] alias exterior_empty := nhdsKer_empty

@[simp] lemma nhdsKer_univ : nhdsKer (univ : Set X) = univ := isOpen_univ.nhdsKer_eq

@[deprecated (since := "2025-07-09")] alias exterior_univ := nhdsKer_univ

@[simp] lemma nhdsKer_eq_empty : nhdsKer s = ∅ ↔ s = ∅ :=
  ⟨eq_bot_mono subset_nhdsKer, by rintro rfl; exact nhdsKer_empty⟩

@[deprecated (since := "2025-07-09")] alias exterior_eq_empty := nhdsKer_eq_empty

@[simp] lemma nhdsSet_nhdsKer (s : Set X) : 𝓝ˢ (nhdsKer s) = 𝓝ˢ s := by
  refine le_antisymm ((hasBasis_nhdsSet _).ge_iff.2 ?_) (nhdsSet_mono subset_nhdsKer)
  exact fun U ⟨hUo, hsU⟩ ↦ hUo.mem_nhdsSet.2 <| hUo.nhdsKer_subset.2 hsU

@[deprecated (since := "2025-07-09")] alias nhdsSet_exterior := nhdsSet_nhdsKer

@[simp] lemma nhdsKer_nhdsKer (s : Set X) : nhdsKer (nhdsKer s) = nhdsKer s := by
  simp only [nhdsKer_eq_nhdsKer_iff_nhdsSet, nhdsSet_nhdsKer]

@[deprecated (since := "2025-07-09")] alias exterior_exterior := nhdsKer_nhdsKer
