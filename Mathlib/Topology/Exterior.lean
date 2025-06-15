/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Yury Kudryashov
-/
import Mathlib.Topology.NhdsSet
import Mathlib.Topology.Inseparable

/-!
# Exterior of a set

We define `exterior s` to be the intersection of all neighborhoods of `s`,
see `Mathlib/Topology/Defs/Filter.lean`.
Note that this construction has no standard name in the literature.

In this file we prove basic properties of this operation.
-/

open Set Filter
open scoped Topology

variable {ι : Sort*} {X : Type*} [TopologicalSpace X] {s t : Set X} {x y : X}

lemma exterior_singleton_eq_ker_nhds (x : X) : exterior {x} = (𝓝 x).ker := by simp [exterior]

@[simp]
theorem mem_exterior_singleton : x ∈ exterior {y} ↔ x ⤳ y := by
  rw [exterior_singleton_eq_ker_nhds, ker_nhds_eq_specializes, mem_setOf]

lemma exterior_def (s : Set X) : exterior s = ⋂₀ {t : Set X | IsOpen t ∧ s ⊆ t} :=
  (hasBasis_nhdsSet _).ker.trans sInter_eq_biInter.symm

lemma mem_exterior : x ∈ exterior s ↔ ∀ U, IsOpen U → s ⊆ U → x ∈ U := by simp [exterior_def]

lemma subset_exterior_iff : s ⊆ exterior t ↔ ∀ U, IsOpen U → t ⊆ U → s ⊆ U := by
  simp [exterior_def]

lemma subset_exterior : s ⊆ exterior s := subset_exterior_iff.2 fun _ _ ↦ id

lemma exterior_minimal (h₁ : s ⊆ t) (h₂ : IsOpen t) : exterior s ⊆ t := by
  rw [exterior_def]; exact sInter_subset_of_mem ⟨h₂, h₁⟩

lemma IsOpen.exterior_eq (h : IsOpen s) : exterior s = s :=
  (exterior_minimal Subset.rfl h).antisymm subset_exterior

lemma IsOpen.exterior_subset (ht : IsOpen t) : exterior s ⊆ t ↔ s ⊆ t :=
  ⟨subset_exterior.trans, fun h ↦ exterior_minimal h ht⟩

@[simp]
theorem exterior_iUnion (s : ι → Set X) : exterior (⋃ i, s i) = ⋃ i, exterior (s i) := by
  simp only [exterior, nhdsSet_iUnion, ker_iSup]

@[simp]
theorem exterior_union (s t : Set X) : exterior (s ∪ t) = exterior s ∪ exterior t := by
  simp only [exterior, nhdsSet_union, ker_sup]

@[simp]
theorem exterior_sUnion (S : Set (Set X)) : exterior (⋃₀ S) = ⋃ s ∈ S, exterior s := by
  simp only [sUnion_eq_biUnion, exterior_iUnion]

theorem mem_exterior_iff_specializes : x ∈ exterior s ↔ ∃ y ∈ s, x ⤳ y := calc
  x ∈ exterior s ↔ x ∈ exterior (⋃ y ∈ s, {y}) := by simp
  _ ↔ ∃ y ∈ s, x ⤳ y := by
    simp only [exterior_iUnion, mem_exterior_singleton, mem_iUnion₂, exists_prop]

@[mono] lemma exterior_mono : Monotone (exterior : Set X → Set X) :=
  fun _s _t h ↦ ker_mono <| nhdsSet_mono h

/-- This name was used to be used for the `Iff` version,
see `exterior_subset_exterior_iff_nhdsSet`.
-/
@[gcongr] lemma exterior_subset_exterior (h : s ⊆ t) : exterior s ⊆ exterior t := exterior_mono h

@[simp] lemma exterior_subset_exterior_iff_nhdsSet : exterior s ⊆ exterior t ↔ 𝓝ˢ s ≤ 𝓝ˢ t := by
  simp +contextual only [subset_exterior_iff, (hasBasis_nhdsSet _).ge_iff,
    and_imp, IsOpen.mem_nhdsSet, IsOpen.exterior_subset]

theorem exterior_eq_exterior_iff_nhdsSet : exterior s = exterior t ↔ 𝓝ˢ s = 𝓝ˢ t := by
  simp [le_antisymm_iff]

lemma specializes_iff_exterior_subset : x ⤳ y ↔ exterior {x} ⊆ exterior {y} := by
  simp [Specializes]

theorem exterior_iInter_subset {s : ι → Set X} : exterior (⋂ i, s i) ⊆ ⋂ i, exterior (s i) :=
  exterior_mono.map_iInf_le

theorem exterior_inter_subset {s t : Set X} : exterior (s ∩ t) ⊆ exterior s ∩ exterior t :=
  exterior_mono.map_inf_le _ _

theorem exterior_sInter_subset {s : Set (Set X)} : exterior (⋂₀ s) ⊆ ⋂ x ∈ s, exterior x :=
  exterior_mono.map_sInf_le

@[simp] lemma exterior_empty : exterior (∅ : Set X) = ∅ := isOpen_empty.exterior_eq
@[simp] lemma exterior_univ : exterior (univ : Set X) = univ := isOpen_univ.exterior_eq

@[simp] lemma exterior_eq_empty : exterior s = ∅ ↔ s = ∅ :=
  ⟨eq_bot_mono subset_exterior, by rintro rfl; exact exterior_empty⟩

@[simp] lemma nhdsSet_exterior (s : Set X) : 𝓝ˢ (exterior s) = 𝓝ˢ s := by
  refine le_antisymm ((hasBasis_nhdsSet _).ge_iff.2 ?_) (nhdsSet_mono subset_exterior)
  exact fun U ⟨hUo, hsU⟩ ↦ hUo.mem_nhdsSet.2 <| hUo.exterior_subset.2 hsU

@[simp] lemma exterior_exterior (s : Set X) : exterior (exterior s) = exterior s := by
  simp only [exterior_eq_exterior_iff_nhdsSet, nhdsSet_exterior]
