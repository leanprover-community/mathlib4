/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Yury Kudryashov
-/
module

public import Mathlib.Topology.Constructions
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Init
import Mathlib.Order.Filter.Ker
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Monotonicity.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Inseparable
import Mathlib.Topology.NhdsSet

/-!
# Neighborhoods kernel of a set

In `Mathlib/Topology/Defs/Filter.lean`, `nhdsKer s` is defined to be the intersection of all
neighborhoods of `s`.
Note that this construction has no standard name in the literature.

In this file we prove basic properties of this operation.
-/

public section

open Set Filter
open scoped Topology

variable {ι : Sort*} {X : Type*} [TopologicalSpace X] {s t : Set X} {x y : X}

lemma nhdsKer_singleton_eq_ker_nhds (x : X) : nhdsKer {x} = (𝓝 x).ker := by simp [nhdsKer]

@[simp]
theorem mem_nhdsKer_singleton : x ∈ nhdsKer {y} ↔ x ⤳ y := by
  rw [nhdsKer_singleton_eq_ker_nhds, ker_nhds_eq_specializes, mem_setOf]

lemma nhdsKer_def (s : Set X) : nhdsKer s = ⋂₀ {t : Set X | IsOpen t ∧ s ⊆ t} :=
  (hasBasis_nhdsSet _).ker.trans sInter_eq_biInter.symm

lemma mem_nhdsKer : x ∈ nhdsKer s ↔ ∀ U, IsOpen U → s ⊆ U → x ∈ U := by simp [nhdsKer_def]

lemma subset_nhdsKer_iff : s ⊆ nhdsKer t ↔ ∀ U, IsOpen U → t ⊆ U → s ⊆ U := by
  simp [nhdsKer_def]

lemma subset_nhdsKer : s ⊆ nhdsKer s := subset_nhdsKer_iff.2 fun _ _ ↦ id

lemma nhdsKer_minimal (h₁ : s ⊆ t) (h₂ : IsOpen t) : nhdsKer s ⊆ t := by
  rw [nhdsKer_def]; exact sInter_subset_of_mem ⟨h₂, h₁⟩

lemma IsOpen.nhdsKer_eq (h : IsOpen s) : nhdsKer s = s :=
  (nhdsKer_minimal Subset.rfl h).antisymm subset_nhdsKer

lemma IsOpen.nhdsKer_subset (ht : IsOpen t) : nhdsKer s ⊆ t ↔ s ⊆ t :=
  ⟨subset_nhdsKer.trans, fun h ↦ nhdsKer_minimal h ht⟩

@[simp]
theorem nhdsKer_iUnion (s : ι → Set X) : nhdsKer (⋃ i, s i) = ⋃ i, nhdsKer (s i) := by
  simp only [nhdsKer, nhdsSet_iUnion, ker_iSup]

theorem nhdsKer_biUnion {ι : Type*} (s : Set ι) (t : ι → Set X) :
    nhdsKer (⋃ i ∈ s, t i) = ⋃ i ∈ s, nhdsKer (t i) := by
  simp only [nhdsKer_iUnion]

@[simp]
theorem nhdsKer_union (s t : Set X) : nhdsKer (s ∪ t) = nhdsKer s ∪ nhdsKer t := by
  simp only [nhdsKer, nhdsSet_union, ker_sup]

@[simp]
theorem nhdsKer_sUnion (S : Set (Set X)) : nhdsKer (⋃₀ S) = ⋃ s ∈ S, nhdsKer s := by
  simp only [sUnion_eq_biUnion, nhdsKer_iUnion]

theorem mem_nhdsKer_iff_specializes : x ∈ nhdsKer s ↔ ∃ y ∈ s, x ⤳ y := calc
  x ∈ nhdsKer s ↔ x ∈ nhdsKer (⋃ y ∈ s, {y}) := by simp
  _ ↔ ∃ y ∈ s, x ⤳ y := by
    simp only [nhdsKer_iUnion, mem_nhdsKer_singleton, mem_iUnion₂, exists_prop]

@[mono] lemma nhdsKer_mono : Monotone (nhdsKer : Set X → Set X) :=
  fun _s _t h ↦ ker_mono <| nhdsSet_mono h

/-- This name was used to be used for the `Iff` version,
see `nhdsKer_subset_nhdsKer_iff_nhdsSet`.
-/
@[gcongr] lemma nhdsKer_subset_nhdsKer (h : s ⊆ t) : nhdsKer s ⊆ nhdsKer t := nhdsKer_mono h

@[simp] lemma nhdsKer_subset_nhdsKer_iff_nhdsSet : nhdsKer s ⊆ nhdsKer t ↔ 𝓝ˢ s ≤ 𝓝ˢ t := by
  simp +contextual only [subset_nhdsKer_iff, (hasBasis_nhdsSet _).ge_iff,
    and_imp, IsOpen.mem_nhdsSet, IsOpen.nhdsKer_subset]

theorem nhdsKer_eq_nhdsKer_iff_nhdsSet : nhdsKer s = nhdsKer t ↔ 𝓝ˢ s = 𝓝ˢ t := by
  simp [le_antisymm_iff]

lemma specializes_iff_nhdsKer_subset : x ⤳ y ↔ nhdsKer {x} ⊆ nhdsKer {y} := by
  simp [Specializes]

theorem nhdsKer_iInter_subset {s : ι → Set X} : nhdsKer (⋂ i, s i) ⊆ ⋂ i, nhdsKer (s i) :=
  nhdsKer_mono.map_iInf_le

theorem nhdsKer_inter_subset {s t : Set X} : nhdsKer (s ∩ t) ⊆ nhdsKer s ∩ nhdsKer t :=
  nhdsKer_mono.map_inf_le _ _

theorem nhdsKer_sInter_subset {s : Set (Set X)} : nhdsKer (⋂₀ s) ⊆ ⋂ x ∈ s, nhdsKer x :=
  nhdsKer_mono.map_sInf_le

@[simp] lemma nhdsKer_empty : nhdsKer (∅ : Set X) = ∅ := isOpen_empty.nhdsKer_eq

@[simp] lemma nhdsKer_univ : nhdsKer (univ : Set X) = univ := isOpen_univ.nhdsKer_eq

@[simp] lemma nhdsKer_eq_empty : nhdsKer s = ∅ ↔ s = ∅ :=
  ⟨eq_bot_mono subset_nhdsKer, by rintro rfl; exact nhdsKer_empty⟩

@[simp] lemma nhdsSet_nhdsKer (s : Set X) : 𝓝ˢ (nhdsKer s) = 𝓝ˢ s := by
  refine le_antisymm ((hasBasis_nhdsSet _).ge_iff.2 ?_) (nhdsSet_mono subset_nhdsKer)
  exact fun U ⟨hUo, hsU⟩ ↦ hUo.mem_nhdsSet.2 <| hUo.nhdsKer_subset.2 hsU

@[simp] lemma nhdsKer_nhdsKer (s : Set X) : nhdsKer (nhdsKer s) = nhdsKer s := by
  simp only [nhdsKer_eq_nhdsKer_iff_nhdsSet, nhdsSet_nhdsKer]

lemma nhdsKer_pair {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) : nhdsKer {(x, y)} = nhdsKer {x} ×ˢ nhdsKer {y} := by
  simp_rw [nhdsKer_singleton_eq_ker_nhds, nhds_prod_eq, ker_prod]

lemma nhdsKer_prod {Y : Type*} [TopologicalSpace Y] (s : Set X) (t : Set Y) :
    nhdsKer (s ×ˢ t) = nhdsKer s ×ˢ nhdsKer t := calc
  _ = ⋃ (p ∈ s ×ˢ t), nhdsKer {p} := by
    conv_lhs => rw [← biUnion_of_singleton (s ×ˢ t), nhdsKer_biUnion]
  _ = ⋃ (p ∈ s ×ˢ t), nhdsKer {p.1} ×ˢ nhdsKer {p.2} := by
    congr! with ⟨x, y⟩ _; rw [nhdsKer_pair]
  _ = (⋃ x ∈ s, nhdsKer {x}) ×ˢ (⋃ y ∈ t, nhdsKer {y}) :=
    biUnion_prod s t (fun x => nhdsKer {x}) (fun y => nhdsKer {y})
  _ = nhdsKer s ×ˢ nhdsKer t := by
    simp_rw [← nhdsKer_biUnion, biUnion_of_singleton]

lemma nhdsKer_singleton_pi {ι : Type*} {X : ι → Type*} [Π (i : ι), TopologicalSpace (X i)]
    (p : Π (i : ι), X i) : nhdsKer {p} = univ.pi (fun i => nhdsKer {p i}) := by
  simp_rw [nhdsKer_singleton_eq_ker_nhds, nhds_pi, ker_pi]

lemma nhdsKer_pi {ι : Type*} {X : ι → Type*} [Π (i : ι), TopologicalSpace (X i)]
    (s : Π (i : ι), Set (X i)) : nhdsKer (univ.pi s) = univ.pi (fun i => nhdsKer (s i)) := calc
  _ = ⋃ (p ∈ univ.pi s), nhdsKer {p} := by
    conv_lhs => rw [← biUnion_of_singleton (univ.pi s), nhdsKer_biUnion]
  _ = ⋃ (p ∈ univ.pi s), univ.pi fun i => nhdsKer {p i} := by
    congr! with p _; rw [nhdsKer_singleton_pi]
  _ = univ.pi fun i => ⋃ x ∈ s i, nhdsKer {x} :=
    biUnion_univ_pi s fun i x => nhdsKer {x}
  _ = univ.pi (fun i => nhdsKer (s i)) := by
    simp_rw [← nhdsKer_biUnion, biUnion_of_singleton]
