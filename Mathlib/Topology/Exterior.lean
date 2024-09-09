/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Topology.NhdsSet
import Mathlib.Topology.Inseparable

/-!
# Exterior of a set

We define `exterior s` to be the intersection of all neighborhoods of `s`,
see `Topology/Defs/Filter`.
Note that this construction has no standard name in the literature.

In this file we prove basic properties of this operation.
-/

open Set Filter
open scoped Topology

variable {X : Type*} [TopologicalSpace X] {s t : Set X} {x y : X}

lemma exterior_singleton_eq_ker_nhds (x : X) : exterior {x} = (𝓝 x).ker := by simp [exterior]

theorem mem_exterior_iff_specializes : x ∈ exterior s ↔ ∃ y ∈ s, x ⤳ y := by
  constructor
  · i

lemma mem_exterior_singleton_iff_specializes : x ∈ exterior {y} ↔ x ⤳ y := by
  rw [exterior_singleton_eq_ker_nhds, mem_ker, specializes_iff_pure, pure_le_iff]

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

lemma IsOpen.exterior_subset_iff (ht : IsOpen t) : exterior s ⊆ t ↔ s ⊆ t :=
  ⟨subset_exterior.trans, fun h ↦ exterior_minimal h ht⟩

@[mono] lemma exterior_mono : Monotone (exterior : Set X → Set X) :=
  fun _s _t h ↦ ker_mono <| nhdsSet_mono h

@[simp] lemma exterior_empty : exterior (∅ : Set X) = ∅ := isOpen_empty.exterior_eq
@[simp] lemma exterior_univ : exterior (univ : Set X) = univ := isOpen_univ.exterior_eq

@[simp] lemma exterior_eq_empty : exterior s = ∅ ↔ s = ∅ :=
  ⟨eq_bot_mono subset_exterior, by rintro rfl; exact exterior_empty⟩

-- TODO: duplicate of `IsOpen.exterior_subset_iff`
lemma IsOpen.exterior_subset (ht : IsOpen t) : exterior s ⊆ t ↔ s ⊆ t :=
  ⟨subset_exterior.trans, fun h ↦ exterior_minimal h ht⟩

lemma specializes_iff_exterior_subset : x ⤳ y ↔ exterior {x} ⊆ exterior {y} := by
  simp only [subset_def, mem_exterior_singleton_iff_specializes]
  exact ⟨fun h₁ z h₂ ↦ h₂.trans h₁, fun h ↦ h _ le_rfl⟩
