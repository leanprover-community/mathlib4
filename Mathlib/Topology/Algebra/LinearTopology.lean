/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández, Anatole Dedecker
-/

import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Linear topologies on rings

Following Bourbaki, *Algebra II*, chapter 4, §2, n° 3, a topology on a ring `R` is *linear* if
it is invariant by translation and there admits a basis of neighborhoods of 0 consisting of
two-sided ideals.

- `LinearTopology.tendsto_zero_mul`: for `f, g : ι → R` such that `f i` converges to `0`,
`f i * g i` converges to `0`.

-/

open scoped Topology
open Filter

section Ring

variable (α : Type*) [Ring α]

/-- A topology on a ring is linear if its topology is defined by a family of ideals. -/
class LinearTopology [TopologicalSpace α] [TopologicalRing α] where
  hasBasis_twoSidedIdeal : (𝓝 (0 : α)).HasBasis
    (fun I : TwoSidedIdeal α ↦ (I : Set α) ∈ 𝓝 0) (fun I : TwoSidedIdeal α ↦ (I : Set α))

variable {α} [TopologicalSpace α] [TopologicalRing α]

lemma LinearTopology.hasBasis_open_twoSidedIdeal [LinearTopology α] :
    (𝓝 (0 : α)).HasBasis
      (fun I : TwoSidedIdeal α ↦ IsOpen (I : Set α)) (fun I : TwoSidedIdeal α ↦ (I : Set α)) :=
  LinearTopology.hasBasis_twoSidedIdeal.congr
    (fun I ↦ ⟨I.asIdeal.toAddSubgroup.isOpen_of_mem_nhds, fun hI ↦ hI.mem_nhds (zero_mem I)⟩)
    (fun _ _ ↦ rfl)

theorem LinearTopology.hasBasis_ideal [LinearTopology α] :
    (𝓝 0).HasBasis (fun I : Ideal α ↦ (I : Set α) ∈ 𝓝 0) (fun I : Ideal α ↦ (I : Set α)) :=
  LinearTopology.hasBasis_twoSidedIdeal.to_hasBasis
    (fun I hI ↦ ⟨I.asIdeal, hI, subset_rfl⟩)
    (fun _ ↦ LinearTopology.hasBasis_twoSidedIdeal.mem_iff.mp)

theorem LinearTopology.hasBasis_open_ideal [LinearTopology α] :
    (𝓝 0).HasBasis (fun I : Ideal α ↦ IsOpen (I : Set α)) (fun I : Ideal α ↦ (I : Set α)) :=
  LinearTopology.hasBasis_ideal.congr
    (fun I ↦ ⟨I.toAddSubgroup.isOpen_of_mem_nhds, fun hI ↦ hI.mem_nhds (zero_mem I)⟩)
    (fun _ _ ↦ rfl)

lemma LinearTopology.mk_of_twoSidedIdeal {ι : Sort*} {p : ι → Prop} {s : ι → TwoSidedIdeal α}
    (h : (𝓝 0).HasBasis p (fun i ↦ (s i : Set α))) :
    LinearTopology α where
  hasBasis_twoSidedIdeal := h.to_hasBasis (fun i hi ↦ ⟨s i, h.mem_of_mem hi, subset_rfl⟩)
    (fun _ ↦ h.mem_iff.mp)

theorem linearTopology_iff_hasBasis_twoSidedIdeal :
    LinearTopology α ↔ (𝓝 0).HasBasis
      (fun I : TwoSidedIdeal α ↦ (I : Set α) ∈ 𝓝 0) (fun I : TwoSidedIdeal α ↦ (I : Set α)) :=
  ⟨fun _ ↦ LinearTopology.hasBasis_twoSidedIdeal, fun h ↦ .mk_of_twoSidedIdeal h⟩

theorem linearTopology_iff_hasBasis_open_twoSidedIdeal :
    LinearTopology α ↔ (𝓝 0).HasBasis
      (fun I : TwoSidedIdeal α ↦ IsOpen (I : Set α)) (fun I : TwoSidedIdeal α ↦ (I : Set α)) :=
  ⟨fun _ ↦ LinearTopology.hasBasis_open_twoSidedIdeal, fun h ↦ .mk_of_twoSidedIdeal h⟩

theorem LinearTopology.tendsto_mul_zero_of_left [LinearTopology α] {ι : Type*} {f : Filter ι}
    (a b : ι → α) (ha : Tendsto a f (𝓝 0)) :
    Tendsto (a * b) f (𝓝 0) := by
  rw [LinearTopology.hasBasis_twoSidedIdeal.tendsto_right_iff] at ha ⊢
  intro I hI
  filter_upwards [ha I hI] with i ai_mem
  exact I.mul_mem_right _ _ ai_mem

theorem LinearTopology.tendsto_mul_zero_of_right_[LinearTopology α] {ι : Type*} {f : Filter ι}
    (a b : ι → α) (hb : Tendsto b f (𝓝 0)) :
    Tendsto (a * b) f (𝓝 0) := by
  rw [LinearTopology.hasBasis_twoSidedIdeal.tendsto_right_iff] at hb ⊢
  intro I hI
  filter_upwards [hb I hI] with i bi_mem
  exact I.mul_mem_left _ _ bi_mem

end Ring

section CommRing

variable {α} [CommRing α] [TopologicalSpace α] [TopologicalRing α]

lemma LinearTopology.mk_of_ideal {ι : Sort*} {p : ι → Prop} {s : ι → Ideal α}
    (h : (𝓝 0).HasBasis p (fun i ↦ (s i : Set α))) :
    LinearTopology α where
  hasBasis_twoSidedIdeal := h.to_hasBasis
    (fun i hi ↦ ⟨(s i).toTwoSided ((s i).mul_mem_right _), by simpa using h.mem_of_mem hi, by simp⟩)
    (fun _ ↦ h.mem_iff.mp)

theorem linearTopology_iff_hasBasis_ideal :
    LinearTopology α ↔ (𝓝 0).HasBasis
      (fun I : Ideal α ↦ (I : Set α) ∈ 𝓝 0) (fun I : Ideal α ↦ (I : Set α)) :=
  ⟨fun _ ↦ LinearTopology.hasBasis_ideal, fun h ↦ .mk_of_ideal h⟩

theorem linearTopology_iff_hasBasis_open_ideal :
    LinearTopology α ↔ (𝓝 0).HasBasis
      (fun I : Ideal α ↦ IsOpen (I : Set α)) (fun I : Ideal α ↦ (I : Set α)) :=
  ⟨fun _ ↦ LinearTopology.hasBasis_open_ideal, fun h ↦ .mk_of_ideal h⟩

end CommRing

#exit
variable {α : Type*} [CommRing α] [TopologicalSpace α] [TopologicalRing α] [LinearTopology α]

theorem mem_nhds_zero_iff (s : Set α) :
    (s ∈ nhds 0) ↔
    (∃ I : Ideal α, ((I : Set α) ∈ nhds 0) ∧ (I : Set α) ⊆ s) := by
  rw [isLinearTopology.mem_iff]
  apply exists_congr
  intro I
  apply and_congr_left
  intro hI
  rw [isOpen_iff_nhds]
  constructor
  · exact fun hI' ↦ hI' 0 I.zero_mem fun ⦃_⦄ a ↦ a
  · intro hI' x hx s hs
    rw [Filter.mem_principal] at hs
    rw [← vadd_mem_nhds_vadd_iff (-x)]
    simp only [vadd_eq_add, neg_add_cancel]
    apply Filter.mem_of_superset hI'
    intro y hy
    rw [Set.mem_neg_vadd_set_iff]
    exact hs (add_mem hx hy)

theorem tendsto_zero_mul {ι : Type*} {f : Filter ι}
    (a b : ι → α) (hb : Filter.Tendsto b f (nhds 0)) :
    Filter.Tendsto (a * b) f (nhds 0) := by
  intro v hv
  obtain ⟨I, I_mem, I_le⟩ := (LinearTopology.mem_nhds_zero_iff _).mp hv
  apply Filter.sets_of_superset _ _ I_le
  simp only [Filter.mem_sets, Filter.mem_map]
  rw [Filter.tendsto_def] at hb
  exact Filter.sets_of_superset _ (hb _ I_mem) (fun x hx ↦ Ideal.mul_mem_left _ _ hx)

end LinearTopology
