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
it is invariant by translation and admits a basis of neighborhoods of 0 consisting of
two-sided ideals.

- `IsLinearTopology.tendsto_mul_zero_of_left`: for `f, g : ι → R` such that `f i` converges to `0`,
`f i * g i` converges to `0`.

- `IsLinearTopology.tendsto_mul_zero_of_right`: for `f, g : ι → R` such that `g i` converges to `0`,
`f i * g i` converges to `0`.

## Instances

- A discrete topology is a linear topology

- If `α` has a linear topology, then the set of twosided ideals of `α` that are
neighborhoods of 0 is nonempty

-/

open scoped Topology
open Filter

section Ring

variable (α : Type*) [Ring α]

/-- A topology on a ring is linear if its topology is defined by a family of ideals. -/
class IsLinearTopology [TopologicalSpace α] [TopologicalRing α] where
  hasBasis_twoSidedIdeal : (𝓝 (0 : α)).HasBasis
    (fun I : TwoSidedIdeal α ↦ (I : Set α) ∈ 𝓝 0) (fun I : TwoSidedIdeal α ↦ (I : Set α))

variable {α} [TopologicalSpace α] [TopologicalRing α]

lemma IsLinearTopology.hasBasis_open_twoSidedIdeal [IsLinearTopology α] :
    (𝓝 (0 : α)).HasBasis
      (fun I : TwoSidedIdeal α ↦ IsOpen (I : Set α)) (fun I : TwoSidedIdeal α ↦ (I : Set α)) :=
  IsLinearTopology.hasBasis_twoSidedIdeal.congr
    (fun I ↦ ⟨I.asIdeal.toAddSubgroup.isOpen_of_mem_nhds, fun hI ↦ hI.mem_nhds (zero_mem I)⟩)
    (fun _ _ ↦ rfl)

theorem IsLinearTopology.hasBasis_ideal [IsLinearTopology α] :
    (𝓝 0).HasBasis (fun I : Ideal α ↦ (I : Set α) ∈ 𝓝 0) (fun I : Ideal α ↦ (I : Set α)) :=
  IsLinearTopology.hasBasis_twoSidedIdeal.to_hasBasis
    (fun I hI ↦ ⟨I.asIdeal, hI, subset_rfl⟩)
    (fun _ ↦ IsLinearTopology.hasBasis_twoSidedIdeal.mem_iff.mp)

theorem IsLinearTopology.hasBasis_open_ideal [IsLinearTopology α] :
    (𝓝 0).HasBasis (fun I : Ideal α ↦ IsOpen (I : Set α)) (fun I : Ideal α ↦ (I : Set α)) :=
  IsLinearTopology.hasBasis_ideal.congr
    (fun I ↦ ⟨I.toAddSubgroup.isOpen_of_mem_nhds, fun hI ↦ hI.mem_nhds (zero_mem I)⟩)
    (fun _ _ ↦ rfl)

lemma IsLinearTopology.mk_of_twoSidedIdeal {ι : Sort*} {p : ι → Prop} {s : ι → TwoSidedIdeal α}
    (h : (𝓝 0).HasBasis p (fun i ↦ (s i : Set α))) :
    IsLinearTopology α where
  hasBasis_twoSidedIdeal := h.to_hasBasis (fun i hi ↦ ⟨s i, h.mem_of_mem hi, subset_rfl⟩)
    (fun _ ↦ h.mem_iff.mp)

theorem isLinearTopology_iff_hasBasis_twoSidedIdeal :
    IsLinearTopology α ↔ (𝓝 0).HasBasis
      (fun I : TwoSidedIdeal α ↦ (I : Set α) ∈ 𝓝 0) (fun I : TwoSidedIdeal α ↦ (I : Set α)) :=
  ⟨fun _ ↦ IsLinearTopology.hasBasis_twoSidedIdeal, fun h ↦ .mk_of_twoSidedIdeal h⟩

theorem isLinearTopology_iff_hasBasis_open_twoSidedIdeal :
    IsLinearTopology α ↔ (𝓝 0).HasBasis
      (fun I : TwoSidedIdeal α ↦ IsOpen (I : Set α)) (fun I : TwoSidedIdeal α ↦ (I : Set α)) :=
  ⟨fun _ ↦ IsLinearTopology.hasBasis_open_twoSidedIdeal, fun h ↦ .mk_of_twoSidedIdeal h⟩

instance [IsLinearTopology α] : Nonempty { J : TwoSidedIdeal α | (J : Set α) ∈ 𝓝 0} := by
  obtain ⟨J, hJ, _⟩ :=
    ((IsLinearTopology.hasBasis_twoSidedIdeal (α := α)).mem_iff' Set.univ).mp (Filter.univ_mem)
  exact ⟨J, hJ⟩

instance [DiscreteTopology α] : IsLinearTopology α := by
 rw [isLinearTopology_iff_hasBasis_twoSidedIdeal]
 apply HasBasis.mk
 intro t
 simp only [mem_nhds_discrete, SetLike.mem_coe, TwoSidedIdeal.zero_mem, true_and]
 constructor
 · intro ht
   use ⊥
   change {0} ⊆ t
   simp only [Set.singleton_subset_iff, ht]
 · rintro ⟨J, hJt⟩
   exact hJt J.zero_mem

theorem IsLinearTopology.tendsto_mul_zero_of_left [IsLinearTopology α] {ι : Type*} {f : Filter ι}
    (a b : ι → α) (ha : Tendsto a f (𝓝 0)) :
    Tendsto (a * b) f (𝓝 0) := by
  rw [IsLinearTopology.hasBasis_twoSidedIdeal.tendsto_right_iff] at ha ⊢
  intro I hI
  filter_upwards [ha I hI] with i ai_mem
  exact I.mul_mem_right _ _ ai_mem

theorem IsLinearTopology.tendsto_mul_zero_of_right [IsLinearTopology α] {ι : Type*} {f : Filter ι}
    (a b : ι → α) (hb : Tendsto b f (𝓝 0)) :
    Tendsto (a * b) f (𝓝 0) := by
  rw [IsLinearTopology.hasBasis_twoSidedIdeal.tendsto_right_iff] at hb ⊢
  intro I hI
  filter_upwards [hb I hI] with i bi_mem
  exact I.mul_mem_left _ _ bi_mem

end Ring

section CommRing

variable {α} [CommRing α] [TopologicalSpace α] [TopologicalRing α]

lemma IsLinearTopology.mk_of_ideal {ι : Sort*} {p : ι → Prop} {s : ι → Ideal α}
    (h : (𝓝 0).HasBasis p (fun i ↦ (s i : Set α))) :
    IsLinearTopology α where
  hasBasis_twoSidedIdeal := h.to_hasBasis
    (fun i hi ↦ ⟨(s i).toTwoSided ((s i).mul_mem_right _), by simpa using h.mem_of_mem hi, by simp⟩)
    (fun _ ↦ h.mem_iff.mp)

theorem isLinearTopology_iff_hasBasis_ideal :
    IsLinearTopology α ↔ (𝓝 0).HasBasis
      (fun I : Ideal α ↦ (I : Set α) ∈ 𝓝 0) (fun I : Ideal α ↦ (I : Set α)) :=
  ⟨fun _ ↦ IsLinearTopology.hasBasis_ideal, fun h ↦ .mk_of_ideal h⟩

theorem isLinearTopology_iff_hasBasis_open_ideal :
    IsLinearTopology α ↔ (𝓝 0).HasBasis
      (fun I : Ideal α ↦ IsOpen (I : Set α)) (fun I : Ideal α ↦ (I : Set α)) :=
  ⟨fun _ ↦ IsLinearTopology.hasBasis_open_ideal, fun h ↦ .mk_of_ideal h⟩

end CommRing
