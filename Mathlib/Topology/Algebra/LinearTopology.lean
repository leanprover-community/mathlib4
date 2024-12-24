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

- `tendsto_mul_zero_of_left`: for `f, g : ι → R` such that `f i` converges to `0`,
`f i * g i` converges to `0`.

- `tendsto_mul_zero_of_right`: for `f, g : ι → R` such that `g i` converges to `0`,
`f i * g i` converges to `0`.

## Instances

- A discrete topology is a linear topology

## Note on the implementation

The definition of Bourbaki doesn't presuppose, but implies, that a linear topology on a ring `R` is
a ring topology. However, in some of our lemmas, we already assume that `R` is a topological ring.
This unnecessary assumption will be made unnecessary by results in the ongoing PR #18437.
Anyway, the idea will be to first define a topology on `R`, and then
prove that it makes `R` a topological ring, and that it is a linear topology.

-/

open scoped Topology
open Filter

namespace IsLinearTopology

section Ring

/-- A topology on a ring is linear if its topology is defined by a family of ideals. -/
class _root_.IsLinearTopology (R : Type*) [Ring R] [TopologicalSpace R] where
  hasBasis_twoSidedIdeal : (𝓝 (0 : R)).HasBasis
    (fun I : TwoSidedIdeal R ↦ (I : Set R) ∈ 𝓝 0) (fun I : TwoSidedIdeal R ↦ (I : Set R))

variable {R : Type*} [Ring R] [TopologicalSpace R]

lemma hasBasis_open_twoSidedIdeal [TopologicalRing R] [IsLinearTopology R] :
    (𝓝 (0 : R)).HasBasis
      (fun I : TwoSidedIdeal R ↦ IsOpen (I : Set R)) (fun I : TwoSidedIdeal R ↦ (I : Set R)) :=
  hasBasis_twoSidedIdeal.congr
    (fun I ↦ ⟨I.asIdeal.toAddSubgroup.isOpen_of_mem_nhds, fun hI ↦ hI.mem_nhds (zero_mem I)⟩)
    (fun _ _ ↦ rfl)

theorem hasBasis_ideal [IsLinearTopology R] :
    (𝓝 0).HasBasis (fun I : Ideal R ↦ (I : Set R) ∈ 𝓝 0) (fun I : Ideal R ↦ (I : Set R)) :=
  hasBasis_twoSidedIdeal.to_hasBasis
    (fun I hI ↦ ⟨I.asIdeal, hI, subset_rfl⟩)
    (fun _ ↦ hasBasis_twoSidedIdeal.mem_iff.mp)

theorem hasBasis_open_ideal [TopologicalRing R] [IsLinearTopology R] :
    (𝓝 0).HasBasis (fun I : Ideal R ↦ IsOpen (I : Set R)) (fun I : Ideal R ↦ (I : Set R)) :=
  hasBasis_ideal.congr
    (fun I ↦ ⟨I.toAddSubgroup.isOpen_of_mem_nhds, fun hI ↦ hI.mem_nhds (zero_mem I)⟩)
    (fun _ _ ↦ rfl)

lemma mk_of_twoSidedIdeal {ι : Sort*} {p : ι → Prop} {s : ι → TwoSidedIdeal R}
    (h : (𝓝 0).HasBasis p (fun i ↦ (s i : Set R))) :
    IsLinearTopology R where
  hasBasis_twoSidedIdeal := h.to_hasBasis (fun i hi ↦ ⟨s i, h.mem_of_mem hi, subset_rfl⟩)
    (fun _ ↦ h.mem_iff.mp)

theorem _root_.isLinearTopology_iff_hasBasis_twoSidedIdeal :
    IsLinearTopology R ↔ (𝓝 0).HasBasis
      (fun I : TwoSidedIdeal R ↦ (I : Set R) ∈ 𝓝 0) (fun I : TwoSidedIdeal R ↦ (I : Set R)) :=
  ⟨fun _ ↦ hasBasis_twoSidedIdeal, fun h ↦ .mk_of_twoSidedIdeal h⟩

theorem _root_.isLinearTopology_iff_hasBasis_open_twoSidedIdeal [TopologicalRing R] :
    IsLinearTopology R ↔ (𝓝 0).HasBasis
      (fun I : TwoSidedIdeal R ↦ IsOpen (I : Set R)) (fun I : TwoSidedIdeal R ↦ (I : Set R)) :=
  ⟨fun _ ↦ hasBasis_open_twoSidedIdeal, fun h ↦ .mk_of_twoSidedIdeal h⟩

instance [DiscreteTopology R] : IsLinearTopology R :=
  have : HasBasis (𝓝 0 : Filter R) (fun _ ↦ True) (fun (_ : Unit) ↦ (⊥ : TwoSidedIdeal R)) := by
    rw [nhds_discrete]
    exact hasBasis_pure _
  mk_of_twoSidedIdeal this

theorem tendsto_mul_zero_of_left [IsLinearTopology R] {ι : Type*} {f : Filter ι}
    (a b : ι → R) (ha : Tendsto a f (𝓝 0)) :
    Tendsto (a * b) f (𝓝 0) := by
  rw [hasBasis_twoSidedIdeal.tendsto_right_iff] at ha ⊢
  intro I hI
  filter_upwards [ha I hI] with i ai_mem
  exact I.mul_mem_right _ _ ai_mem

theorem tendsto_mul_zero_of_right [IsLinearTopology R] {ι : Type*} {f : Filter ι}
    (a b : ι → R) (hb : Tendsto b f (𝓝 0)) :
    Tendsto (a * b) f (𝓝 0) := by
  rw [hasBasis_twoSidedIdeal.tendsto_right_iff] at hb ⊢
  intro I hI
  filter_upwards [hb I hI] with i bi_mem
  exact I.mul_mem_left _ _ bi_mem

end Ring

section CommRing

variable {R : Type*} [CommRing R] [TopologicalSpace R]

lemma mk_of_ideal {ι : Sort*} {p : ι → Prop} {s : ι → Ideal R}
    (h : (𝓝 0).HasBasis p (fun i ↦ (s i : Set R))) :
    IsLinearTopology R where
  hasBasis_twoSidedIdeal := h.to_hasBasis
    (fun i hi ↦ ⟨(s i).toTwoSided ((s i).mul_mem_right _), by simpa using h.mem_of_mem hi, by simp⟩)
    (fun _ ↦ h.mem_iff.mp)

theorem _root_.isLinearTopology_iff_hasBasis_ideal :
    IsLinearTopology R ↔ (𝓝 0).HasBasis
      (fun I : Ideal R ↦ (I : Set R) ∈ 𝓝 0) (fun I : Ideal R ↦ (I : Set R)) :=
  ⟨fun _ ↦ hasBasis_ideal, fun h ↦ .mk_of_ideal h⟩

theorem _root_.isLinearTopology_iff_hasBasis_open_ideal [TopologicalRing R] :
    IsLinearTopology R ↔ (𝓝 0).HasBasis
      (fun I : Ideal R ↦ IsOpen (I : Set R)) (fun I : Ideal R ↦ (I : Set R)) :=
  ⟨fun _ ↦ hasBasis_open_ideal, fun h ↦ .mk_of_ideal h⟩

end CommRing

end IsLinearTopology
