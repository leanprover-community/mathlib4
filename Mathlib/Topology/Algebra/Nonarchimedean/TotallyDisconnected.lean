/-
Copyright (c) 2024 Jou Glasheen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jou Glasheen, Kevin Buzzard
-/

import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# Total disconnectedness of nonarchimedean groups

In this file, we prove that a nonarchimedean group is a totally disconnected topological space.

## Main results

- `NonarchimedeanGroup.instTotallyDisconnectedSpace`: A nonarchimedean group is a
                                                      totally disconnected topological space.

## Notation

 - `G` : Is a nonarchimedean group.
 - `V` : Is an open subgroup which is a neighbourhood of the identity in `G`.

## References

See Proposition 2.3.9 and Problem 63 in :
Gouvêa, F. Q. (2020) p-adic Numbers An Introduction. 3rd edition.
  Cham, Springer International Publishing.
-/

open Pointwise TopologicalSpace

namespace NonarchimedeanGroup.auxiliary

variable {G : Type*} [TopologicalSpace G] [Group G] [NonarchimedeanGroup G] [T2Space G]

variable {t : G} in
@[to_additive]
lemma open_subgroup_separating
    (ht : t ≠ 1) : ∃ (A : Opens G) (V : OpenSubgroup G),
    t ∈ A ∧ 1 ∈ V ∧ Disjoint (A : Set G) V := by
  rcases (t2_separation ht) with ⟨A, B, opena, openb, diff, one, disj⟩
  obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean B (IsOpen.mem_nhds openb one)
  exact ⟨⟨A, opena⟩, V, diff, one_mem V,
    fun _ ↦ by apply Set.disjoint_of_subset_right hV disj⟩

end NonarchimedeanGroup.auxiliary

namespace TopologicalGroup
variable {G : Type*} [TopologicalSpace G] [Group G]

variable {x y : G} {U : Set G} {A : Opens G} in
@[to_additive]
lemma non_empty_intersection_compl_coset (hx : x ∈ U)
    (quot : (y⁻¹ * x) ∈ A ) (V : OpenSubgroup G) (dva : Disjoint (V : Set G) A) :
    (U ∩ ((y • (V : Set G))ᶜ)).Nonempty := by
  simp_rw [Set.inter_nonempty, Set.mem_compl_iff]
  use x, hx
  intro con
  rw [mem_leftCoset_iff y] at con
  have mem : (y⁻¹ * x) ∈ (V : Set G) ∩ A := Set.mem_inter con quot
  have subempty : (V : Set G) ∩ A = ∅ := Disjoint.inter_eq dva
  rw [subempty] at mem
  simp at mem

variable {y : G} {U : Set G} in
@[to_additive]
lemma non_empty_intersection_coset (hy :  y ∈ U)
    (V : OpenSubgroup G) : (U ∩ (y • (V : Set G))).Nonempty := by
  simp only [Set.inter_nonempty]
  use y
  refine ⟨hy, ?_⟩
  simp only [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, inv_mul_cancel, SetLike.mem_coe,
    one_mem V]

end TopologicalGroup

namespace NonarchimedeanGroup
open NonarchimedeanGroup.auxiliary TopologicalGroup

variable {G : Type*} [TopologicalSpace G] [Group G]
  [TopologicalGroup G] [NonarchimedeanGroup G] [T2Space G]

variable {x y : G} {U : Set G} in
/-- In a nonarchimedean group, any set which contains two distinct points is disconnected. -/
@[to_additive]
theorem non_singleton_set_disconnected
    (hx : x ∈ U) (hy :  y ∈ U) (hxy : y ≠ x) : ¬ IsConnected U := by
  obtain ⟨A , V, ha, _ , dav⟩ : ∃ (A : Opens G) (V : OpenSubgroup G), y⁻¹ * x ∈ A ∧ 1 ∈ V ∧
          Disjoint (A : Set G) V := by
    have ht : y⁻¹ * x ≠ 1 := by
        by_contra! con
        rw [← inv_mul_cancel y] at con
        apply mul_left_cancel at con
        exact hxy (id (Eq.symm con))
    exact open_subgroup_separating ht
  obtain ⟨u , v, ou, ov, Uuv, Uu, Uv, emptyUuv⟩ : ∃ u v : Set G, (IsOpen u) ∧ (IsOpen v) ∧
      (U ⊆ u ∪ v) ∧ ((U ∩ u).Nonempty) ∧ ((U ∩ v).Nonempty) ∧ (¬(U ∩ (u ∩ v)).Nonempty) := by
    use (y • (V : Set G)) , (y • (V : Set G))ᶜ
    simp_rw [(IsOpen.smul (OpenSubgroup.isOpen V) y), isOpen_compl_iff,
        IsClosed.smul (OpenSubgroup.isClosed V) y,
        Set.union_compl_self, Set.subset_univ,
        non_empty_intersection_coset hy V,
        non_empty_intersection_compl_coset hx ha V dav.symm,
        Set.inter_compl_self, Set.inter_empty, Set.not_nonempty_empty, not_false_eq_true,
        and_self]
  rintro ⟨_, h2⟩
  exact emptyUuv <| ((((h2 u v ou) ov) Uuv) Uu) Uv

/-- A nonarchimedean group is a totally disconnected topological space. -/
@[to_additive]
instance : TotallyDisconnectedSpace G := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_singleton]
  intro x
  by_contra con
  obtain ⟨y, hyu, hneq⟩ : ∃ y : G, (y ∈ connectedComponent x) ∧ (y ≠ x) := by
    by_contra! con2
    exact con <| (Set.Nonempty.subset_singleton_iff ⟨x, mem_connectedComponent⟩).mp con2
  exact non_singleton_set_disconnected mem_connectedComponent hyu
    hneq isConnected_connectedComponent

end NonarchimedeanGroup
