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

variable {G : Type*} [TopologicalSpace G] [Group G] [NonarchimedeanGroup G] [T2Space G]

namespace NonarchimedeanGroup.auxiliary

@[to_additive]
lemma exists_openSubgroup_separating {t : G} (ht : t ≠ 1) :
    ∃ (A : Opens G) (V : OpenSubgroup G), t ∈ A ∧ 1 ∈ V ∧ Disjoint (A : Set G) V := by
  rcases (t2_separation ht) with ⟨A, B, opena, openb, diff, one, disj⟩
  obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean B (IsOpen.mem_nhds openb one)
  exact ⟨⟨A, opena⟩, V, diff, one_mem V,
    fun _ ↦ by apply Set.disjoint_of_subset_right hV disj⟩

end NonarchimedeanGroup.auxiliary

namespace NonarchimedeanGroup
open NonarchimedeanGroup.auxiliary

@[to_additive]
instance instTotallySeparated : TotallySeparatedSpace G where
  isTotallySeparated_univ x _ y _ hxy := by
    rcases exists_openSubgroup_separating (hxy ∘ inv_mul_eq_one.mp) with ⟨A, V, hA, -, hAV⟩
    refine ⟨_, _, V.isOpen.smul x, (V.isClosed.smul x).isOpen_compl, mem_own_leftCoset ..,
        ?_, (Set.union_compl_self _).ge, Set.disjoint_compl_right_iff_subset.mpr (le_refl _)⟩
    rw [Set.mem_compl_iff, mem_leftCoset_iff]
    exact Set.disjoint_left.mp hAV hA

end NonarchimedeanGroup
