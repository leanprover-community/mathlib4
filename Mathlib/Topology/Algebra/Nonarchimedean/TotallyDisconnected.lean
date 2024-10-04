/-
Copyright (c) 2024 Jou Glasheen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jou Glasheen, Kevin Buzzard, David Loeffler, Yongle Hu
-/

import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# Total separatedness of nonarchimedean groups

In this file, we prove that a nonarchimedean group is a totally separated topological space.

## Main results

- `NonarchimedeanGroup.instTotallySeparated`:
  A nonarchimedean group is a totally separated topological space.

## Notation

 - `G` : Is a nonarchimedean group.
 - `V` : Is an open subgroup which is a neighbourhood of the identity in `G`.

## References

See Proposition 2.3.9 and Problem 63 in [F. Q. Gouvêa, *p-adic numbers*][gouvea1997].
-/

open Pointwise TopologicalSpace

variable {G : Type*} [TopologicalSpace G] [Group G] [NonarchimedeanGroup G] [T2Space G]

namespace NonarchimedeanGroup.auxiliary

@[to_additive]
lemma exists_openSubgroup_separating {t : G} (ht : t ≠ 1) :
    ∃ (A : Opens G) (V : OpenSubgroup G), t ∈ A ∧ 1 ∈ V ∧ Disjoint (A : Set G) V := by
  rcases t2_separation ht with ⟨A, B, open_A, open_B, mem_A, mem_B, disj⟩
  obtain ⟨V, hV⟩ := is_nonarchimedean B (open_B.mem_nhds mem_B)
  exact ⟨⟨A, open_A⟩, V, mem_A, one_mem V, disj.mono_right hV⟩

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
