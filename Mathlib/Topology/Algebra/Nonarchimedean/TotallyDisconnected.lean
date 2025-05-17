/-
Copyright (c) 2024 Jou Glasheen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jou Glasheen, Kevin Buzzard, David Loeffler, Yongle Hu, Johan Commelin
-/

import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# Total separatedness of nonarchimedean groups

In this file, we prove that a nonarchimedean group is a totally separated topological space.
The fact that a nonarchimedean group is a totally disconnected topological space
is implied by the fact that a nonarchimedean group is totally separated.

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

namespace NonarchimedeanGroup

@[to_additive]
lemma exists_openSubgroup_separating {a b : G} (h : a ≠ b) :
    ∃ V : OpenSubgroup G, Disjoint (a • (V : Set G)) (b • V) := by
  obtain ⟨u, v, _, open_v, mem_u, mem_v, dis⟩ := t2_separation (h ∘ inv_mul_eq_one.mp)
  obtain ⟨V, hV⟩ := is_nonarchimedean v (open_v.mem_nhds mem_v)
  use V
  simp only [Disjoint, Set.le_eq_subset, Set.bot_eq_empty, Set.subset_empty_iff]
  intros x mem_aV mem_bV
  by_contra! con
  obtain ⟨s, hs⟩ := con
  have hsa : s ∈ a • (V : Set G) := mem_aV hs
  have hsb : s ∈ b • (V : Set G) := mem_bV hs
  rw [mem_leftCoset_iff] at hsa hsb
  refine dis.subset_compl_right mem_u (hV ?_)
  simpa [mul_assoc] using mul_mem hsa (inv_mem hsb)

@[to_additive]
instance (priority := 100) instTotallySeparated : TotallySeparatedSpace G where
  isTotallySeparated_univ x _ y _ hxy := by
    obtain ⟨V, dxy⟩ := exists_openSubgroup_separating hxy
    exact ⟨_, _, V.isOpen.smul x, (V.isClosed.smul x).isOpen_compl, mem_own_leftCoset ..,
      dxy.subset_compl_left <| mem_own_leftCoset .., by simp, disjoint_compl_right⟩

end NonarchimedeanGroup
