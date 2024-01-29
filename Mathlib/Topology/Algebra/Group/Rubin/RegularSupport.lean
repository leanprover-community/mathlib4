/-
Copyright (c) 2024 Emilie Burgun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emilie Burgun
-/

import Mathlib.Topology.Separation
import Mathlib.Topology.Algebra.Group.LocallyDense
import Mathlib.GroupTheory.GroupAction.FixedPoints
import Mathlib.Topology.RegularOpen

/-!
# Regular supports in Rubin's theorem

This module defines the notion of a regular support in the proof of Rubin's theorem.
The regular support of a group element `g` is the `interior` of the `closure` of the set
`(fixedBy α g)ᶜ`.

## References

* [J. Belk, L. Elliott, F. Matucci, *A short proof of Rubin's theorem*][belk2023short]
-/

namespace Rubin

open Topology
open TopologicalSpace (RegularOpens)
open MulAction
open Pointwise

variable {G : Type*} (α : Type*) [Group G] [MulAction G α] [TopologicalSpace α]

/--
The regular support of a group element `g` on the topology `α` that the group is acting on is
the interior of the closure of the set of points moved by `g`.
-/
def RegularSupport (g : G) : RegularOpens α := RegularOpens.fromSet (fixedBy α g)ᶜ

lemma regularSupport_def (g : G) : RegularSupport α g = RegularOpens.fromSet (fixedBy α g)ᶜ := rfl

namespace RegularSupport

theorem subset_closure_fixedBy_compl (g : G) :
    (RegularSupport α g : Set α) ⊆ closure (fixedBy α g)ᶜ := interior_subset

variable [T2Space α] [ContinuousConstSMul G α]

theorem fixedBy_compl_subset (g : G) : (fixedBy α g)ᶜ ⊆ RegularSupport α g :=
  RegularOpens.subset_fromSet_of_isOpen (isClosed_fixedBy α g).isOpen_compl

variable {α} in
theorem le_iff_fixedBy_compl_subset (g : G) (s : RegularOpens α) :
    (fixedBy α g)ᶜ ⊆ s ↔ RegularSupport α g ≤ s := by
  nth_rw 2 [← RegularOpens.fromSet_coe s]
  constructor
  · intro subset
    exact RegularOpens.fromSet_mono subset
  · intro le
    apply subset_trans (fixedBy_compl_subset α g)
    rw [← s.regularOpen]
    exact le

variable {α} in
theorem le_iff_mem_fixingSubgroup_compl (g : G) (s : RegularOpens α) :
    g ∈ G•[(↑s : Set α)ᶜ] ↔ RegularSupport α g ≤ s := by
  rw [mem_fixingSubgroup_compl_iff_movedBy_subset]
  exact le_iff_fixedBy_compl_subset g s

theorem smul (g h : G) : h • RegularSupport α g = RegularSupport α (h * g * h⁻¹) := by
  unfold RegularSupport
  rw [RegularOpens.smul_fromSet, Set.smul_set_compl, smul_fixedBy]

end RegularSupport

end Rubin
