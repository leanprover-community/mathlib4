/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Closed subgroups of a topological group

This file builds the frame of closed subgroups in a topological group `G`,
and its additive version `ClosedAddSubgroup`.

# Main definitions and results

* `normalCore_isClosed`: The `normalCore` of a closed subgroup is closed.

* `finindex_closedSubgroup_isOpen`: A closed subgroup with finite index is open.

## TODO

Actually provide the `Order.Frame (ClosedSubgroup G)` instance.
-/

section

universe u v

/-- The type of closed subgroups of a topological group. -/
@[ext]
structure ClosedSubgroup (G : Type u) [Group G] [TopologicalSpace G] extends Subgroup G where
  isClosed' : IsClosed carrier

/-- The type of closed subgroups of an additive topological group. -/
@[ext]
structure ClosedAddSubgroup (G : Type u) [AddGroup G] [TopologicalSpace G] extends
    AddSubgroup G where
  isClosed' : IsClosed carrier

attribute [to_additive] ClosedSubgroup

attribute [coe] ClosedSubgroup.toSubgroup ClosedAddSubgroup.toAddSubgroup

namespace ClosedSubgroup

variable (G : Type u) [Group G] [TopologicalSpace G]

variable {G} in
@[to_additive]
theorem toSubgroup_injective : Function.Injective
    (ClosedSubgroup.toSubgroup : ClosedSubgroup G → Subgroup G) :=
  fun A B h ↦ by
  ext
  rw [h]

@[to_additive]
instance : SetLike (ClosedSubgroup G) G where
  coe U := U.1
  coe_injective' _ _ h := toSubgroup_injective <| SetLike.ext' h

@[to_additive]
instance : SubgroupClass (ClosedSubgroup G) G where
  mul_mem := Subsemigroup.mul_mem' _
  one_mem U := U.one_mem'
  inv_mem := Subgroup.inv_mem' _

@[to_additive]
instance : Coe (ClosedSubgroup G) (Subgroup G) where
  coe := toSubgroup

@[to_additive]
instance instInfClosedSubgroup : Min (ClosedSubgroup G) :=
  ⟨fun U V ↦ ⟨U ⊓ V, U.isClosed'.inter V.isClosed'⟩⟩

@[to_additive]
instance instSemilatticeInfClosedSubgroup : SemilatticeInf (ClosedSubgroup G) :=
  SetLike.coe_injective.semilatticeInf ((↑) : ClosedSubgroup G → Set G) fun _ _ ↦ rfl

@[to_additive]
instance [CompactSpace G] (H : ClosedSubgroup G) : CompactSpace H :=
  isCompact_iff_compactSpace.mp (IsClosed.isCompact H.isClosed')

end ClosedSubgroup

open scoped Pointwise

namespace Subgroup

variable {G : Type u} [Group G] [TopologicalSpace G] [ContinuousMul G]

lemma normalCore_isClosed (H : Subgroup G) (h : IsClosed (H : Set G)) :
    IsClosed (H.normalCore : Set G) := by
  rw [normalCore_eq_iInf_conjAct]
  push_cast
  apply isClosed_iInter
  intro g
  convert IsClosed.preimage (IsTopologicalGroup.continuous_conj (ConjAct.ofConjAct g⁻¹)) h using 1
  exact Set.ext (fun t ↦ Set.mem_smul_set_iff_inv_smul_mem)

@[to_additive]
lemma isOpen_of_isClosed_of_finiteIndex (H : Subgroup G) [H.FiniteIndex]
    (h : IsClosed (H : Set G)) : IsOpen (H : Set G) := by
  rw [← QuotientGroup.t1Space_iff] at h
  rw [← QuotientGroup.discreteTopology_iff]
  infer_instance

end Subgroup

end
