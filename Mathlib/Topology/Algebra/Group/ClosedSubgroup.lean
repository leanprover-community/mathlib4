/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Closed subgroups of a topological group

This files builds the frame of closed subgroups in a topological group `G`,
and its additive version `ClosedAddSubgroup`.

# Main definitions and results

* `normalCore_isClosed` : The `normalCore` of a closed subgroup is closed.

* `finindex_closedSubgroup_isOpen` : A closed subgroup with finite index is open.

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
  convert IsClosed.preimage (IsTopologicalGroup.continuous_conj (ConjAct.ofConjAct g⁻¹)) h
  exact Set.ext (fun t ↦ Set.mem_smul_set_iff_inv_smul_mem)

@[to_additive]
lemma isOpen_of_isClosed_of_finiteIndex (H : Subgroup G) [H.FiniteIndex]
    (h : IsClosed (H : Set G)) : IsOpen (H : Set G) := by
  apply isClosed_compl_iff.mp
  convert isClosed_iUnion_of_finite <| fun (x : {x : (G ⧸ H) // x ≠ QuotientGroup.mk 1})
    ↦ IsClosed.smul h (Quotient.out x.1)
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have : QuotientGroup.mk 1 ≠ QuotientGroup.mk (s := H) x := by
      apply QuotientGroup.eq.not.mpr
      simpa only [inv_one, one_mul, ne_eq]
    simp only [ne_eq, Set.mem_iUnion]
    use ⟨QuotientGroup.mk (s := H) x, this.symm⟩,
      (Quotient.out (QuotientGroup.mk (s := H) x))⁻¹ * x
    simp only [SetLike.mem_coe, smul_eq_mul, mul_inv_cancel_left, and_true]
    exact QuotientGroup.eq.mp <| QuotientGroup.out_eq' (QuotientGroup.mk (s := H) x)
  · rcases h with ⟨S,⟨y,hS⟩,mem⟩
    simp only [← hS] at mem
    rcases mem with ⟨h,hh,eq⟩
    simp only [Set.mem_compl_iff, SetLike.mem_coe]
    by_contra mH
    simp only [← eq, ne_eq, smul_eq_mul] at mH
    absurd y.2.symm
    rw [← QuotientGroup.out_eq' y.1, QuotientGroup.eq]
    simp only [inv_one, ne_eq, one_mul, (Subgroup.mul_mem_cancel_right H hh).mp mH]

end Subgroup

end
