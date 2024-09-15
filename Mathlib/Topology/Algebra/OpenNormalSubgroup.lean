/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/

import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Open subgroups of a topological groups

This files builds the lattice `OpenNormalSubgroup G` of open subgroups in a topological group `G`,
and its additive version `OpenNormalAddSubgroup`.
-/

universe u v

/-- The type of open normal subgroups of a topological group. -/
@[ext]
structure OpenNormalSubgroup (G : Type u) [Group G] [TopologicalSpace G]
  extends OpenSubgroup G where
  isNormal' : toSubgroup.Normal := by infer_instance

@[ext]
structure OpenNormalAddSubgroup (G : Type u) [AddGroup G] [TopologicalSpace G]
  extends OpenAddSubgroup G where
  isNormal' : toAddSubgroup.Normal := by infer_instance

attribute [to_additive] OpenNormalSubgroup

namespace OpenNormalSubgroup

variable {G : Type u} [Group G] [TopologicalSpace G]

@[to_additive]
instance (H : OpenNormalSubgroup G) : H.toSubgroup.Normal := H.isNormal'

@[to_additive]
theorem toSubgroup_injective : Function.Injective
  (fun H => H.toOpenSubgroup.toSubgroup : OpenNormalSubgroup G → Subgroup G) :=
  fun A B h => by
  ext
  dsimp at h
  rw [h]

@[to_additive]
instance : SetLike (OpenNormalSubgroup G) G where
  coe U := U.1
  coe_injective' _ _ h := toSubgroup_injective <| SetLike.ext' h

@[to_additive]
instance : SubgroupClass (OpenNormalSubgroup G) G where
  mul_mem := Subsemigroup.mul_mem' _
  one_mem U := U.one_mem'
  inv_mem := Subgroup.inv_mem' _

@[to_additive]
instance : Coe (OpenNormalSubgroup G) (Subgroup G) where
  coe := fun H => H.toOpenSubgroup.toSubgroup

@[to_additive]
instance instPartialOrderOpenNormalSubgroup : PartialOrder (OpenNormalSubgroup G) := inferInstance

@[to_additive]
instance instInfClosedSubgroup : Inf (OpenNormalSubgroup G) :=
  ⟨fun U V => ⟨U.toOpenSubgroup ⊓ V.toOpenSubgroup,
    Subgroup.normal_inf_normal U.toSubgroup V.toSubgroup⟩⟩

@[to_additive]
instance instSemilatticeInfOpenNormalSubgroup : SemilatticeInf (OpenNormalSubgroup G) :=
  SetLike.coe_injective.semilatticeInf ((↑) : OpenNormalSubgroup G → Set G) fun _ _ => rfl

@[to_additive]
instance [ContinuousMul G] : Sup (OpenNormalSubgroup G) :=
  ⟨fun U V => ⟨U.toOpenSubgroup ⊔ V.toOpenSubgroup,
    Subgroup.sup_normal U.toOpenSubgroup.1 V.toOpenSubgroup.1⟩⟩

@[to_additive]
instance instSemilatticeSupOpenNormalSubgroup [ContinuousMul G] :
    SemilatticeSup (OpenNormalSubgroup G) :=
  toSubgroup_injective.semilatticeSup
    (fun (H : OpenNormalSubgroup G) ↦ ↑H.toOpenSubgroup) (fun _ _ => rfl)

@[to_additive]
instance [ContinuousMul G] : Lattice (OpenNormalSubgroup G) :=
  { instSemilatticeInfOpenNormalSubgroup,
    instSemilatticeSupOpenNormalSubgroup with
    toPartialOrder := instPartialOrderOpenNormalSubgroup}

end OpenNormalSubgroup
