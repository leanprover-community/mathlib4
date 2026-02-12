/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.GroupTheory.Index

/-!
# Finite-index normal subgroups

This file builds the lattice `FiniteIndexNormalSubgroup G` of finite-index normal subgroups of a
group `G`, and its additive version `FiniteIndexNormalAddSubgroup`.

This is used primarily in the definition of the profinite completion of a group.
-/

@[expose] public section

section

/-- The type of finite-index normal subgroups of a group. -/
@[ext]
structure FiniteIndexNormalSubgroup (G : Type*) [Group G] extends Subgroup G where
  isNormal' : toSubgroup.Normal := by infer_instance
  isFiniteIndex' : toSubgroup.FiniteIndex := by infer_instance

/-- The type of finite-index normal additive subgroups of an additive group. -/
@[ext]
structure FiniteIndexNormalAddSubgroup (G : Type*) [AddGroup G] extends AddSubgroup G where
  isNormal' : toAddSubgroup.Normal := by infer_instance
  isFiniteIndex' : toAddSubgroup.FiniteIndex := by infer_instance

attribute [to_additive] FiniteIndexNormalSubgroup

namespace FiniteIndexNormalSubgroup

variable {G : Type*} [Group G]

@[to_additive]
theorem toSubgroup_injective : Function.Injective
    (fun H ↦ H.toSubgroup : FiniteIndexNormalSubgroup G → Subgroup G) :=
  fun A B h ↦ by
  ext
  dsimp at h
  rw [h]

@[to_additive]
instance : SetLike (FiniteIndexNormalSubgroup G) G where
  coe U := U.1
  coe_injective' _ _ h := toSubgroup_injective <| SetLike.ext' h

@[to_additive]
instance : PartialOrder (FiniteIndexNormalSubgroup G) := .ofSetLike (FiniteIndexNormalSubgroup G) G

@[to_additive]
instance : SubgroupClass (FiniteIndexNormalSubgroup G) G where
  mul_mem := Subsemigroup.mul_mem' _
  one_mem U := U.one_mem'
  inv_mem := Subgroup.inv_mem' _

@[to_additive]
instance : Coe (FiniteIndexNormalSubgroup G) (Subgroup G) where
  coe H := H.toSubgroup

@[to_additive]
instance (H : FiniteIndexNormalSubgroup G) : H.toSubgroup.Normal := H.isNormal'

@[to_additive]
instance (H : FiniteIndexNormalSubgroup G) : H.toSubgroup.FiniteIndex := H.isFiniteIndex'

@[to_additive]
instance instPartialOrderFiniteIndexNormalSubgroup : PartialOrder (FiniteIndexNormalSubgroup G) :=
  inferInstance

@[to_additive]
instance instInfFiniteIndexNormalSubgroup : Min (FiniteIndexNormalSubgroup G) :=
  ⟨fun U V ↦ {
    toSubgroup := U.toSubgroup ⊓ V.toSubgroup
    isNormal' := Subgroup.normal_inf_normal U.toSubgroup V.toSubgroup
  }⟩

@[to_additive]
instance instSemilatticeInfFiniteIndexNormalSubgroup :
    SemilatticeInf (FiniteIndexNormalSubgroup G) :=
  SetLike.coe_injective.semilatticeInf ((↑) : FiniteIndexNormalSubgroup G → Set G) fun _ _ ↦ rfl

@[to_additive]
instance : Max (FiniteIndexNormalSubgroup G) :=
  ⟨fun U V ↦ {
    toSubgroup := U.toSubgroup ⊔ V.toSubgroup
    isNormal' := Subgroup.sup_normal U.toSubgroup V.toSubgroup
    isFiniteIndex' := Subgroup.finiteIndex_of_le
      (H := U.toSubgroup) (K := U.toSubgroup ⊔ V.toSubgroup) le_sup_left
  }⟩

@[to_additive]
instance instSemilatticeSupFiniteIndexNormalSubgroup :
    SemilatticeSup (FiniteIndexNormalSubgroup G) :=
  toSubgroup_injective.semilatticeSup _ (fun _ _ ↦ rfl)

@[to_additive]
instance : Lattice (FiniteIndexNormalSubgroup G) where

/-- Bundle a subgroup with typeclass assumptions of normality and finite index. -/
@[to_additive
  /-- Bundle an additive subgroup with typeclass assumptions of normality and finite index. -/]
def ofSubgroup (H : Subgroup G) [H.Normal] [H.FiniteIndex] : FiniteIndexNormalSubgroup G :=
  { toSubgroup := H }

@[to_additive (attr := simp)]
theorem toSubgroup_ofSubgroup (H : Subgroup G) [H.Normal] [H.FiniteIndex] :
    ((ofSubgroup H : FiniteIndexNormalSubgroup G) : Subgroup G) = H :=
  rfl

section Comap

variable {H : Type*} {N : Type*} [Group H] [Group N]

/-- The preimage of a finite-index normal subgroup under a group homomorphism. -/
@[to_additive
  /-- The preimage of a finite-index normal additive subgroup under an additive homomorphism. -/]
def comap (f : G →* H) (K : FiniteIndexNormalSubgroup H) : FiniteIndexNormalSubgroup G where
  toSubgroup := K.toSubgroup.comap f
  isFiniteIndex' := by
    let g : G →* (H ⧸ K.toSubgroup) := (QuotientGroup.mk' K.toSubgroup).comp f
    have hker : K.toSubgroup.comap f = g.ker := by
      simpa using MonoidHom.comap_ker (g := QuotientGroup.mk' K.toSubgroup) (f := f)
    simpa [hker] using (inferInstance : g.ker.FiniteIndex)

@[to_additive (attr := simp)]
theorem toSubgroup_comap (f : G →* H) (K : FiniteIndexNormalSubgroup H) :
    ((comap f K : FiniteIndexNormalSubgroup G) : Subgroup G) = (K : Subgroup H).comap f :=
  rfl

@[to_additive]
theorem comap_mono (f : G →* H) {K L : FiniteIndexNormalSubgroup H} (h : K ≤ L) :
    comap f K ≤ comap f L :=
  fun _ hx ↦ h hx

@[to_additive (attr := simp)]
theorem comap_id (K : FiniteIndexNormalSubgroup G) : comap (MonoidHom.id G) K = K := by
  rfl

@[to_additive (attr := simp)]
theorem comap_comp (f : G →* H) (g : H →* N) (K : FiniteIndexNormalSubgroup N) :
    comap (g.comp f) K = comap f (comap g K) := by
  rfl

end Comap

end FiniteIndexNormalSubgroup

end
