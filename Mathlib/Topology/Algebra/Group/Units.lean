/-
Copyright (c) 2025 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde, David Ledvinka
-/
module

public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Monoid

/-!
# Topological properties of units

This file contains lemmas about the topology of units in topological monoids,
including results about submonoid units and units of product spaces.
-/

@[expose] public section

open Units

/-- If a submonoid is open in a topological monoid, then its units form an open subset
of the units of the monoid. -/
@[to_additive /-- If a submonoid is open in a topological additive monoid,
then its additive units form an open subset of the additive units of the monoid. -/]
lemma Submonoid.isOpen_units {M : Type*} [TopologicalSpace M] [Monoid M]
    {U : Submonoid M} (hU : IsOpen (U : Set M)) : IsOpen (U.units : Set Mˣ) :=
  (hU.preimage Units.continuous_val).inter (hU.preimage Units.continuous_coe_inv)

/-- The isomorphism of topological groups between the units of a product and
the product of the units. -/
@[to_additive /-- The isomorphism of topological additive groups between the additive units of a
product and the product of the additive units. -/]
def ContinuousMulEquiv.piUnits {ι : Type*}
    {M : ι → Type*} [(i : ι) → Monoid (M i)] [(i : ι) → TopologicalSpace (M i)] :
    (Π i, M i)ˣ ≃ₜ* Π i, (M i)ˣ where
  __ := MulEquiv.piUnits
  continuous_toFun := continuous_pi fun _ ↦ Units.continuous_iff.mpr
    ⟨continuous_apply _ |>.comp Units.continuous_val,
      continuous_apply _ |>.comp Units.continuous_coe_inv⟩
  continuous_invFun := Units.continuous_iff.mpr
    ⟨continuous_pi fun _ ↦ Units.continuous_val.comp <| continuous_apply _,
      continuous_pi fun _ ↦ Units.continuous_coe_inv.comp <| continuous_apply _⟩

namespace Units

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] [Monoid M] [Monoid N]

/-- Any `ContinuousMulEquiv` induces a `ContinuousMulEquiv` on units. -/
@[simps! apply]
def mapContinuousMulEquiv (f : M ≃ₜ* N) : Mˣ ≃ₜ* Nˣ :=
  { __ := Units.mapEquiv f
    continuous_toFun := f.continuous.units_map _
    continuous_invFun := f.symm.continuous.units_map _ }

@[simp]
theorem symm_mapContinuousMulEquiv (f : M ≃ₜ* N) :
    (mapContinuousMulEquiv f).symm = mapContinuousMulEquiv f.symm := rfl

@[simp]
theorem toMulEquiv_mapContinuousMulEquiv (f : M ≃ₜ* N) :
    (mapContinuousMulEquiv f : Mˣ ≃* Nˣ) = mapEquiv f := rfl

end Units

open Set Filter TopologicalSpace Function Topology MulOpposite Pointwise

variable {G H α β : Type*}

/-- If `G` is a group with topological `⁻¹`, then it is homeomorphic to its units. -/
@[to_additive /-- If `G` is an additive group with topological negation, then it is homeomorphic to
its additive units. -/]
def toUnits_homeomorph [Group G] [TopologicalSpace G] [ContinuousInv G] : G ≃ₜ Gˣ where
  toEquiv := toUnits.toEquiv
  continuous_toFun := Units.continuous_iff.2 ⟨continuous_id, continuous_inv⟩

@[to_additive] theorem Units.isEmbedding_val [Group G] [TopologicalSpace G] [ContinuousInv G] :
    IsEmbedding (val : Gˣ → G) :=
  toUnits_homeomorph.symm.isEmbedding

lemma Continuous.of_coeHom_comp [Group G] [Monoid H] [TopologicalSpace G] [TopologicalSpace H]
    [ContinuousInv G] {f : G →* Hˣ} (hf : Continuous ((Units.coeHom H).comp f)) : Continuous f := by
  apply continuous_induced_rng.mpr ?_
  refine continuous_prodMk.mpr ⟨hf, ?_⟩
  simp_rw [← map_inv]
  exact MulOpposite.continuous_op.comp (hf.comp continuous_inv)

namespace Units

@[to_additive]
theorem range_embedProduct [Monoid α] :
    Set.range (embedProduct α) = {p : α × αᵐᵒᵖ | p.1 * unop p.2 = 1 ∧ unop p.2 * p.1 = 1} :=
  Set.range_eq_iff _ _ |>.mpr
    ⟨fun a ↦ ⟨a.mul_inv, a.inv_mul⟩, fun p hp ↦ ⟨⟨p.1, unop p.2, hp.1, hp.2⟩, rfl⟩⟩

variable [Monoid α] [TopologicalSpace α] [Monoid β] [TopologicalSpace β]

@[to_additive]
instance [ContinuousMul α] : IsTopologicalGroup αˣ where
  continuous_inv := Units.continuous_iff.2 <| ⟨continuous_coe_inv, continuous_val⟩

@[to_additive]
theorem isClosedEmbedding_embedProduct [T1Space α] [ContinuousMul α] :
    IsClosedEmbedding (embedProduct α) where
  toIsEmbedding := isEmbedding_embedProduct
  isClosed_range := by
    rw [range_embedProduct]
    refine .inter (isClosed_singleton.preimage ?_) (isClosed_singleton.preimage ?_) <;>
    fun_prop

lemma _root_.Topology.IsClosedEmbedding.units_map [ContinuousMul α] [T1Space α] {f : α →* β}
    (hf : IsClosedEmbedding f) : IsClosedEmbedding (map f) := by
  refine .of_comp isEmbedding_embedProduct ?_
  exact (hf.prodMap (opHomeomorph.isClosedEmbedding.comp
    <| hf.comp opHomeomorph.symm.isClosedEmbedding)).comp isClosedEmbedding_embedProduct

@[to_additive]
instance [T1Space α] [ContinuousMul α] [CompactSpace α] : CompactSpace αˣ :=
  isClosedEmbedding_embedProduct.compactSpace

@[to_additive]
instance [T1Space α] [ContinuousMul α] [WeaklyLocallyCompactSpace α] :
    WeaklyLocallyCompactSpace αˣ :=
  isClosedEmbedding_embedProduct.weaklyLocallyCompactSpace

@[to_additive]
instance [T1Space α] [ContinuousMul α] [LocallyCompactSpace α] : LocallyCompactSpace αˣ :=
  isClosedEmbedding_embedProduct.locallyCompactSpace

lemma _root_.Submonoid.units_isCompact [T1Space α] [ContinuousMul α] {S : Submonoid α}
    (hS : IsCompact (S : Set α)) : IsCompact (S.units : Set αˣ) := by
  have : IsCompact (S ×ˢ S.op) := hS.prod (opHomeomorph.isCompact_preimage.mp hS)
  exact isClosedEmbedding_embedProduct.isCompact_preimage this

/-- The topological group isomorphism between the units of a product of two monoids, and the product
of the units of each monoid. -/
@[to_additive prodAddUnits
  /-- The topological group isomorphism between the additive units of a product of two
  additive monoids, and the product of the additive units of each additive monoid. -/]
def _root_.Homeomorph.prodUnits : (α × β)ˣ ≃ₜ αˣ × βˣ where
  continuous_toFun :=
    (continuous_fst.units_map (MonoidHom.fst α β)).prodMk
      (continuous_snd.units_map (MonoidHom.snd α β))
  continuous_invFun :=
    Units.continuous_iff.2
      ⟨continuous_val.fst'.prodMk continuous_val.snd',
        continuous_coe_inv.fst'.prodMk continuous_coe_inv.snd'⟩
  toEquiv := MulEquiv.prodUnits.toEquiv

end Units
