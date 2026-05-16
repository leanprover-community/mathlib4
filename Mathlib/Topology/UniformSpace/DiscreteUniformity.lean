/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Antoine Chambert-Loir, María Inés de Frutos Fernández
-/
module

public import Mathlib.Topology.UniformSpace.Basic

/-! # Discrete uniformity

The discrete uniformity is the smallest possible uniformity, the one for which
the diagonal is an entourage of itself.

It induces the discrete topology.

It is complete.

-/

public section

open Filter UniformSpace

/-- The discrete uniformity -/
@[mk_iff discreteUniformity_iff_eq_bot]
class DiscreteUniformity (X : Type*) [u : UniformSpace X] : Prop where
  eq_bot : u = ⊥

namespace DiscreteUniformity

/-- The bot uniformity is the discrete uniformity. -/
instance (X : Type*) : @DiscreteUniformity X ⊥ :=
  @DiscreteUniformity.mk X ⊥ rfl

variable (X : Type*) [u : UniformSpace X] [DiscreteUniformity X]

theorem _root_.discreteUniformity_iff_eq_principal_setRelId {X : Type*} [UniformSpace X] :
    DiscreteUniformity X ↔ uniformity X = 𝓟 SetRel.id := by
  rw [discreteUniformity_iff_eq_bot, UniformSpace.ext_iff, Filter.ext_iff, bot_uniformity]

@[deprecated (since := "2025-12-19")]
alias _root_.discreteUniformity_iff_eq_principal_relId :=
  _root_.discreteUniformity_iff_eq_principal_setRelId

@[deprecated (since := "2025-10-17")]
alias _root_.discreteUniformity_iff_eq_principal_idRel :=
  discreteUniformity_iff_eq_principal_setRelId

theorem eq_principal_setRelId : uniformity X = 𝓟 SetRel.id :=
  discreteUniformity_iff_eq_principal_setRelId.mp inferInstance

@[deprecated (since := "2025-12-19")] alias eq_principal_relId := eq_principal_setRelId

@[deprecated (since := "2025-10-17")]
alias eq_principal_idRel := eq_principal_setRelId

/-- The discrete uniformity induces the discrete topology. -/
instance : DiscreteTopology X where
  eq_bot := by
    rw [DiscreteUniformity.eq_bot (X := X), UniformSpace.toTopologicalSpace_bot]

theorem _root_.discreteUniformity_iff_setRelId_mem_uniformity {X : Type*} [UniformSpace X] :
    DiscreteUniformity X ↔ SetRel.id ∈ uniformity X := by
  rw [← uniformSpace_eq_bot, discreteUniformity_iff_eq_bot]

@[deprecated (since := "2025-12-19")]
alias _root_.discreteUniformity_iff_relId_mem_uniformity :=
  _root_.discreteUniformity_iff_setRelId_mem_uniformity

@[deprecated (since := "2025-10-17")]
alias _root_.discreteUniformity_iff_idRel_mem_uniformity :=
  discreteUniformity_iff_setRelId_mem_uniformity

theorem relId_mem_uniformity : SetRel.id ∈ uniformity X :=
  discreteUniformity_iff_setRelId_mem_uniformity.mp inferInstance

@[deprecated (since := "2025-10-17")]
alias idRel_mem_uniformity := relId_mem_uniformity

instance {Y : Type*} [Finite Y] [UniformSpace Y] [DiscreteTopology Y] :
    DiscreteUniformity Y := by
  have h : SetRel.id = ⋂ y : Y, {p | p.2 = y → p.1 ∈ ({y} : Set Y)} := by
    ext x
    simp [SetRel.id]
  simp_rw [discreteUniformity_iff_setRelId_mem_uniformity, h, Filter.iInter_mem,
    ← mem_nhds_uniformity_iff_left, nhds_discrete, Filter.mem_pure, Set.mem_singleton_iff,
    implies_true]

variable {X} in
/-- A product of spaces with discrete uniformity has a discrete uniformity. -/
instance {Y : Type*} [UniformSpace Y] [DiscreteUniformity Y] :
    DiscreteUniformity (X × Y) := by
  simp [discreteUniformity_iff_eq_principal_setRelId, uniformity_prod_eq_comap_prod,
    eq_principal_setRelId, SetRel.id, Set.prod_eq, Prod.ext_iff, Set.setOf_and]

variable {x} in
/-- On a space with a discrete uniformity, any function is uniformly continuous. -/
theorem uniformContinuous {Y : Type*} [UniformSpace Y] (f : X → Y) :
    UniformContinuous f := by
  simp only [uniformContinuous_iff, DiscreteUniformity.eq_bot, bot_le]

end DiscreteUniformity
