/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Antoine Chambert-Loir, María Inés de Frutos Fernández
-/
import Mathlib.Topology.UniformSpace.Basic

/-! # Discrete uniformity

The discrete uniformity is the smallest possible uniformity, the one for which
the diagonal is an entourage of itself.

It induces the discrete topology.

It is complete.

-/

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

theorem _root_.discreteUniformity_iff_eq_principal_idRel {X : Type*} [UniformSpace X] :
    DiscreteUniformity X ↔ uniformity X = principal idRel := by
  rw [discreteUniformity_iff_eq_bot, UniformSpace.ext_iff, Filter.ext_iff, bot_uniformity]

theorem eq_principal_idRel : uniformity X = principal idRel :=
  discreteUniformity_iff_eq_principal_idRel.mp inferInstance

/-- The discrete uniformity induces the discrete topology. -/
instance : DiscreteTopology X where
  eq_bot := by
    rw [DiscreteUniformity.eq_bot (X := X), UniformSpace.toTopologicalSpace_bot]

theorem _root_.discreteUniformity_iff_idRel_mem_uniformity {X : Type*} [UniformSpace X] :
    DiscreteUniformity X ↔ idRel ∈ uniformity X := by
  rw [← uniformSpace_eq_bot, discreteUniformity_iff_eq_bot]

theorem idRel_mem_uniformity : idRel ∈ uniformity X :=
  discreteUniformity_iff_idRel_mem_uniformity.mp inferInstance

variable {X} in
/-- A product of spaces with discrete uniformity has a discrete uniformity. -/
instance {Y : Type*} [UniformSpace Y] [DiscreteUniformity Y] :
    DiscreteUniformity (X × Y) := by
  simp [discreteUniformity_iff_eq_principal_idRel, uniformity_prod_eq_comap_prod,
    eq_principal_idRel, idRel, Set.prod_eq, Prod.ext_iff, Set.setOf_and]

variable {x} in
/-- On a space with a discrete uniformity, any function is uniformly continuous. -/
theorem uniformContinuous {Y : Type*} [UniformSpace Y] (f : X → Y) :
    UniformContinuous f := by
  simp only [uniformContinuous_iff, DiscreteUniformity.eq_bot, bot_le]

end DiscreteUniformity
