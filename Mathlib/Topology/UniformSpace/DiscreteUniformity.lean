/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Antoine Chambert-Loir, María Inés de Frutos Fernández
-/
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.Algebra.UniformGroup.Defs

/-! # Discrete uniformity

The discrete uniformity is the smallest possibly uniformity, the one for which
the diagonal is an entourage of itself.

It induces the discrete topology.

It is complete.

-/

open Filter

/-- The discrete uniformity -/
class DiscreteUniformity (α : Type*) [UniformSpace α] : Prop where
  eq_principal_idRel : uniformity α = principal idRel

namespace DiscreteUniformity

/-- The bot uniformity is the discrete uniformity -/
instance (α : Type*) : @DiscreteUniformity α ⊥ := by
  apply @DiscreteUniformity.mk α ⊥ rfl

variable (X : Type*) [UniformSpace X] [DiscreteUniformity X]

/-- The discrete uniformity induces the discrete topology -/
instance : DiscreteTopology X := by
  rw [discreteTopology_iff_singleton_mem_nhds]
  intro a
  rw [UniformSpace.mem_nhds_iff]
  use Set.diagonal X
  simp [UniformSpace.ball, eq_principal_idRel]

/-- The discrete uniformity makes a group a `UniformGroup -/
@[to_additive "The discrete uniformity makes an additive group a `UniformAddGroup`"]
instance [Group X] : UniformGroup X where
  uniformContinuous_div := fun s hs ↦ by
    simp only [uniformity_prod, eq_principal_idRel, comap_principal,
      inf_principal, map_principal, mem_principal, Set.image_subset_iff]
    rintro ⟨⟨x, y⟩, z, t⟩
    simp only [Set.mem_inter_iff, Set.mem_preimage, mem_idRel, and_imp]
    rintro ⟨rfl⟩ ⟨rfl⟩
    exact mem_uniformity_of_eq hs rfl

variable {X} in
/-- A Cauchy filter in a discrete uniform space is contained in a principal filter. -/
theorem cauchy_le_pure {α : Filter X} (hα : Cauchy α) : ∃ x : X, α = pure x := by
  rcases hα with ⟨α_ne_bot, α_le⟩
  simp only [DiscreteUniformity.eq_principal_idRel, le_principal_iff, mem_prod_iff] at α_le
  obtain ⟨S, ⟨hS, ⟨T, ⟨hT, H⟩⟩⟩⟩ := α_le
  obtain ⟨x, rfl⟩ := eq_singleton_left_of_prod_subset_idRel (α_ne_bot.nonempty_of_mem hS)
    (Filter.nonempty_of_mem hT) H
  exact ⟨x, α_ne_bot.le_pure_iff.mp <| le_pure_iff.mpr hS⟩

/-- The discrete uniformity makes a space complete -/
instance : CompleteSpace X where
  complete {f} hf := by
    obtain ⟨x, rfl⟩ := cauchy_le_pure hf
    exact ⟨x, Specializes.pure_le_nhds fun ⦃U⦄ a ↦ a⟩

variable {X}

/-- A constant to which a Cauchy filter in a discrete uniform space converges. -/
noncomputable def cauchyConst {α : Filter X} (hα : Cauchy α) : X :=
  (cauchy_le_pure hα).choose

theorem eq_const_of_cauchy {α : Filter X} (hα : Cauchy α) : α = pure (cauchyConst hα) :=
  (DiscreteUniformity.cauchy_le_pure hα).choose_spec

end DiscreteUniformity
