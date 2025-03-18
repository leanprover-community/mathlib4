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

open Filter UniformSpace

/-- The discrete uniformity -/
class DiscreteUniformity (X : Type*) [u : UniformSpace X] : Prop where
  eq_bot: u = ⊥

namespace DiscreteUniformity

/-- The bot uniformity is the discrete uniformity -/
instance (X : Type*) : @DiscreteUniformity X ⊥ :=
  @DiscreteUniformity.mk X ⊥ rfl

variable (X : Type*) [u : UniformSpace X] [DiscreteUniformity X]

theorem eq_principal_idRel : uniformity X = principal idRel :=
  le_antisymm
    (by simpa [uniformSpace_eq_bot, ← le_principal_iff] using eq_bot)
    refl_le_uniformity

theorem iff_eq_principal_idRel {X : Type*} [UniformSpace X] :
    DiscreteUniformity X ↔ uniformity X = principal idRel :=
  ⟨fun _ ↦ eq_principal_idRel X, fun h ↦ { eq_bot := by ext; rw [h]; rfl }⟩

/-- The discrete uniformity induces the discrete topology -/
instance : DiscreteTopology X where
  eq_bot := by
    convert UniformSpace.toTopologicalSpace_bot
    exact eq_bot

theorem idRel_mem_uniformity : idRel ∈ uniformity X := by
  simp only [eq_principal_idRel, mem_principal, subset_refl]

variable {X} in
/-- A product of spaces with discrete uniformity has a discrete uniformity -/
instance {Y : Type*} [UniformSpace Y] [DiscreteUniformity Y] :
    DiscreteUniformity (X × Y) where
  eq_bot := by
    rw [instUniformSpaceProd, UniformSpace.uniformSpace_eq_bot, uniformity_prod_eq_comap_prod,
      mem_comap]
    refine ⟨idRel.prod idRel, prod_mem_prod (idRel_mem_uniformity _) (idRel_mem_uniformity _), ?_⟩
    rintro ⟨⟨x, y⟩, x', y'⟩ h
    simpa only [mem_idRel, Prod.mk.injEq] using h

variable {x} in
/-- On a space with a discrete uniformity, any function is uniformly continuous -/
theorem uniformContinuous {Y : Type*} [UniformSpace Y] (f : X → Y) :
    UniformContinuous f := fun s hs ↦ by
  rw [mem_map]
  apply Filter.mem_of_superset (idRel_mem_uniformity X)
  simp only [idRel_subset, Set.mem_preimage]
  exact fun _ ↦ mem_uniformity_of_eq hs rfl

/-- The discrete uniformity makes a group a `UniformGroup -/
@[to_additive "The discrete uniformity makes an additive group a `UniformAddGroup`"]
instance [Group X] : UniformGroup X where
  uniformContinuous_div := uniformContinuous (X × X) fun p ↦ p.1 / p.2

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
