/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Topology.Category.LightProfinite.Basic
import Mathlib.CategoryTheory.Functor.OfSequence
/-!

# Limits of surjections in `LightProfinite`

This file proves that a sequential limit of surjections is surjective in `LightProfinite`
In other words, given surjections
`⋯ ⟶ Sₙ₊₁ ⟶ Sₙ ⟶ ⋯ ⟶ S₀`,
the projection map `lim Sₙ ⟶ S₀` is surjective.
-/

open CategoryTheory Limits

attribute [local instance] ConcreteCategory.instFunLike

namespace LightProfinite

variable {F : ℕᵒᵖ ⥤ LightProfinite} {c : Cone F} (hc : IsLimit c)
  (hF : ∀ n, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op))

private noncomputable def preimage
    (a : F.obj ⟨0⟩) : (n : ℕ) → F.obj ⟨n⟩
    | 0 => a
    | n+1 => (hF n (preimage a n)).choose

lemma limit_of_surjections_surjective' :
    Function.Surjective ((limitCone F).π.app ⟨0⟩) := by
  intro a
  refine ⟨⟨fun ⟨n⟩ ↦ preimage hF a n, ?_⟩, rfl⟩
  intro ⟨n⟩ ⟨m⟩ ⟨⟨⟨(h : m ≤ n)⟩⟩⟩
  induction h with
  | refl =>
    simp only [Functor.comp_obj, lightProfiniteToCompHaus_obj, compHausToTop_obj, Functor.comp_map,
      lightProfiniteToCompHaus_map, compHausToTop_map]
    erw [CategoryTheory.Functor.map_id, id_apply]
  | @step p h ih =>
    simp only [Functor.comp_obj, lightProfiniteToCompHaus_obj, compHausToTop_obj, Functor.comp_map,
      lightProfiniteToCompHaus_map, compHausToTop_map] at ih
    simp only [Functor.comp_obj, lightProfiniteToCompHaus_obj, compHausToTop_obj,
      Nat.succ_eq_add_one, Functor.comp_map, lightProfiniteToCompHaus_map, compHausToTop_map]
    rw [← ih]
    have h' : m ≤ p := h
    erw [CategoryTheory.Functor.map_comp (f := (homOfLE (Nat.le_succ p)).op) (g := (homOfLE h').op),
      CategoryTheory.comp_apply, (hF p _).choose_spec]
    rfl

lemma limit_of_surjections_surjective : Function.Surjective (c.π.app ⟨0⟩) := by
  let i := hc.conePointUniqueUpToIso (limitConeIsLimit F)
  have : c.π.app ⟨0⟩ = i.hom ≫ (limitCone F).π.app ⟨0⟩ := by simp [i]
  rw [this]
  erw [CategoryTheory.coe_comp]
  apply Function.Surjective.comp
  · exact limit_of_surjections_surjective' hF
  · rw [← epi_iff_surjective]
    infer_instance
