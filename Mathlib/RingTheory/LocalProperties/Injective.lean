/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Injective
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.RingTheory.LocalProperties.Submodule

/-!

# Being injective is a local property

-/

universe u v

@[expose] public section

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] (S : Submonoid R)

lemma Module.Baer.iff_surjective : Module.Baer R M ↔
    ∀ (I : Ideal R), Function.Surjective (LinearMap.lcomp R M I.subtype) := by
  refine ⟨fun h I g ↦ ?_, fun h I g ↦ ?_⟩
  · rcases h I g with ⟨g', hg'⟩
    use g'
    ext x
    simp [hg']
  · rcases h I g with ⟨g', hg'⟩
    use g'
    intro x hx
    simp [← hg']

section

private instance [IsNoetherianRing R] (I : Ideal R) : Module.FinitePresentation R (R ⧸ I) := sorry

universe u' v'

theorem Module.injective_of_isLocalizedModule [Small.{v} R] [IsNoetherianRing R] {Rₛ : Type u'}
    [Small.{v'} Rₛ] [CommRing Rₛ] [Algebra R Rₛ] {Mₛ : Type v'} [AddCommGroup Mₛ] [Module R Mₛ]
    [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ] (f : M →ₗ[R] Mₛ) [IsLocalization S Rₛ]
    [IsLocalizedModule S f] [Module.Injective R M] : Module.Injective Rₛ Mₛ := by
  have MB : Baer R M := Baer.of_injective ‹_›
  rw [← Baer.iff_injective, Baer.iff_surjective]
  intro I

  sorry

end
