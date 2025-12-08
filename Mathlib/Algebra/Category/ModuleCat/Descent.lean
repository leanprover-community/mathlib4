/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jack McKoen, Christian Merten, Joël Riou, Adam Topaz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Monad.Comonadicity
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Faithfully flat descent for modules

In this file we show that extension of scalars by a faithfully flat ring homomorphism is comonadic.
Then the general theory of descent implies that the pseudofunctor to `Cat` given by extension
of scalars has effective descent relative to faithfully flat maps (TODO).

## Notes

This contribution was created as part of the AIM workshop
"Formalizing algebraic geometry" in June 2024.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory Comonad ModuleCat Limits MonoidalCategory

variable {A B : Type u} [CommRing A] [CommRing B] {f : A →+* B}

instance (M : ModuleCat.{u} A) [Module.Flat A M] : PreservesFiniteLimits <| tensorLeft M := by
  have h2 := (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi (tensorLeft M)).mp
    (inferInstanceAs <| PreservesFiniteColimits (tensorLeft M))
  rw [Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
  refine fun S hS ↦ ⟨(h2 S hS).1, ?_⟩
  have := hS.mono_f
  rw [ModuleCat.mono_iff_injective] at this ⊢
  exact Module.Flat.lTensor_preserves_injective_linearMap _ this

lemma foo (M : ModuleCat.{u} A) : Module.Flat A M ↔ PreservesFiniteLimits (tensorLeft M) := by
  refine ⟨fun _ ↦ ?_, fun h ↦ ?_⟩
  · have h2 := (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi (tensorLeft M)).mp
      (inferInstanceAs <| PreservesFiniteColimits (tensorLeft M))
    rw [Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
    refine fun S hS ↦ ⟨(h2 S hS).1, ?_⟩
    have := hS.mono_f
    rw [ModuleCat.mono_iff_injective] at this ⊢
    exact Module.Flat.lTensor_preserves_injective_linearMap _ this
  · constructor
    intro P _ _ _ N hN
    -- rw [← ModuleCat.mono_iff_injective]
    sorry


lemma ModuleCat.preservesFiniteLimits_tensorLeft_of_flat (hf : f.Flat) :
    PreservesFiniteLimits <| tensorLeft ((restrictScalars f).obj (ModuleCat.of B B)) := by
  algebraize [f]
  change PreservesFiniteLimits <| tensorLeft (ModuleCat.of A B)
  infer_instance

lemma ModuleCat.preservesFiniteLimits_extendScalars_of_flat (hf : f.Flat) :
    PreservesFiniteLimits (extendScalars.{_, _, u} f) := by
  have : PreservesFiniteLimits (extendScalars.{_, _, u} f ⋙ restrictScalars.{_, _, u} f) :=
    ModuleCat.preservesFiniteLimits_tensorLeft_of_flat hf
  exact preservesFiniteLimits_of_reflects_of_preserves (extendScalars f) (restrictScalars f)

/-- Extension of scalars along faithfully flat ring maps reflects isomorphisms. -/
lemma ModuleCat.reflectsIsomorphisms_extendScalars_of_faithfullyFlat
    (hf : f.FaithfullyFlat) : (extendScalars.{_, _, u} f).ReflectsIsomorphisms := by
  refine ⟨fun {M N} g h ↦ ?_⟩
  algebraize [f]
  rw [ConcreteCategory.isIso_iff_bijective] at h ⊢
  replace h : Function.Bijective (LinearMap.lTensor B g.hom) := h
  rwa [Module.FaithfullyFlat.lTensor_bijective_iff_bijective] at h

/-- Extension of scalars by a faithfully flat ring map is comonadic. -/
def comonadicExtendScalars (hf : f.FaithfullyFlat) :
    ComonadicLeftAdjoint (extendScalars f) := by
  have := preservesFiniteLimits_extendScalars_of_flat hf.flat
  have := reflectsIsomorphisms_extendScalars_of_faithfullyFlat hf
  convert Comonad.comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms
      (extendRestrictScalarsAdj f)
  · exact ⟨inferInstance⟩
  · exact ⟨inferInstance⟩
